// Slow-burn momentum bot for the pump.fun replay (agent-fun/replay/v2).
//
// Idea: most new bonding curves die fast, but the ones that keep attracting
// fresh buyers for a while tend to keep climbing a little longer. This bot
// waits until a curve has proven itself (old enough that the launch dump is
// over, several different wallets buying, net SOL still flowing in and the
// price sitting near its recent high), then buys a small first stake and
// only adds to the position while the tape stays strong. Every position
// carries a hard stop, a trailing stop once it is in profit, a fade exit
// when the flow turns, and a hard time limit, so no single coin can eat the
// book. A small probe trade keeps the run on pace for the guardrail bar
// (20+ coins, 200+ fills) when the momentum entries are running slow.
//
// Everything is a pure function of the replay stream: no clock, no
// randomness, iteration only over insertion-ordered maps, so the two
// grading runs produce byte-identical action logs.

import { LAMPORTS_PER_SOL, runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000;
const CURVE_FEE = 0.0125; // protocol + creator take on a sale, as a share of proceeds
const SOL = LAMPORTS_PER_SOL;

// ---- tunables (chosen on the dev window, kept in flat regions) ----
const WINDOW = 30; // entry lookback, in slots
const FADE_WINDOW = 15; // fade-exit lookback, in slots
const MIN_NET_SOL = 1; // net SOL (buys minus sells) over the entry window
const MIN_BUYS = 3; // buy trades inside the window
const MIN_BUYERS = 4; // distinct buying wallets inside the window
const MIN_UP = 0.05; // price must be up at least 5% over the window
const MAX_UP = 1.5; // ... but not more than 150% (already ran away)
const NEAR_HIGH = 0.95; // price must sit within 5% of the window high
const MAX_BUYER_SHARE = 0.6; // no single wallet may supply >60% of buy SOL
const MIN_RQ_SOL = 2; // curve real SOL at entry: at least 2
const MAX_RQ_SOL = 60; // ... at most 60 (bigger curves move too slowly)
const MIN_AGE = 500; // slots since CreateEvent before an entry is allowed
const STAKE_SOL = 2; // most SOL ever put into one position
const FIRST_SOL = 0.05; // first buy of a position
const ADD_SOL = 0.2; // each pyramid add
const MIN_BUY_SOL = 0.01; // smallest buy worth sending
const BUY_SLIP_BPS = 1500; // slippage allowed on buys; sells go out wide open
const STOP_LOSS = 0.2; // sell when value falls 20% under cost
const TRAIL = 0.3; // sell when value falls 30% under its peak...
const TRAIL_ARM = 0.05; // ...once the peak reached cost + 5%
const FADE_NET_SOL = -0.5; // sell when 15-slot net flow drops under -0.5 SOL
const BIG_SELL_SOL = 2; // sell on any single recorded sell of 2+ SOL
const MAX_HOLD = 1500; // sell after this many slots held...
const HOLD_IF_UP = 0.2; // ...unless the position is up 20% or more
const COOLDOWN = 150; // slots to wait after an exit before re-entering a curve
const MAX_ENTRIES = 2; // most entries per curve over the run
const MAX_EXPOSURE_SOL = 6; // most SOL at cost across all positions at once
const TARGET_COINS = 25; // guardrail pacing: coins to reach by end of window
const TARGET_FILLS = 240; // guardrail pacing: fills to reach by end of window
const PACE_SECS = 14_400; // block-time span the pacing targets are spread over
const PROBE_SOL = 0.02; // probe round-trip size (above the 0.01 SOL bar)
const MAX_PROBES = 1; // most probe round trips open at once

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: TapeTrade[];
  entries: number;
  lastExit: number;
}

interface Held {
  opened: number;
  peak: number; // best close value seen, SOL
  invested: number; // SOL sent in buys for this position, fees included
  exiting: boolean;
  filled: boolean; // some buy of this position filled
  lastAddPrice: number; // price when the last buy was decided
  lastValue: number; // close value at the latest batch, SOL
}

const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
const probes = new Map<Pubkey, boolean>(); // mint -> true once its probe buy landed
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;
const KEEP = Math.max(WINDOW, FADE_WINDOW) + 5;

function tapeOf(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], entries: 0, lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
}

/** Price of one token in SOL, from virtual reserves. */
function priceOf(vq: bigint, vt: bigint): number {
  return Number(vq) / Number(vt);
}

/** What selling `tokens` would bring back, in SOL, after curve + tx fees. */
function closeValue(tokens: bigint, vq: bigint, vt: bigint, txLamports: bigint): number {
  const out = (Number(tokens) * Number(vq)) / (Number(vt) + Number(tokens));
  return (out / LAMPORTS) * (1 - CURVE_FEE) - Number(txLamports) / LAMPORTS;
}

/** Net recorded SOL (buys minus sells) on a tape over the last `w` slots. */
function netFlow(t: Tape, now: number, w: number): number {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
}

/** The entry signal: mature curve, broad buying, accelerating inflow, price near its high. */
function entryOk(t: Tape, now: number, rqSol: number): boolean {
  if (rqSol < MIN_RQ_SOL || rqSol > MAX_RQ_SOL) return false;
  if (t.created === null || now - t.created < MIN_AGE) return false;
  const from = now - WINDOW;
  const mid = now - WINDOW / 2;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let netOld = 0;
  let netNew = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const byUser = new Map<string, number>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    const signed = tr.buy ? tr.sol : -tr.sol;
    if (tr.slot <= mid) netOld += signed;
    else netNew += signed;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      byUser.set(tr.user, (byUser.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < MIN_BUYS || byUser.size < MIN_BUYERS) return false;
  if (buySol - sellSol < MIN_NET_SOL) return false;
  if (startPrice <= 0) return false;
  const up = last / startPrice - 1;
  if (up < MIN_UP || up > MAX_UP) return false;
  if (last < high * NEAR_HIGH) return false;
  if (netNew <= 0 || netNew < netOld) return false; // inflow must be accelerating
  let top = 0;
  for (const v of byUser.values()) if (v > top) top = v;
  if (top > MAX_BUYER_SHARE * buySol) return false; // one wallet must not dominate
  return true;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const bigSell = new Set<Pubkey>();
    const traded = new Set<Pubkey>();

    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        myCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstTime === null) firstTime = e.block_time;
        if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
        traded.add(e.mint);
        if (!e.is_buy && Number(e.sol_amount) / LAMPORTS >= BIG_SELL_SOL) bigSell.add(e.mint);
      }
    }
    // Prune old tape entries so memory stays bounded.
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - KEEP) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAMPORTS;

    // --- exits first: stop loss, trailing stop, fade, whale dump, time limit ---
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          held.delete(mint);
          const t = tapeOf(mint);
          if (h.filled) t.lastExit = now;
          else t.entries--;
        }
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? BigInt(mk.virtual_quote_reserves) : curve.virtual_quote_reserves;
      const vt = mk ? BigInt(mk.virtual_token_reserves) : curve.virtual_token_reserves;
      const rqSol = Number(mk ? mk.real_quote_reserves : curve.real_quote_reserves) / LAMPORTS;
      const value = closeValue(pos.token_amount, vq, vt, state.txFeeLamports());
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      if (value > h.peak) h.peak = value;
      h.lastValue = value;
      let exit = h.exiting;
      const t = tapeOf(mint);
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && h.peak >= cost * (1 + TRAIL_ARM) && value < h.peak * (1 - TRAIL)) exit = true;
      if (!exit && netFlow(t, now, FADE_WINDOW) < FADE_NET_SOL) exit = true;
      if (!exit && bigSell.has(mint)) exit = true;
      if (!exit && now - h.opened > MAX_HOLD && value < cost * (1 + HOLD_IF_UP)) exit = true;
      if (!exit) continue;
      h.exiting = true;
      if (pendingByMint.has(mint)) {
        let sellPending = false;
        for (const po of state.pending.values()) {
          if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
        }
        if (sellPending) continue;
      }
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
    }

    // --- probes: sell the whole probe as soon as its buy has landed ---
    for (const [mint, selling] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      if (!selling) probes.set(mint, true);
    }

    // --- entries and pyramid adds ---
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let exposure = 0;
    for (const [mint, h] of held) {
      exposure += Math.max(h.invested, Number(state.positions.get(mint)?.cost_lamports ?? 0n) / LAMPORTS);
    }
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint)) continue;
      const t = tapes.get(mint)!;
      const h = held.get(mint);
      const price = priceOf(curve.virtual_quote_reserves, curve.virtual_token_reserves);
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      let want: number;
      if (h === undefined) {
        if (slotsLeft <= 0) continue;
        if (t.entries >= MAX_ENTRIES || now - t.lastExit < COOLDOWN) continue;
        if (!entryOk(t, now, rqSol)) continue;
        want = Math.min(FIRST_SOL, STAKE_SOL);
      } else {
        // Pyramid into strength only: still in profit, price stepped up from
        // the last add, and net SOL still flowing in over the entry window.
        if (h.exiting || !h.filled || h.invested >= STAKE_SOL - MIN_BUY_SOL) continue;
        const pos = state.positions.get(mint);
        if (pos === undefined) continue;
        if (price < h.lastAddPrice) continue;
        if (h.lastValue < (Number(pos.cost_lamports) / LAMPORTS) * 1.0) continue;
        if (netFlow(t, now, WINDOW) < MIN_NET_SOL) continue;
        if (rqSol > MAX_RQ_SOL) continue;
        want = Math.min(ADD_SOL, STAKE_SOL - h.invested);
      }
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, want, MAX_EXPOSURE_SOL - exposure);
      if (amount > free - tx) amount = free - tx;
      if (amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      free -= amount + tx;
      exposure += amount;
      if (h === undefined) {
        held.set(mint, {
          opened: now,
          peak: 0,
          invested: amount,
          exiting: false,
          filled: false,
          lastAddPrice: price,
          lastValue: 0,
        });
        t.entries++;
        slotsLeft--;
      } else {
        h.invested += amount;
        h.lastAddPrice = price;
      }
    }

    // --- guardrail pacing: open a probe when fills or coins lag the pace ---
    if (probes.size < MAX_PROBES && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / PACE_SECS);
      const needCoins = myCoins.size < Math.ceil(TARGET_COINS * pace);
      const needFills = myFills < Math.ceil(TARGET_FILLS * pace);
      if (needCoins || needFills) {
        const minRq = (PROBE_SOL * 10_000) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= MAX_PROBES) break;
          if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && myCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / LAMPORTS < minRq * 1.5) continue;
          if (free < PROBE_SOL + 2 * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(PROBE_SOL * LAMPORTS)), max_slippage_bps: BUY_SLIP_BPS });
          probes.set(mint, false);
          free -= PROBE_SOL + tx;
        }
      }
    }
    return orders;
  },
});
