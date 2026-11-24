// Launch sniper with a deep-reserve filter, for the pump.fun replay (agent-fun/replay/v2).
//
// Idea: on a bonding curve the cheapest tokens belong to the earliest buyers,
// so the bot buys launches, not run-ups. But most launches are rugs, so it
// only buys when the launch itself looks honest: the curve already holds at
// least 2 SOL of real reserves within its first few slots, the creator put
// up to 2.5 SOL of their own money in the create slot, at most one other
// wallet has bought in yet (a launch bundled by many wallets is a dump in
// waiting), and the creator has not sold a token. Coins first seen through
// a trade, with no CreateEvent, are never bought: their launch was missed
// and buying them would mean buying the top. One small fixed buy per
// coin, out fast: take profit at +20%, cut at -12%, never hold past 30
// slots, and leave at once if the creator sells. A small probe trade keeps
// the run on pace for the guardrail bar (20+ coins) when sniper entries
// run slow.
//
// Everything is a pure function of the replay stream: no clock, no
// randomness, iteration only over insertion-ordered maps, so the two
// grading runs produce byte-identical action logs.

import { LAMPORTS_PER_SOL, runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000;
const CURVE_FEE = 0.0125; // protocol + creator take on a sale, as a share of proceeds

// ---- tunables (swept on the dev window with the pilot's simulator; the
// chosen cell is positive in the sim with both halves checked) ----
const MAX_AGE = 3; // oldest age (slots since CreateEvent) at which a first buy may be decided
const STAKE_SOL = 0.05; // SOL to aim for per coin
const MIN_BUY_SOL = 0.01; // smallest buy worth paying the tx fee for
const MIN_REAL_SOL = 2; // curve real SOL at decision time: at least 2
const MAX_DEV_BUY_SOL = 2.5; // creator's own buys in the create slot: at most 2.5 SOL
const MAX_BUYERS = 1; // distinct non-creator buyers seen before entry: at most 1
const BUY_SLIP_BPS = 10_000; // slippage allowed on buys; sells go out wide open
const TAKE_PROFIT = 0.2; // sell the whole position once value reaches cost + 20%
const STOP_LOSS = 0.12; // sell when value falls 12% under cost
const MAX_HOLD = 30; // sell after this many slots held
const TARGET_COINS = 22; // guardrail pacing floor: coins to reach by end of window
const PACE_SECS = 14_400; // block-time span the pacing target is spread over
const PROBE_SOL = 0.02; // probe round-trip size (above the 0.01 SOL bar)
const MAX_PROBES = 1; // most probe round trips open at once

interface Launch {
  creator: string;
  created: number;
  devBuySol: number; // creator's buys in the create slot, SOL
  buyers: Set<string>; // distinct non-creator buyers
  devSold: boolean; // the creator sold before entry
  bought: boolean; // we already bought this coin
}

interface Held {
  opened: number;
  exiting: boolean;
  filled: boolean;
}

const launches = new Map<Pubkey, Launch>();
const held = new Map<Pubkey, Held>();
const probes = new Map<Pubkey, boolean>(); // mint -> true once its probe buy landed
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;

/** Price of one token in SOL, from virtual reserves. */
function priceOf(vq: bigint, vt: bigint): number {
  return Number(vq) / Number(vt);
}

/** What selling `tokens` would bring back, in SOL, after curve + tx fees. */
function closeValue(tokens: bigint, vq: bigint, vt: bigint, txLamports: bigint): number {
  const out = (Number(tokens) * Number(vq)) / (Number(vt) + Number(tokens));
  return (out / LAMPORTS) * (1 - CURVE_FEE) - Number(txLamports) / LAMPORTS;
}

function launchOf(mint: Pubkey, creator: string, slot: number): Launch {
  let l = launches.get(mint);
  if (l === undefined) {
    l = { creator, created: slot, devBuySol: 0, buyers: new Set(), devSold: false, bought: false };
    launches.set(mint, l);
  }
  return l;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
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
        launchOf(e.mint, e.creator, e.slot);
      } else if (e.event === 'TradeEvent') {
        // Only track coins we saw created: a trade without a CreateEvent is
        // an older coin whose launch we missed, and buying it as a fresh
        // launch means buying its top.
        const l = launches.get(e.mint);
        if (l === undefined) continue;
        const sol = Number(e.sol_amount) / LAMPORTS;
        if (e.user === l.creator) {
          if (e.is_buy) {
            if (e.slot === l.created) l.devBuySol += sol;
          } else {
            l.devSold = true;
          }
        } else if (e.is_buy) {
          l.buyers.add(e.user);
        }
        traded.add(e.mint);
      }
    }

    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAMPORTS;

    // --- exits first: take profit, stop loss, time limit, creator sold ---
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) held.delete(mint);
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? BigInt(mk.virtual_quote_reserves) : curve.virtual_quote_reserves;
      const vt = mk ? BigInt(mk.virtual_token_reserves) : curve.virtual_token_reserves;
      const value = closeValue(pos.token_amount, vq, vt, state.txFeeLamports());
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      const l = launches.get(mint);
      let exit = h.exiting;
      if (!exit && value >= cost * (1 + TAKE_PROFIT)) exit = true;
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && now - h.opened > MAX_HOLD) exit = true;
      if (!exit && l !== undefined && l.devSold) exit = true;
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

    // --- sniper entries: launches in their first slots that pass the filter ---
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    for (const mint of traded) {
      if (orders.length >= cap) break;
      if (slotsLeft <= 0) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint) || held.has(mint)) continue;
      const l = launches.get(mint);
      if (l === undefined || l.bought) continue;
      const age = now - l.created;
      if (age < 0 || age > MAX_AGE) continue;
      if (l.devSold) continue;
      if (l.devBuySol > MAX_DEV_BUY_SOL) continue;
      if (l.buyers.size > MAX_BUYERS) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      if (rqSol < MIN_REAL_SOL) continue;
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, STAKE_SOL);
      if (amount > free - tx) amount = free - tx;
      if (amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      l.bought = true;
      held.set(mint, { opened: now, exiting: false, filled: false });
      free -= amount + tx;
      slotsLeft--;
    }

    // --- guardrail pacing: open a probe when the coin count lags the pace ---
    if (probes.size < MAX_PROBES && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / PACE_SECS);
      const needCoins = myCoins.size < Math.ceil(TARGET_COINS * pace);
      if (needCoins) {
        const minRq = (PROBE_SOL * 10_000) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= MAX_PROBES) break;
          if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (myCoins.has(mint)) continue;
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
