// Momentum rider for the pump.fun replay (agent-fun/replay/v2).
//
// The launch-snipe family is exhausted: buying a coin in its first seconds
// loses a few percent per trade no matter how the filter is tuned, because
// almost every launch is a rug and the few runners cannot pay for the rest.
// This bot does the opposite: it waits until a coin has survived its first
// minutes and already shown it can run — up at least 20% over the last 120
// slots, aged 120 to 600 slots since creation — and only then buys a small
// fixed stake. The edge, if any, is not in picking the entry: it is in the
// exit. A fixed take-profit caps the winners at the same size as the losers
// it cuts, and on this window that loses money on every parameter set tried.
// So winners are left to run behind a trailing stop instead: once a position
// is up 10% the stop trails 15% below its best value, so a coin that runs
// 2x or 5x pays for the many that hit the -12% stop. Positions die after
// 600 slots held. One buy per coin, ever — a coin that already had its
// chance does not get a second one.
//
// Everything is a pure function of the replay stream: no clock, no
// randomness, iteration only over insertion-ordered maps, so the two
// grading runs produce byte-identical action logs.

import { LAMPORTS_PER_SOL, runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000;
const CURVE_FEE = 0.0125; // protocol + creator take on a sale, as a share of proceeds

// ---- tunables (chosen from a batch-end replay of the dev window; the
// fixed take-profit grid on this entry set is negative at every setting,
// while the trailing-stop exit is positive in the same replay) ----
const MIN_AGE = 120; // youngest age (slots since CreateEvent) at which a buy may be decided
const MAX_AGE = 600; // oldest age at which a buy may be decided
const LOOKBACK = 120; // slots of price history the rise is measured over
const MIN_RISE = 0.2; // price now over price LOOKBACK slots ago, minus 1
const STAKE_SOL = 0.05; // SOL to aim for per coin
const MIN_BUY_SOL = 0.01; // smallest buy worth paying the tx fee for
const BUY_SLIP_BPS = 1500; // a buy whose price jumps more than 15% in the 2-slot latency is refused (free)
const STOP_LOSS = 0.12; // sell when value falls 12% under cost
const TRAIL_ARM = 0.1; // the trailing stop arms once value reaches cost + 10%
const TRAIL_GIVEBACK = 0.1; // once armed, sell when value falls 10% below its best
const MAX_HOLD = 600; // sell after this many slots held

interface TapePoint {
  slot: number;
  price: number;
}

interface Ride {
  opened: number;
  peak: number;
  armed: boolean;
  exiting: boolean;
}

const tapes = new Map<Pubkey, TapePoint[]>();
const createdAt = new Map<Pubkey, number>();
const bought = new Set<Pubkey>();
const rides = new Map<Pubkey, Ride>();

/** Price of one token in SOL, from virtual reserves. */
function priceOf(vq: bigint, vt: bigint): number {
  return Number(vq) / Number(vt);
}

/** What selling `tokens` would bring back, in SOL, after curve + tx fees. */
function closeValue(tokens: bigint, vq: bigint, vt: bigint, txLamports: bigint): number {
  const out = (Number(tokens) * Number(vq)) / (Number(vt) + Number(tokens));
  return (out / LAMPORTS) * (1 - CURVE_FEE) - Number(txLamports) / LAMPORTS;
}

/** Last sampled price at or before `slot`, or null when the tape starts later. */
function priceBefore(mint: Pubkey, slot: number): number | null {
  const tape = tapes.get(mint);
  if (tape === undefined || tape.length === 0) return null;
  let lo = 0;
  let hi = tape.length - 1;
  let ans = -1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (tape[mid].slot <= slot) {
      ans = mid;
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }
  return ans >= 0 ? tape[ans].price : null;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const traded = new Set<Pubkey>();

    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        createdAt.set(e.mint, e.slot);
        if (!tapes.has(e.mint)) tapes.set(e.mint, []);
      } else if (e.event === 'TradeEvent') {
        if (!createdAt.has(e.mint)) continue; // trade-first mint: launch missed, skip
        const tape = tapes.get(e.mint);
        if (tape === undefined) continue;
        tape.push({
          slot: e.slot,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
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

    // --- exits first: stop loss, trailing stop, time limit ---
    for (const [mint, ride] of rides) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) rides.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? BigInt(mk.virtual_quote_reserves) : curve.virtual_quote_reserves;
      const vt = mk ? BigInt(mk.virtual_token_reserves) : curve.virtual_token_reserves;
      const value = closeValue(pos.token_amount, vq, vt, state.txFeeLamports());
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      if (value > ride.peak) ride.peak = value;
      if (!ride.armed && value >= cost * (1 + TRAIL_ARM)) ride.armed = true;
      let exit = ride.exiting;
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && ride.armed && value <= ride.peak * (1 - TRAIL_GIVEBACK)) exit = true;
      if (!exit && now - ride.opened > MAX_HOLD) exit = true;
      if (!exit) continue;
      ride.exiting = true;
      let sellPending = false;
      for (const po of state.pending.values()) {
        if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
      }
      if (sellPending) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
    }

    // --- entries: coins aged 120-600 slots that rose >=20% over the last 120 ---
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    for (const mint of traded) {
      if (orders.length >= cap) break;
      if (slotsLeft <= 0) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || rides.has(mint) || bought.has(mint)) continue;
      const created = createdAt.get(mint);
      if (created === undefined) continue;
      const age = now - created;
      if (age < MIN_AGE || age > MAX_AGE) continue;
      const past = priceBefore(mint, now - LOOKBACK);
      const nowPrice = priceBefore(mint, now);
      if (past === null || nowPrice === null || past <= 0) continue;
      if (nowPrice / past - 1 < MIN_RISE) continue;
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, STAKE_SOL);
      if (amount > free - tx) amount = free - tx;
      if (amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      bought.add(mint);
      rides.set(mint, { opened: now, peak: 0, armed: false, exiting: false });
      free -= amount + tx;
      slotsLeft--;
    }
    return orders;
  },
});
