# dex-verity

A constant-product automated market maker (AMM), in the style of Uniswap V2. It is written in
[Verity](https://github.com/mab-xyz/verity), a Lean 4 language for smart contracts, and
compiled by Verity to EVM bytecode. Lean proves 24 properties of the contracts. Foundry tests
the compiled bytecode: unit, fuzz, invariant and differential tests, plus mutation testing.

This README explains, for each proved property, what it says, which attack it rules out,
and what it does not cover.

- [The contracts in one page](#the-contracts-in-one-page)
- [How to read a theorem here](#how-to-read-a-theorem-here)
- [Threat model](#threat-model)
- [The properties, by threat](#the-properties-by-threat)
- [Threat coverage map](#threat-coverage-map)
- [What is not covered](#what-is-not-covered)
- [Testing the compiled bytecode](#testing-the-compiled-bytecode)
- [Trust base](#trust-base)
- [Reproduce](#reproduce)

## The contracts in one page

| Contract | File | Role |
|---|---|---|
| `Pool` | `Dex/Pool.lean` | Holds one token pair. Stores the two *reserves* and an internal ledger of liquidity-provider (*LP*) shares. Entry points: `mint` (deposit, receive shares), `burn` (return shares, withdraw), `swap`, `sync`; and an ERC-20-like LP ledger (`transfer`, `transferFrom`, `approve`). |
| `Router` | `Dex/Router.lean` | What users call: `addLiquidity`, `removeLiquidity`, `swapExactIn`, each with a deadline and slippage bounds. |
| `Factory` | `Dex/Factory.lean` | Deploys one pool per token pair with CREATE2 and records it (`getPool`, `allPoolsLength`, `poolAt`). |

Three design points matter for the properties:

- **Balance-delta accounting.** Users send tokens to the pool first; the pool then measures
  what arrived by asking each token for its `balanceOf(pool)`. The pool never trusts an
  amount a caller claims.
- **The k-invariant.** A swap is accepted only if `reserve0 * reserve1` does not decrease
  after a 0.3% fee on the input. This is what keeps liquidity providers from being drained.
- **One lock per pool.** `mint`, `burn`, `swap` and `sync` are `nonreentrant`: while one
  runs, a nested call to any of them reverts.

Two names differ from Uniswap V2 because of Lean: `initialize` and `to` are Lean keywords, so the
pool uses `initPool` and `recipient`. The LP getters are `lpBalanceOf`, `lpAllowance` and
`lpTotalSupply`, so they do not shadow Verity's `balanceOf token owner` helper.

## How to read a theorem here

Every contract property is a Lean theorem about the contract's *executable semantics*: the
Lean function the Verity compiler compiles to bytecode. Most have this shape:

```lean
theorem swap_k_nondecreasing (ctx : ExecutableCallContext) (out0 out1 : Uint256)
    (rcpt : Address) (s s' : ContractState)
    (hr0 : (s.storage 3).val < 2 ^ 112) (hr1 : (s.storage 4).val < 2 ^ 112)
    (h : Pool.swap ctx out0 out1 rcpt s = .success () s') :
    (s'.storage 3).val < 2 ^ 112 ∧ (s'.storage 4).val < 2 ^ 112 ∧
      (s.storage 3).val * (s.storage 4).val ≤ (s'.storage 3).val * (s'.storage 4).val
```

Read it as follows:

- **For every state `s`.** That covers every history, every caller and every block
  timestamp, plus whatever other users did just before (front-running included).
- **For every argument**, here `out0`, `out1` and `rcpt`.
- **For every behaviour of the outside world (`ctx`).** `ctx.adversary` answers every
  external call the contract makes: what each token's `balanceOf` returns, whether each
  `transfer` succeeds, and how the world changes during the call. Only one theorem narrows
  this: the burn-supply theorem (L2), which uses Verity's reentrancy model and is explained
  where it appears.
- **If the call succeeds** and ends in state `s'`, the conclusion holds. Where a call must
  fail, a separate theorem states the revert (`… = .revert msg s`).

Storage slots are named in `Dex/Pool.lean`. For the pool: 3 and 4 are the reserves, 5 the
LP supply, 6 the LP balances, 9 the lock.

All proofs are checked by the Lean kernel, with no `sorry`. They rely only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`; check with `#print axioms`).

## Threat model

These attackers are in scope. Each property below says which of them it stops.

- **T1, a hostile token.** One of the pool's two tokens behaves arbitrarily:
  - it lies in `balanceOf`;
  - it takes a fee on transfer or rebases;
  - it reverts, or returns garbage;
  - it re-enters the pool or the router from inside a transfer.

  In the proofs this token is `ctx.adversary`, and the theorems hold for every choice.
- **T2, a hostile trader or LP.** Any sequence of calls with any arguments, made directly
  to the pool, bypassing the router.
- **T3, front-running and stale transactions.** Between signing and inclusion, others move
  the price, or the transaction lands much later.
- **T4, rounding and overflow abuse.** Inputs chosen so integer rounding or 256-bit wrap-around
  pays the attacker.
- **T5, first-depositor and empty-pool games.** Manipulating a pool while its supply is zero
  or tiny, so that later depositors receive too few shares.
- **T6, fake pools and hijacked deployment.** A pool not deployed by the factory, a pool
  deployed with different code, two pools for one pair, or someone else initialising a fresh
  pool.
- **T7, reentrancy into the pool.** A token transfer calls back into the pool mid-operation.

## The properties, by threat

### Swap safety: liquidity providers cannot be drained (T1, T2, T4, T7)

**L3, the constant product never decreases** (`swap_k_nondecreasing`).
- **Says:** if a swap succeeds, the new `reserve0 * reserve1` is at least the old one, and
  both reserves stay below 2^112.
- **Why it matters:** this is the core AMM guarantee. Every possible swap trades along or
  above the curve, so liquidity cannot be taken without paying for it.
- **Strength:** it holds for every `ctx`, with no reentrancy assumption. Even a token that
  re-enters during the payout and rewrites anything cannot produce a successful swap that
  lowers k. The reason is that the check compares the balances measured *after* the payout
  against the reserves read *before* it, and those measured balances become the new
  reserves.
- **Built from:**
  - `settle_k_nondecreasing`, the measure-then-check step;
  - `k_of_check`, the arithmetic: the fee-adjusted check implies the raw product grows.

**L8, a swap asking for nothing reverts** (`swap_reverts_without_output`).
- `swap(0, 0, …)` reverts in every state, so a swap must request some output.

**L6, reserves stay below 2^112** (`sync_/mint_/burn_preserves_reserve_cap`, and the cap
conclusion of `swap_k_nondecreasing`).
- **Says:** every entry point that writes the reserves leaves them below 2^112.
- **Why it matters:** this is L3's hypothesis, and it guarantees `reserve0 * reserve1` never
  wraps around 2^256 (T4).
- **Closing the loop:** a fresh pool has reserves 0, and every writer keeps the cap. So by
  induction over any sequence of successful calls, L3's hypothesis always holds and k never
  falls.

**P2–P4, the swap formula**: pure math in `Dex/Math.lean`, the formula the router quotes.
- **P2** (`getAmountOut_lt_reserve`): an exact-in swap never asks for the whole output
  reserve.
- **P3** (`getAmountOut_mono`): more input never yields less output, so there is no
  price inversion to exploit.
- **P4** (`kCheck_getAmountOut`): paying `amountIn` and taking `getAmountOut(amountIn)`
  passes the pool's k-check. The router's quote is therefore always acceptable to the pool,
  and honest users are not rejected.

**P6, the exact-out formula is sufficient** (`getAmountOut_getAmountIn`).
- Paying `getAmountIn(out)` buys at least `out`. The rounding-up in `getAmountIn` is
  enough, so a user who pays it is never short-changed (T4).

### Liquidity accounting: shares stay honest (T2, T4, T5, T7)

**L2, LP shares are conserved.**
- **`transfer_conserves_lp_sum`** (with `transfer_balances` and `transfer_succeeds`):
  - an LP transfer moves shares and creates none: the sum of balances over any set of
    holders containing both parties is unchanged;
  - only the two parties' balances change;
  - a transfer within the sender's balance succeeds.
- **`mint_lp_accounting`**, for every token answer:
  - a successful `mint` gives the recipient (any address other than 0) exactly the `v`
    shares it reports, and `v > 0`;
  - the supply grows by exactly `v`;
  - no other holder's balance changes;
  - exception, the first mint: the supply becomes `1000 + v`, with the extra 1000 credited
    to address 0 (see L5).
- **`burn_supply_drops_by_burned`**: the supply drops by exactly the shares burned, i.e. the
  pool's own LP balance at the start of the burn.
  - This one is proved under reentrancy. During the payout, a token may call back into any
    pool entry point, any number of times (Verity's `CallbackBounded` model).
  - The proof (`registry_preserves`) checks all twelve entry points. The four locked ones
    revert. The eight others (`initPool`, the getters, `approve`, `transfer`,
    `transferFrom`) never write the supply.
  - *What it does not say:* LP balances can legitimately move during a burn, through a
    re-entrant `transfer` (see [What is not covered](#what-is-not-covered)).

**L4, burns are proportional and rounded in the pool's favour** (`burn_proportional`,
`burn_payout_le`).
- **Says:** burning `liq` of `supply` shares pays `liq * balance / supply` of each token,
  rounded down, and both amounts are positive. With `liq ≤ supply`, no payout exceeds the
  pool's balance.
- **Why it matters (T4):** no sequence of mints and burns can extract more than a
  proportional share. Rounding always favours the remaining LPs.

**L5, the first deposit locks 1000 shares** (`mint_first_locks_min_liquidity`).
- **Says:** the first `mint` into an empty pool sets the supply to `1000 + v`. The 1000 go
  to address 0, which can never burn them, and the depositor gets `v > 0`.
- **Why it matters (T5):** this is Uniswap V2's defence against the share-inflation attack.
  With a permanent floor of 1000 shares, an attacker cannot make one share worth so much that
  later deposits round down to zero shares.

**P1, the square root is exact** (`Dex.Isqrt.isqrt_eq_sqrt`, `isqrt_floor`).
- **Says:** the first mint prices shares at `isqrt(amount0 * amount1)`. The theorem proves
  the contract's own `isqrt` returns exactly `⌊√n⌋`, i.e. `r² ≤ n < (r+1)²`, and never
  reverts, for every `n < 2^255` (the pool calls it with `n < 2^224`).
- **Proof idea:**
  - each Babylonian step lands at or above the root (integer AM-GM);
  - above the root, each step halves the distance to it;
  - so the loop's 256 rounds are enough to reach the root;
  - and the contract's 256-bit arithmetic never wraps along the way.
- **Why it matters:** an inexact root would mis-price the first shares, and a revert would
  make some first deposits impossible (T5).

**P5, quotes never overstate** (`quote_mul_le`).
- `quote(a, rA, rB) * rA ≤ a * rB`: the amount quoted at the pool price is rounded down
  (T4).

### Pool state reflects reality (T1, T2)

**L9, `sync` stores what the tokens report** (`sync_reserves_eq_reported`).
- **Says:** after a successful `sync`, each reserve is exactly the value that token
  returned to `balanceOf(pool)`, for every token behaviour.
- **Why it matters:** `sync` is how a pool recovers from tokens sent directly to it
  (donations), or from a token whose balance changes on its own (rebasing). The theorem
  says the pool adopts the token's own report and nothing else. If the token lies, the pool
  believes it; that is the T1 boundary (see [What is not covered](#what-is-not-covered)).

**L7, the lock works** (`swap_/mint_/sync_reverts_when_locked`).
- While the lock is held, `swap`, `mint` and `sync` revert and leave the state untouched.
  This is the guarantee the reentrancy argument for `burn` in L2 builds on (T7).

### Deployment integrity: the right pools, set up by the right party (T6)

**L1, a pool is initialised once, and only by its factory** (`initPool_reverts_when_not_factory`,
`initPool_reverts_when_initialized`, `initPool_succeeds`, `initPool_records_tokens`,
`initPool_marks_initialized`).
- `initPool` reverts unless the caller is the address that deployed the pool, the factory.
  It also reverts on a second call.
- On the first call it records the two tokens and marks the pool initialised.
- So nobody can front-run the factory and set a pool's tokens.

**F5, pool addresses are the CREATE2 addresses of the pinned code** (`createPool_address`).
- **Says:** the factory refuses creation code that does not hash to `poolCodeHash`, which is
  fixed at construction. The created pool's address is the CREATE2 address computed from the
  factory, a salt, and `poolCodeHash`.
- **Why it matters:** anyone can recompute where a pool lives and check it runs the audited
  pool code. Barring a keccak collision, a pool with other code cannot sit at that address.

**F1/F4, F2, F3, one pool per pair, findable both ways** (`createPool_registers`,
`createPool_reverts_existing`, `createPool_reverts_identical`).
- A successful `createPool` registers the pool under both token orders, so `getPool(A, B)`
  and `getPool(B, A)` agree, and increments the pool count.
- Creating a pair that already exists reverts, so there are no duplicate pools to split
  liquidity or confuse routers.
- Creating a pool of a token with itself reverts.

### User protection at the router (T3)

These hold whatever the factory, pool and tokens answer: the checks are in the router.

**R1, deadlines** (`swapExactIn_/addLiquidity_/removeLiquidity_reverts_after_deadline`).
- Past the deadline, every router entry point reverts. A transaction that sat in the
  mempool cannot execute at a stale price.

**R2, slippage on swaps** (`swapExactIn_respects_min`).
- A successful `swapExactIn` returns at least `amountOutMin`. A sandwich attack can push the
  price only as far as the user's own bound.

**R3, deposits stay within bounds** (`quoteAmounts_bounds`).
- **Says:** the amounts `addLiquidity` transfers, computed by the helper `quoteAmounts`,
  never exceed the desired amounts. Into a non-empty pool, one amount is the desired one
  and the other meets its minimum (Uniswap V2's rule).
- So a moved price cannot make a depositor overpay. The theorem is about the helper. That
  `addLiquidity` hands the helper's result to the two transfers is visible in the source,
  and fuzz-tested on the bytecode.

**R4, slippage on withdrawals** (`removeLiquidity_respects_mins`).
- A successful `removeLiquidity` returns at least both minimums.

## Threat coverage map

| Threat | Properties that address it |
|---|---|
| T1, hostile token | every contract theorem quantifies over all token behaviour; L3, L9, L2 (mint), R2, R4 do not depend on token honesty |
| T2, hostile trader or LP | L3, L8, L2, L4, L1 (theorems for every state and argument) |
| T3, front-running, stale transactions | R1, R2, R3, R4 |
| T4, rounding, overflow | L4, P5, P6, L6 (no wrap in k), P1, P2, P3 |
| T5, first depositor | L5, P1, L2 (mint) |
| T6, fake pools, deployment hijack | F5, F1–F3, L1 |
| T7, reentrancy | L7, L3 (holds against any reentrant behaviour), L2 (burn: under `CallbackBounded`) |

## What is not covered

These are limits of the guarantees, stated so they are not mistaken for gaps in the proofs.

- **A lying token lies to the pool.** If a token's `balanceOf` reports funds it never
  received, the pool accepts them, as any balance-delta AMM does. L3 then still holds in
  the pool's accounting, but that accounting is only as true as the token. Pools with
  unknown tokens are at the LPs' risk.
- **LP shares can move during a burn.** `transfer`, `transferFrom` and `approve` are not
  locked, as in Uniswap V2. A token's callback during `burn` can move LP shares between
  holders. The supply theorem holds regardless; per-holder balances after a burn are not
  claimed.
- **Prices, not just rules.** The proofs say trades follow the curve and the user's bounds.
  They do not say the price is fair. A sandwich within the user's slippage bound is allowed,
  and there is no price oracle here (no TWAP).
- **Gas and liveness.** Gas is not modelled. A theorem saying a call succeeds says so
  assuming enough gas; denial-of-service through gas is out of scope.
- **Partial correctness.** Theorems of the form "if the call succeeds, then …" say nothing
  about calls that revert. The revert theorems (L1, L7, L8, F2, F3, R1) and P1's "never
  reverts" state the important failure cases explicitly.

## Testing the compiled bytecode

The proofs are about the executable semantics; the tests run the bytecode that is actually
deployed. `scripts/build-evm.sh` compiles the contracts to Yul (`lake exe dex-compile`) and
then to bytecode with solc. Every Foundry test deploys that bytecode.

| Layer | Path | What it checks |
|---|---|---|
| Unit | `test/unit/` | 34 tests: every pool, router and factory entry point, its reverts and its state effects; the CREATE2 address; the full router → factory → pool stack; both `addLiquidity` branches, and R3's bound fuzzed |
| Fuzz | `test/fuzz/` | the exact swap formula is accepted, one wei more is rejected, k holds; burns are proportional |
| Invariant | `test/invariant/` | random operation sequences keep LP shares = supply, reserves = balances, reserves < 2^112, and k monotone over swaps |
| Differential | `test/differential/` | the same fuzzed sequence on the Verity pool and on a Solidity reference (`test/ref/RefPool.sol`) gives identical results |
| Mutation | `scripts/mutants.sh` | six Yul mutants (fee removed, k-check flipped or removed, MIN_LIQUIDITY unlocked, burn cap removed, lock ignored); every one must be caught |

## Trust base

What you must trust for the proofs to say something about the chain:

- **The Lean kernel**, which checks every proof.
- **Verity's compiler**, from the executable semantics to Yul. Verity proves parts of this
  translation and documents the rest in its `docs/TRUST_ASSUMPTIONS.md`. The tests above
  check the compiled code directly.
- **solc**, from Yul to bytecode.
- **The model of external calls.** Tokens are an arbitrary adversary: the theorems quantify
  over every answer and every world change. The burn theorem uses Verity's narrower
  `CallbackBounded` model, in which a callback is a sequence of the pool's own entry points.
- **The Verity fork.** `lakefile.lean` pins `mab-xyz/verity` (branch `ours`). Three of its
  fixes matter here:
  - real `keccak256` and CREATE2 semantics, needed for F5 (`fix/edsl-memory-hash-semantics`);
  - loops that run like the bytecode, needed for P1 and L5 (`fix/foreach-executable-iterates`);
  - token reads answered by the adversary even inside helpers and view-only entry points,
    which makes "for every token behaviour" true for `mint`, `sync` and `swap`
    (`fix/view-call-helpers-adversary`).

## Reproduce

```sh
lake exe cache get && lake build          # all proofs
SOLC=solc scripts/build-evm.sh            # Yul + bytecode in out/
forge test                                # unit, fuzz, invariant, differential
scripts/mutants.sh                        # every mutant must be KILLED
```
