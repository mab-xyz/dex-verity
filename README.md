# dex-verity

A constant-product AMM DEX (Uniswap-V2 style: router, pool factory, pools) written in
[Verity](https://github.com/mab-xyz/verity) (Lean 4). Its properties are proved in Lean,
and the EVM bytecode the Verity compiler produces is tested with Foundry.

## Contracts

| Contract | File | Role |
|---|---|---|
| `Pool` | `Dex/Pool.lean` | One token pair: reserves, LP shares (internal ledger), `mint`/`burn`/`swap`/`sync`. Callers transfer tokens in first; the pool measures what arrived (balance-delta accounting). 0.3% fee. Balances are capped below 2^112. |
| `Router` | `Dex/Router.lean` | User entry points: `addLiquidity`, `removeLiquidity`, `swapExactIn`, with deadlines and slippage bounds; pure `getAmountOut`/`quote`. |
| `Factory` | `Dex/Factory.lean` | One pool per pair, deployed with CREATE2 (salt `keccak256(abi.encode(token0, token1))`) from creation code that must hash to `poolCodeHash`; registry `getPool` (both orders), `allPoolsLength`, `poolAt`. |

Names forced by Lean: `initialize` and `to` are keywords, so the pool uses `initPool` and
`recipient`; its LP getters are `lpBalanceOf`/`lpAllowance`/`lpTotalSupply` (a contract
function named `balanceOf` would hide Verity's ERC-20 `balanceOf token owner` helper).

## Proved properties

All theorems are over Verity's EDSL semantics of the contracts above; no `sorry`, no axiom.
Token contracts are an arbitrary adversary: pool theorems hold for every token behaviour,
including reentrant ones.

| Id | Property | Theorem(s) |
|---|---|---|
| P2 | An exact-in swap never drains the output reserve | `Dex.Math.getAmountOut_lt_reserve` |
| P3 | More input never gives less output | `Dex.Math.getAmountOut_mono` |
| P4 | Paying `amountIn` and taking `getAmountOut` passes the k-check | `Dex.Math.kCheck_getAmountOut` |
| P5 | `quote` never overstates | `Dex.Math.quote_mul_le` |
| L1 | A pool is initialised once, only by its factory | `initPool_reverts_when_not_factory`, `initPool_reverts_when_initialized`, `initPool_succeeds`, `initPool_records_tokens`, `initPool_marks_initialized` |
| L2 | LP accounting: transfers conserve the holder sum; `mint` adds the minted shares to the recipient and the supply (first mint: plus 1000 locked at the zero address), no other holder changes; `burn` lowers the supply by exactly the pool's own LP balance, even if the tokens re-enter the pool | `transfer_conserves_lp_sum` (with `transfer_succeeds`, `transfer_balances`), `mint_lp_accounting`, `burn_supply_drops_by_burned` (with `registry_preserves`) |
| L3 | A successful swap never decreases `reserve0 * reserve1` | `swap_k_nondecreasing` (with `settle_k_nondecreasing`, `k_of_check`) |
| L4 | A burn pays the rounded-down share `liquidity / supply` of each measured balance: positive, and at most that balance when `liquidity ≤ supply` | `burn_proportional`, `burn_payout_le` |
| L5 | The first mint locks 1000 shares at the zero address; supply = 1000 + minted shares, minted > 0 | `mint_first_locks_min_liquidity` (with `isqrt_state`, `loopList_state`) |
| L6 | Every reserve write keeps reserves below 2^112 (L3's precondition) | `sync_/mint_/burn_preserves_reserve_cap`, `swap_k_nondecreasing` |
| L7 | With the lock held, `swap`/`mint`/`sync` revert without effect | `swap_reverts_when_locked`, `mint_reverts_when_locked`, `sync_reverts_when_locked` |
| L8 | A swap asking for no output reverts | `swap_reverts_without_output` |
| L9 | After `sync`, each reserve is the value its token returned to `balanceOf(pool)`, for every token behaviour | `sync_reserves_eq_reported` |
| F1, F4 | A created pool is registered once, under both token orders, and counted | `createPool_registers` |
| F2 | Creating an existing pair reverts | `createPool_reverts_existing` |
| F3 | Identical tokens revert | `createPool_reverts_identical` |
| F5 | The pool address is CREATE2(factory, salt, `poolCodeHash`): the deployed code hashes to `poolCodeHash` | `createPool_address` |
| R1 | Past the deadline every router entry point reverts | `swapExactIn_/addLiquidity_/removeLiquidity_reverts_after_deadline` |
| R2 | A successful `swapExactIn` returns at least `amountOutMin` | `swapExactIn_respects_min` |
| R3 | `addLiquidity` never transfers more than the desired amounts; into a non-empty pool one amount is the desired one and the other meets its minimum | `quoteAmounts_bounds` (the helper computing the transferred amounts) |
| R4 | A successful `removeLiquidity` returns at least both minimums | `removeLiquidity_respects_mins` |

P1 (`isqrt` is exact) holds by construction: the pool checks `r*r ≤ n ≤ r*r + 2r` at
runtime after its Babylonian loop.

## Testing the compiled EVM code

`scripts/build-evm.sh` compiles the Verity contracts to Yul (`lake exe dex-compile`) and the
Yul to bytecode with solc; every Foundry test deploys that bytecode.

| Layer | Path | What it checks |
|---|---|---|
| Unit | `test/unit/` | 32 tests: every pool/router/factory entry point, its reverts and its state effects; the CREATE2 address; the full router → factory → pool stack |
| Fuzz | `test/fuzz/` | exact swap formula accepted, one wei more rejected, k kept; proportional burns |
| Invariant | `test/invariant/` | random operation sequences keep LP shares = supply, reserves = balances, reserves < 2^112, k monotone |
| Differential | `test/differential/` | same fuzzed sequence on the Verity pool and a Solidity reference (`test/ref/RefPool.sol`): identical results |
| Mutation | `scripts/mutants.sh` | six Yul mutants (fee, k-check, MIN_LIQUIDITY, burn cap, lock); all must be killed |

## Trust assumptions

- Verity's own trust boundary (`docs/TRUST_ASSUMPTIONS.md` upstream): the compiler's proofs
  cover its supported fragment; solc is trusted; gas is not modelled.
- External calls (tokens, pools seen from the router/factory) are modelled as an
  arbitrary adversary or oracle; properties never assume a well-behaved token.
- `keccak256` and CREATE2 use the fork's exact models (`fix/edsl-memory-hash-semantics`); loops
  run like the bytecode (`fix/foreach-executable-iterates`).
- Token reads (`balanceOf`), including those inside helpers (`Pool.settle`) and in `mint` and
  `sync`, are answered by the call context's adversary (`fix/view-call-helpers-adversary`):
  every pool and router theorem quantifies over all token answers.
- Reentrancy (`burn_supply_drops_by_burned`): the token calls may re-enter any pool entry
  point (`CallbackBounded Pool.entrypointRegistry`, Verity's reentrancy model). The guarded
  ones revert under the lock; `transfer`, `transferFrom` and `approve` are not guarded, so
  LP balances can move during a burn and the theorem states only the supply.

## Reproduce

```sh
lake exe cache get && lake build          # all proofs
SOLC=solc scripts/build-evm.sh            # Yul + bytecode in out/
forge test                                # unit, fuzz, invariant, differential
scripts/mutants.sh                        # every mutant must be KILLED
```
