import Contracts.Common
import Dex.Pool

namespace Dex

open Contracts
open Verity hiding pure bind contractAddress blockTimestamp
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-! Function selectors of the factory and pool entry points the router calls. -/
def selGetPool : Nat := Compiler.keccak256_first_4_bytes "getPool(address,address)"
def selGetReserves : Nat := Compiler.keccak256_first_4_bytes "getReserves()"
def selMint : Nat := Compiler.keccak256_first_4_bytes "mint(address)"
def selBurn : Nat := Compiler.keccak256_first_4_bytes "burn(address)"
def selSwap : Nat := Compiler.keccak256_first_4_bytes "swap(uint256,uint256,address)"
def selLpTransferFrom : Nat :=
  Compiler.keccak256_first_4_bytes "transferFrom(address,address,uint256)"

/-!
# Router

User-facing entry points: it pulls tokens from the caller into the pool (the caller
approves the router), then calls the pool. Every entry point takes a `deadline` and
slippage bounds. `getAmountOut`/`quote` are the formulas of `Dex.Math`, evaluated with
512-bit `mulDiv` so they never overflow.
-/
verity_contract Router where
  storage
    factory : Address := slot 0
    lock : Uint256 := slot 1

  constructor (fac : Address) := do
    setStorageAddr factory fac

  function getAmountOut (amountIn : Uint256, reserveIn : Uint256, reserveOut : Uint256) : Uint256 := do
    require (amountIn > 0) "Router: INSUFFICIENT_INPUT_AMOUNT"
    require (reserveIn > 0) "Router: INSUFFICIENT_LIQUIDITY"
    require (reserveOut > 0) "Router: INSUFFICIENT_LIQUIDITY"
    require (reserveIn < 5192296858534827628530496329220096) "Router: OVERFLOW"
    require (amountIn < 5192296858534827628530496329220096) "Router: OVERFLOW"
    let amountInWithFee := mul amountIn 997
    let denominator := add (mul reserveIn 1000) amountInWithFee
    return mulDiv512Down amountInWithFee reserveOut denominator

  function quote (amountA : Uint256, reserveA : Uint256, reserveB : Uint256) : Uint256 := do
    require (amountA > 0) "Router: INSUFFICIENT_AMOUNT"
    require (reserveA > 0) "Router: INSUFFICIENT_LIQUIDITY"
    return mulDiv512Down amountA reserveB reserveA

  function internal poolFor (tokenA : Address, tokenB : Address) : Address := do
    let fac ← getStorageAddr factory
    let poolWord ← ecmCall (fun r => Compiler.Modules.Calls.withReturnModule r selGetPool 2 true)
      [addressToWord fac, addressToWord tokenA, addressToWord tokenB]
    require (poolWord != 0) "Router: POOL_NOT_FOUND"
    return wordToAddress poolWord

  function nonreentrant(lock) swapExactIn (amountIn : Uint256, amountOutMin : Uint256, tokenIn : Address,
      tokenOut : Address, recipient : Address, deadline : Uint256) : Uint256 := do
    let now ← blockTimestamp
    require (now <= deadline) "Router: EXPIRED"
    let pool ← poolFor tokenIn tokenOut
    ecmBind [r0, r1] (Compiler.Modules.Calls.withReturnsModule ["r0", "r1"] selGetReserves 0 true)
      [addressToWord pool]
    let inIsToken0 := addressToWord tokenIn < addressToWord tokenOut
    let reserveIn := if inIsToken0 then r0 else r1
    let reserveOut := if inIsToken0 then r1 else r0
    require (amountIn > 0) "Router: INSUFFICIENT_INPUT_AMOUNT"
    require (reserveIn > 0) "Router: INSUFFICIENT_LIQUIDITY"
    require (reserveOut > 0) "Router: INSUFFICIENT_LIQUIDITY"
    require (amountIn < 5192296858534827628530496329220096) "Router: OVERFLOW"
    let amountInWithFee := mul amountIn 997
    let amountOut := mulDiv512Down amountInWithFee reserveOut (add (mul reserveIn 1000) amountInWithFee)
    require (amountOut >= amountOutMin) "Router: INSUFFICIENT_OUTPUT_AMOUNT"
    let sender ← msgSender
    safeTransferFrom tokenIn sender pool amountIn
    let out0 := if inIsToken0 then 0 else amountOut
    let out1 := if inIsToken0 then amountOut else 0
    ecmDo (Compiler.Modules.Calls.noReturnModule selSwap 3 false)
      [addressToWord pool, out0, out1, addressToWord recipient]
    return amountOut

  function nonreentrant(lock) addLiquidity (tokenA : Address, tokenB : Address, amountADesired : Uint256,
      amountBDesired : Uint256, amountAMin : Uint256, amountBMin : Uint256, recipient : Address,
      deadline : Uint256) : Uint256 := do
    let now ← blockTimestamp
    require (now <= deadline) "Router: EXPIRED"
    let pool ← poolFor tokenA tokenB
    ecmBind [r0, r1] (Compiler.Modules.Calls.withReturnsModule ["r0", "r1"] selGetReserves 0 true)
      [addressToWord pool]
    let aIsToken0 := addressToWord tokenA < addressToWord tokenB
    let reserveA := if aIsToken0 then r0 else r1
    let reserveB := if aIsToken0 then r1 else r0
    let mut amountA := amountADesired
    let mut amountB := amountBDesired
    if reserveA != 0 || reserveB != 0 then
      let amountBOptimal := mulDiv512Down amountADesired reserveB reserveA
      if amountBOptimal <= amountBDesired then
        require (amountBOptimal >= amountBMin) "Router: INSUFFICIENT_B_AMOUNT"
        amountB := amountBOptimal
      else
        let amountAOptimal := mulDiv512Down amountBDesired reserveA reserveB
        require (amountAOptimal <= amountADesired) "Router: INSUFFICIENT_A_AMOUNT"
        require (amountAOptimal >= amountAMin) "Router: INSUFFICIENT_A_AMOUNT"
        amountA := amountAOptimal
    let sender ← msgSender
    safeTransferFrom tokenA sender pool amountA
    safeTransferFrom tokenB sender pool amountB
    let liquidity ← ecmCall (fun r => Compiler.Modules.Calls.withReturnModule r selMint 1 false)
      [addressToWord pool, addressToWord recipient]
    return liquidity

  function nonreentrant(lock) removeLiquidity (tokenA : Address, tokenB : Address, liquidity : Uint256,
      amountAMin : Uint256, amountBMin : Uint256, recipient : Address,
      deadline : Uint256) : Tuple [Uint256, Uint256] := do
    let now ← blockTimestamp
    require (now <= deadline) "Router: EXPIRED"
    let pool ← poolFor tokenA tokenB
    let sender ← msgSender
    let _moved ← ecmCall (fun r => Compiler.Modules.Calls.withReturnModule r selLpTransferFrom 3 false)
      [addressToWord pool, addressToWord sender, addressToWord pool, liquidity]
    ecmBind [amount0, amount1] (Compiler.Modules.Calls.withReturnsModule ["amount0", "amount1"] selBurn 1 false)
      [addressToWord pool, addressToWord recipient]
    let aIsToken0 := addressToWord tokenA < addressToWord tokenB
    let amountA := if aIsToken0 then amount0 else amount1
    let amountB := if aIsToken0 then amount1 else amount0
    require (amountA >= amountAMin) "Router: INSUFFICIENT_A_AMOUNT"
    require (amountB >= amountBMin) "Router: INSUFFICIENT_B_AMOUNT"
    return (amountA, amountB)

end Dex
