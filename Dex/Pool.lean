import Contracts.Common

namespace Dex

open Contracts
open Verity hiding pure bind contractAddress blockTimestamp
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-!
# Pool: one constant-product pair

Balance-delta accounting (Uniswap V2 style): callers transfer tokens to the pool first,
then call `mint`/`swap`; the pool measures what arrived with `balanceOf`. Reserves and
balances are capped below `2^112`, so every product in the k-check fits in 256 bits.

LP shares are an internal ERC-20 ledger (`balances`, `allowances`, `totalSupply`).
`MIN_LIQUIDITY` shares are locked at address 0 on the first mint.
-/
verity_contract Pool where
  storage
    factory : Address := slot 0
    token0 : Address := slot 1
    token1 : Address := slot 2
    reserve0 : Uint256 := slot 3
    reserve1 : Uint256 := slot 4
    totalSupply : Uint256 := slot 5
    balances : Address → Uint256 := slot 6
    allowances : Address → Address → Uint256 := slot 7
    initialized : Uint256 := slot 8
    lock : Uint256 := slot 9

  event_defs
    event Mint(@indexed sender : Address, amount0 : Uint256, amount1 : Uint256, liquidity : Uint256)
    event Burn(@indexed sender : Address, amount0 : Uint256, amount1 : Uint256, @indexed recipient : Address)
    event Swap(@indexed sender : Address, in0 : Uint256, in1 : Uint256, out0 : Uint256, out1 : Uint256, @indexed recipient : Address)
    event Sync(reserve0 : Uint256, reserve1 : Uint256)
    event Transfer(@indexed src : Address, @indexed dst : Address, amount : Uint256)
    event Approval(@indexed owner : Address, @indexed spender : Address, amount : Uint256)

  constructor () := do
    let deployer ← msgSender
    setStorageAddr factory deployer

  -- Integer square root: Babylonian iteration, then a runtime check that the result is
  -- exact, so every successful call satisfies `r*r ≤ n < (r+1)*(r+1)` (property P1).
  function internal isqrt (n : Uint256) : Uint256 := do
    let mut z := 0
    if n > 3 then
      z := n
      let mut x := add (div n 2) 1
      forEach "i" 256 (do
        if x < z then
          z := x
          x := div (add (div n x) x) 2)
    else
      if n != 0 then
        z := 1
    require (mul z z <= n) "isqrt: too large"
    require (sub n (mul z z) <= mul 2 z) "isqrt: too small"
    return z

  function initPool (t0 : Address, t1 : Address) : Unit := do
    let sender ← msgSender
    let fac ← getStorageAddr factory
    require (sender == fac) "Pool: FORBIDDEN"
    let done ← getStorage initialized
    require (done == 0) "Pool: ALREADY_INITIALIZED"
    setStorageAddr token0 t0
    setStorageAddr token1 t1
    setStorage initialized 1

  function getReserves () : Tuple [Uint256, Uint256] := do
    let r0 ← getStorage reserve0
    let r1 ← getStorage reserve1
    return (r0, r1)

  -- LP share ledger (ERC-20 surface).
  function lpBalanceOf (owner : Address) : Uint256 := do
    let bal ← getMapping balances owner
    return bal

  function lpAllowance (owner : Address, spender : Address) : Uint256 := do
    let amount ← getMapping2 allowances owner spender
    return amount

  function lpTotalSupply () : Uint256 := do
    let supply ← getStorage totalSupply
    return supply

  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount
    emit "Approval" [sender, spender, amount]
    return true

  function transfer (dst : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let srcBal ← getMapping balances sender
    require (srcBal >= amount) "Pool: INSUFFICIENT_BALANCE"
    setMapping balances sender (sub srcBal amount)
    let dstBal ← getMapping balances dst
    setMapping balances dst (add dstBal amount)
    emit "Transfer" [sender, dst, amount]
    return true

  function transferFrom (src : Address, dst : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let allowed ← getMapping2 allowances src sender
    require (allowed >= amount) "Pool: INSUFFICIENT_ALLOWANCE"
    setMapping2 allowances src sender (sub allowed amount)
    let srcBal ← getMapping balances src
    require (srcBal >= amount) "Pool: INSUFFICIENT_BALANCE"
    setMapping balances src (sub srcBal amount)
    let dstBal ← getMapping balances dst
    setMapping balances dst (add dstBal amount)
    emit "Transfer" [src, dst, amount]
    return true

  function nonreentrant(lock) mint (recipient : Address) : Uint256 := do
    let t0 ← getStorageAddr token0
    let t1 ← getStorageAddr token1
    let me ← contractAddress
    let b0 ← balanceOf t0 me
    let b1 ← balanceOf t1 me
    require (b0 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    require (b1 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    let r0 ← getStorage reserve0
    let r1 ← getStorage reserve1
    require (b0 >= r0) "Pool: BALANCE_BELOW_RESERVE"
    require (b1 >= r1) "Pool: BALANCE_BELOW_RESERVE"
    let a0 := sub b0 r0
    let a1 := sub b1 r1
    let supply ← getStorage totalSupply
    let mut liquidity := 0
    if supply == 0 then
      let root ← isqrt (mul a0 a1)
      require (root > 1000) "Pool: INSUFFICIENT_INITIAL_LIQUIDITY"
      liquidity := sub root 1000
      let lockedBal ← getMapping balances zeroAddress
      setMapping balances zeroAddress (add lockedBal 1000)
      setStorage totalSupply 1000
    else
      let l0 := mulDiv512Down a0 supply r0
      let l1 := mulDiv512Down a1 supply r1
      liquidity := if l0 < l1 then l0 else l1
    require (liquidity > 0) "Pool: INSUFFICIENT_LIQUIDITY_MINTED"
    let supplyNow ← getStorage totalSupply
    setStorage totalSupply (add supplyNow liquidity)
    let toBal ← getMapping balances recipient
    setMapping balances recipient (add toBal liquidity)
    setStorage reserve0 b0
    setStorage reserve1 b1
    let sender ← msgSender
    emit "Mint" [sender, a0, a1, liquidity]
    emit "Sync" [b0, b1]
    return liquidity

  function nonreentrant(lock) burn (recipient : Address) : Tuple [Uint256, Uint256] := do
    let t0 ← getStorageAddr token0
    let t1 ← getStorageAddr token1
    let me ← contractAddress
    let b0 ← balanceOf t0 me
    let b1 ← balanceOf t1 me
    let liquidity ← getMapping balances me
    let supply ← getStorage totalSupply
    require (supply > 0) "Pool: NO_LIQUIDITY"
    let amount0 := mulDiv512Down liquidity b0 supply
    let amount1 := mulDiv512Down liquidity b1 supply
    require (amount0 > 0) "Pool: INSUFFICIENT_LIQUIDITY_BURNED"
    require (amount1 > 0) "Pool: INSUFFICIENT_LIQUIDITY_BURNED"
    setMapping balances me 0
    setStorage totalSupply (sub supply liquidity)
    safeTransfer t0 recipient amount0
    safeTransfer t1 recipient amount1
    let nb0 ← balanceOf t0 me
    let nb1 ← balanceOf t1 me
    -- Every reserve write keeps the 2^112 cap the swap k-check relies on.
    require (nb0 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    require (nb1 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    setStorage reserve0 nb0
    setStorage reserve1 nb1
    let sender ← msgSender
    emit "Burn" [sender, amount0, amount1, recipient]
    emit "Sync" [nb0, nb1]
    return (amount0, amount1)

  -- The part of `swap` after the payouts: measure what arrived, enforce the fee-adjusted
  -- k-check against the reserves read before the payouts, store the new reserves. One
  -- linear body, so the k property is proved on it directly. Only `swap` calls it, under
  -- the reentrancy lock, which is why post-interaction writes are allowed here.
  function internal allow_post_interaction_writes settle (r0 : Uint256, r1 : Uint256, out0 : Uint256, out1 : Uint256,
      t0 : Address, t1 : Address, recipient : Address) : Unit := do
    let me ← contractAddress
    let b0 ← balanceOf t0 me
    let b1 ← balanceOf t1 me
    require (b0 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    require (b1 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    let left0 := sub r0 out0
    let left1 := sub r1 out1
    let in0 := if b0 > left0 then sub b0 left0 else 0
    let in1 := if b1 > left1 then sub b1 left1 else 0
    require (in0 > 0 || in1 > 0) "Pool: INSUFFICIENT_INPUT_AMOUNT"
    -- k-check with the 0.3% fee on the input; all factors are below 2^122.
    let adj0 := sub (mul b0 1000) (mul in0 3)
    let adj1 := sub (mul b1 1000) (mul in1 3)
    require (mul adj0 adj1 >= mul (mul r0 r1) 1000000) "Pool: K"
    let sender ← msgSender
    emit "Swap" [sender, in0, in1, out0, out1, recipient]
    emit "Sync" [b0, b1]
    setStorage reserve0 b0
    setStorage reserve1 b1

  function nonreentrant(lock) swap (out0 : Uint256, out1 : Uint256, recipient : Address) : Unit := do
    require (out0 > 0 || out1 > 0) "Pool: INSUFFICIENT_OUTPUT_AMOUNT"
    let r0 ← getStorage reserve0
    let r1 ← getStorage reserve1
    require (out0 < r0) "Pool: INSUFFICIENT_LIQUIDITY"
    require (out1 < r1) "Pool: INSUFFICIENT_LIQUIDITY"
    let t0 ← getStorageAddr token0
    let t1 ← getStorageAddr token1
    require (recipient != t0) "Pool: INVALID_TO"
    require (recipient != t1) "Pool: INVALID_TO"
    if out0 > 0 then
      safeTransfer t0 recipient out0
    if out1 > 0 then
      safeTransfer t1 recipient out1
    settle r0 r1 out0 out1 t0 t1 recipient

  function nonreentrant(lock) sync () : Unit := do
    let t0 ← getStorageAddr token0
    let t1 ← getStorageAddr token1
    let me ← contractAddress
    let b0 ← balanceOf t0 me
    let b1 ← balanceOf t1 me
    require (b0 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    require (b1 < 5192296858534827628530496329220096) "Pool: OVERFLOW"
    setStorage reserve0 b0
    setStorage reserve1 b1
    emit "Sync" [b0, b1]

end Dex
