import Contracts.Common
import Compiler.Modules.Create2SSTORE2
import Dex.Router

namespace Dex

open Contracts
open Verity hiding pure bind contractAddress blockTimestamp
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def selInitPool : Nat := Compiler.keccak256_first_4_bytes "initPool(address,address)"

/-!
# Factory

Deploys one pool per unordered token pair with CREATE2 and records it. The pool's
creation code is passed in the call and must hash to `poolCodeHash`, fixed at
construction; the salt is `keccak256(abi.encode(token0, token1))`, so the pool address is
`CREATE2(factory, salt, poolCodeHash)` for the sorted pair.

Memory: the salt preimage uses the scratch words 0 and 32; the creation code is copied to
0x2000, above the compiler's stack-spill slots (see the comment in `createPool`).
-/
verity_contract Factory where
  storage
    poolCodeHash : Uint256 := slot 0
    pools : Address → Address → Uint256 := slot 1
    poolCount : Uint256 := slot 2
    allPools : Uint256 → Uint256 := slot 3
    lock : Uint256 := slot 4

  event_defs
    event PoolCreated(@indexed token0 : Address, @indexed token1 : Address, pool : Address, index : Uint256)

  constructor (codeHash : Uint256) := do
    setStorage poolCodeHash codeHash

  function getPool (tokenA : Address, tokenB : Address) : Address := do
    let poolWord ← getMapping2 pools tokenA tokenB
    return wordToAddress poolWord

  function allPoolsLength () : Uint256 := do
    let n ← getStorage poolCount
    return n

  function poolAt (index : Uint256) : Address := do
    let poolWord ← getMappingUint allPools index
    return wordToAddress poolWord

  function nonreentrant(lock) createPool (tokenA : Address, tokenB : Address, initcode : Bytes) : Address := do
    require (tokenA != tokenB) "Factory: IDENTICAL_ADDRESSES"
    let aIsToken0 := addressToWord tokenA < addressToWord tokenB
    let t0 := if aIsToken0 then tokenA else tokenB
    let t1 := if aIsToken0 then tokenB else tokenA
    require (t0 != zeroAddress) "Factory: ZERO_ADDRESS"
    let existing ← getMapping2 pools t0 t1
    require (existing == 0) "Factory: POOL_EXISTS"
    -- Read before any external call, so the new index is the pre-call count.
    let n ← getStorage poolCount
    unsafe "abi.encode(token0, token1) in scratch memory, for the CREATE2 salt" do
      mstore 0 (addressToWord t0)
      mstore 32 (addressToWord t1)
    let salt := keccak256 0 64
    -- The creation code (several KB) goes to 0x2000: above the compiler's stack-spill slots
    -- (from 0x1000; a copy at 0x80 would overwrite them), and nothing is allocated from the
    -- free-memory pointer before CREATE2 consumes it. Reading the free pointer instead needs
    -- `mload` outside `unsafe`, which Verity admits only with an assumed local obligation.
    let ptr := 8192
    unsafe "copy the pool creation code to free memory to hash and deploy it" do
      copyBytes initcode ptr
    let size := bytesLength initcode
    let codeHash := keccak256 ptr size
    let expected ← getStorage poolCodeHash
    require (codeHash == expected) "Factory: WRONG_INITCODE"
    let zero := 0
    let poolWord ← ecmCall Compiler.Modules.Create2SSTORE2.deployModule [zero, ptr, size, salt]
    require (poolWord != 0) "Factory: CREATE2_FAILED"
    ecmDo (Compiler.Modules.Calls.noReturnModule selInitPool 2 false)
      [poolWord, addressToWord t0, addressToWord t1]
    emit "PoolCreated" [t0, t1, wordToAddress poolWord, n]
    setMapping2 pools t0 t1 poolWord
    setMapping2 pools t1 t0 poolWord
    setMappingUint allPools n poolWord
    setStorage poolCount (add n 1)
    return wordToAddress poolWord

end Dex
