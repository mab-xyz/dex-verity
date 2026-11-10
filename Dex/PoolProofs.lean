import Dex.Pool
import Verity.Proofs.Stdlib.Automation

/-!
# Pool properties

Properties of `Dex.Pool` over Verity's EDSL semantics (the same code the compiler lowers to
the EVM bytecode tested in `test/`). Storage layout: factory 0, token0 1, token1 2,
reserve0 3, reserve1 4, totalSupply 5, balances 6, allowances 7, initialized 8, lock 9.
-/

namespace Dex.PoolProofs

open Verity
open Contracts
open Dex
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne)

/-- L1a: only the factory can initialise the pool. -/
theorem initPool_reverts_when_not_factory (s : ContractState) (t0 t1 : Address)
    (h : s.sender ≠ s.storageAddr 0) :
    ∃ msg, (Pool.initPool t0 t1).run s = ContractResult.revert msg s := by
  simp only [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.run]
  simp [address_beq_false_of_ne s.sender (s.storageAddr 0) h, ContractState.readAddrSlot]

/-- L1b: the pool can be initialised only once. -/
theorem initPool_reverts_when_initialized (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 ≠ 0) :
    ∃ msg, (Pool.initPool t0 t1).run s = ContractResult.revert msg s := by
  simp only [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.run]
  simp [hf, hi, ContractState.readAddrSlot, ContractState.readSlot]

/-- L1c: the first initialisation by the factory succeeds… -/
theorem initPool_succeeds (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 = 0) :
    (Pool.initPool t0 t1).run s =
      ContractResult.success () ((Pool.initPool t0 t1).runState s) := by
  simp [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.run, Contract.runState,
    hf, hi, ContractState.readAddrSlot, ContractState.readSlot]

/-- …records both tokens… -/
theorem initPool_records_tokens (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 = 0) :
    ((Pool.initPool t0 t1).runState s).storageAddr 1 = t0 ∧
      ((Pool.initPool t0 t1).runState s).storageAddr 2 = t1 := by
  simp [Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.runState,
    hf, hi, ContractState.readAddrSlot, ContractState.readSlot,
    ContractState.writeAddrSlot, ContractState.writeSlot, ContractState.storageAddr]

/-- …and marks the pool initialised, so every later `initPool` reverts (L1b). -/
theorem initPool_marks_initialized (s : ContractState) (t0 t1 : Address)
    (hf : s.sender = s.storageAddr 0) (hi : s.storage 8 = 0) :
    ((Pool.initPool t0 t1).runState s).storage 8 ≠ 0 := by
  have hi' : s.storageWords (StorageKey.slot 8) = 0 := hi
  simp [hi', Pool.initPool, Pool.factory, Pool.initialized, Pool.token0, Pool.token1,
    msgSender, getStorageAddr, getStorage, setStorage, setStorageAddr,
    Verity.require, Verity.bind, Bind.bind, Contract.runState,
    hf, ContractState.readAddrSlot, ContractState.readSlot,
    ContractState.writeAddrSlot, ContractState.writeSlot, ContractState.storage]
  decide

end Dex.PoolProofs
