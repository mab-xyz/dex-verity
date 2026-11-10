import Dex.Factory
import Dex.SwapProofs

/-!
# Factory properties

Storage layout: poolCodeHash 0, pools (pair → pool word) 1, poolCount 2, allPools 3.
-/

namespace Dex.FactoryProofs

open Verity Contracts Dex
open Dex.ProofKit

/-- F3: a pool of a token with itself is rejected, without effect. -/
theorem createPool_reverts_identical (ctx : ExecutableCallContext) (token : Address)
    (initcode : ByteArray) (s : ContractState) :
    ∃ msg, Factory.createPool ctx token token initcode s = ContractResult.revert msg s := by
  unfold Factory.createPool Verity.Core.NonReentrantGuard.guarded
  by_cases hlock : s.transientStorage 4 = 0
  · simp [hlock, Verity.require, Verity.bind, Bind.bind, Contract.run]
  · simp [hlock]

/-- F1 + F4: if `createPool` succeeds, it returns a non-zero pool, records it for the pair
in both orders and at index `poolCount`, and increments `poolCount` by exactly one. -/
theorem createPool_registers (ctx : ExecutableCallContext) (tokenA tokenB : Address)
    (initcode : ByteArray) (s s' : ContractState) (v : Address)
    (h : Factory.createPool ctx tokenA tokenB initcode s = .success v s') :
    let t0 := if addressToWord tokenA < addressToWord tokenB then tokenA else tokenB
    let t1 := if addressToWord tokenA < addressToWord tokenB then tokenB else tokenA
    ∃ poolWord : Uint256, poolWord ≠ 0 ∧ v = wordToAddress poolWord ∧
      s'.storageMap2 1 t0 t1 = poolWord ∧ s'.storageMap2 1 t1 t0 = poolWord ∧
      s'.storage 2 = EVM.Uint256.add (s.storage 2) 1 := by
  intro t0 t1
  unfold Factory.createPool Verity.Core.NonReentrantGuard.guarded at h
  split at h
  · split at h
    · rename_i a s'' hbody
      injection h with ha hs'
      subst ha hs'
      replace hbody := Contract.eq_of_run_success hbody
      simp only [Bind.bind] at hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hne, hs1⟩ := require_success hq
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs2⟩ := require_success hq
      obtain ⟨_, _, hge, hbody⟩ := bind_success hbody
      simp only [getMapping2, Factory.pools] at hge
      injection hge with _ hsE
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨-, hs3⟩ := require_success hq
      obtain ⟨n, sN, hgn, hbody⟩ := bind_success hbody
      iterate 6 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨_, _, -, hbody⟩ := bind_success hbody
      obtain ⟨poolWord, _, -, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hq, hbody⟩ := bind_success hbody
      obtain ⟨hpw, -⟩ := require_success hq
      iterate 2 (obtain ⟨_, _, -, hbody⟩ := bind_success hbody)
      obtain ⟨_, _, hw1, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hw2, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hw3, hbody⟩ := bind_success hbody
      obtain ⟨_, _, hw4, hbody⟩ := bind_success hbody
      simp only [getStorage, Factory.poolCount] at hgn
      injection hgn with hn hsN
      simp only [setMapping2, setMappingUint, setStorage, Factory.pools, Factory.allPools,
        Factory.poolCount, Verity.pure, Pure.pure] at hw1 hw2 hw3 hw4 hbody
      injection hw1 with _ hw1
      injection hw2 with _ hw2
      injection hw3 with _ hw3
      injection hw4 with _ hw4
      injection hbody with hv hfin
      subst hw1 hw2 hw3 hw4 hfin
      -- `n` was read from the locked pre-state: only requires and reads ran before it
      have hn' : n = s.storage 2 := by
        rw [← hn, hs3, ← hsE, hs2, hs1]; rfl
      refine ⟨poolWord, by simpa using hpw, hv.symm, ?_, ?_, ?_⟩
      · have hab : tokenA ≠ tokenB := by simpa using hne
        have hdiff : t0 ≠ t1 := by
          simp only [t0, t1]; split <;> [exact hab; exact Ne.symm hab]
        have hdiff' : t1 ≠ t0 := Ne.symm hdiff
        simp only [t0, t1] at hdiff hdiff'
        simp [ContractState.storageMap2, ContractState.writeMap2, ContractState.writeSlot,
          ContractState.writeMapUint, Verity.Core.NonReentrantGuard.setLock,
          ContractState.writeTransient, t0, t1, hdiff, hdiff']
      · simp [ContractState.storageMap2, ContractState.writeMap2, ContractState.writeSlot,
          ContractState.writeMapUint, Verity.Core.NonReentrantGuard.setLock,
          ContractState.writeTransient, t0, t1]
      · rw [hn']
        simp [ContractState.storage, ContractState.writeSlot, Verity.Core.NonReentrantGuard.setLock,
          ContractState.writeTransient]
    · simp at h
  · simp at h

end Dex.FactoryProofs
