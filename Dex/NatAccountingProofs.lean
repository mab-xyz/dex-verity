import Dex.BurnRegistryProofs

/-! Natural-number LP accounting. Headroom and balance bounds are explicit obligations,
not consequences of the existing reserve cap. The iff theorems characterize precisely
when the modular implementation also satisfies ordinary integer accounting. -/
open Verity Contracts Dex
open Compiler.CompilationModel.DenoteExternalCalls

namespace Dex.NatAccounting

/-- Supply before the final mint addition, including the initial locked allocation. -/
def mintBase (s : ContractState) : Uint256 :=
  if s.storage 5 = 0 then 1000 else s.storage 5

theorem add_exact_iff (a b : Uint256) :
    (EVM.Uint256.add a b).val = a.val + b.val ↔
      a.val + b.val < Core.Uint256.modulus := by
  constructor
  · intro h
    rw [← h]
    exact (EVM.Uint256.add a b).isLt
  · exact Core.Uint256.addNoWrap

theorem sub_exact_iff (a b : Uint256) :
    (EVM.Uint256.sub a b).val + b.val = a.val ↔ b.val ≤ a.val := by
  constructor
  · omega
  · intro h
    have he := Core.Uint256.sub_eq_of_le h
    change (EVM.Uint256.sub a b).val = a.val - b.val at he
    rw [he]
    exact Nat.sub_add_cancel h

/-- Exact supply growth holds iff the final addition has room. No headroom is assumed. -/
theorem mint_supply_exact_iff (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (hr : recipient ≠ zeroAddress)
    (h : Pool.mint ctx recipient s = .success v s') :
    ((s'.storage 5).val = (mintBase s).val + v.val ↔
      (mintBase s).val + v.val < Core.Uint256.modulus) := by
  obtain ⟨_, _, _, hfirst, hlater⟩ := mint_lp_accounting ctx recipient s s' v hr h
  have hs : s'.storage 5 = EVM.Uint256.add (mintBase s) v := by
    by_cases hz : s.storage 5 = 0
    · simpa [mintBase, hz] using (hfirst hz).1
    · simpa [mintBase, hz] using (hlater hz).1
  rw [hs]
  exact add_exact_iff _ _

/-- Exact supply decrease holds iff the burned shares do not exceed supply.
Callbacks are still restricted to the pool's registered entrypoints. -/
theorem burn_supply_exact_iff (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (hb : CallbackBounded Pool.entrypointRegistry ctx.adversary)
    (h : Pool.burn ctx recipient s = .success v s') :
    ((s'.storage 5).val + (s.storageMap 6 s.thisAddress).val = (s.storage 5).val ↔
      (s.storageMap 6 s.thisAddress).val ≤ (s.storage 5).val) := by
  rw [BurnRegistry.burn_supply_drops_by_burned ctx recipient s s' v hb h]
  exact sub_exact_iff _ _

/-- Natural-number mint accounting under explicit supply headroom and pre-state holder
bounds. These hypotheses must be established by a separate reachable-state invariant. -/
theorem mint_lp_accounting_nat (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256) (hr : recipient ≠ zeroAddress)
    (h : Pool.mint ctx recipient s = .success v s')
    (hcap : (mintBase s).val + v.val < Core.Uint256.modulus)
    (hholders : ∀ a, (s.storageMap 6 a).val ≤ (s.storage 5).val) :
    0 < v.val ∧
      (s'.storageMap 6 recipient).val = (s.storageMap 6 recipient).val + v.val ∧
      (s'.storage 5).val = (s.storage 5).val + v.val +
        (if s.storage 5 = 0 then 1000 else 0) ∧
      (s'.storageMap 6 zeroAddress).val = (s.storageMap 6 zeroAddress).val +
        (if s.storage 5 = 0 then 1000 else 0) ∧
      (∀ a, a ≠ recipient → a ≠ zeroAddress → s'.storageMap 6 a = s.storageMap 6 a) := by
  obtain ⟨hv, hrec, hother, hfirst, hlater⟩ := mint_lp_accounting ctx recipient s s' v hr h
  have hbase : (s.storage 5).val ≤ (mintBase s).val := by
    by_cases hz : s.storage 5 = 0 <;> simp [mintBase, hz]
  have hrecCap : (s.storageMap 6 recipient).val + v.val < Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.add_le_add_right (le_trans (hholders recipient) hbase) _) hcap
  have hsup := (mint_supply_exact_iff ctx recipient s s' v hr h).2 hcap
  refine ⟨hv, ?_, ?_, ?_, hother⟩
  · rw [hrec]
    exact (add_exact_iff _ _).2 hrecCap
  · by_cases hz : s.storage 5 = 0
    · simpa [mintBase, hz, Nat.add_comm, show (1000 : Uint256).val = 1000 from rfl] using hsup
    · simpa [mintBase, hz] using hsup
  · by_cases hz : s.storage 5 = 0
    · have hzero : (s.storageMap 6 zeroAddress).val = 0 := by
        have := hholders zeroAddress
        simp [hz] at this
        exact this
      rw [(hfirst hz).2]
      have hzeroCap : (s.storageMap 6 zeroAddress).val + (1000 : Uint256).val <
          Core.Uint256.modulus := by rw [hzero]; decide
      rw [(add_exact_iff _ _).2 hzeroCap]
      simp [hz]
      rfl
    · rw [(hlater hz).2]
      simp [hz]

/-- A pre-state holder bound is sufficient for a genuine integer decrease. -/
theorem burn_supply_drops_nat (ctx : ExecutableCallContext) (recipient : Address)
    (s s' : ContractState) (v : Uint256 × Uint256)
    (hb : CallbackBounded Pool.entrypointRegistry ctx.adversary)
    (h : Pool.burn ctx recipient s = .success v s')
    (hle : (s.storageMap 6 s.thisAddress).val ≤ (s.storage 5).val) :
    (s'.storage 5).val + (s.storageMap 6 s.thisAddress).val = (s.storage 5).val :=
  (burn_supply_exact_iff ctx recipient s s' v hb h).2 hle

end Dex.NatAccounting
