import Dex.LiquidityProofs

/-!
# P1: the pool's `isqrt` is the floor square root

`Pool.isqrt n` runs a Babylonian iteration for 256 rounds, then checks the result. For
`n < 2^255` it always succeeds and returns `Nat.sqrt n`, so `r² ≤ n < (r+1)²` and the
runtime checks never revert (the pool calls it with `n < 2^224`).

Why 256 rounds suffice, with `s = Nat.sqrt n`: every Babylonian step lands at or above `s`
(integer AM-GM, `sqrt_le_next`); above `s` it halves the distance to `s`
(`next_sub_le_half`). The first round moves to `n/2 + 1 < 2^255`, and 255 halvings bring
the distance to 0; at `s` the iteration is stable.
-/

namespace Dex.Isqrt

/-- One Babylonian step from guess `x`. -/
def next (n x : Nat) : Nat := (n / x + x) / 2

/-- One round of the contract's loop on `(z, x)`: take `x` if it improves on `z`. -/
def bstep (n : Nat) (p : Nat × Nat) : Nat × Nat :=
  if p.2 < p.1 then (p.2, next n p.2) else p

/-- Integer AM-GM: a step never lands below the floor square root. -/
theorem sqrt_le_next (n x : Nat) (hx : 0 < x) : Nat.sqrt n ≤ next n x := by
  unfold next
  by_contra hlt
  push Not at hlt
  have hs := Nat.sqrt_le' n
  have hq : n < (n / x + 1) * x := by
    have := Nat.lt_div_mul_add (a := n) hx
    nlinarith [Nat.div_add_mod n x, Nat.mod_lt n hx]
  have h2 : n / x + 1 + x ≤ 2 * Nat.sqrt n := by omega
  have h3 : (n / x + 1 + x) * (n / x + 1 + x) ≤ (2 * Nat.sqrt n) * (2 * Nat.sqrt n) :=
    Nat.mul_le_mul h2 h2
  have key : (4 : Int) * (n / x + 1) * x ≤ ((n / x + 1 : Int) + x) * ((n / x + 1 : Int) + x) := by
    nlinarith [sq_nonneg ((n / x + 1 : Int) - x)]
  zify at hq h3 hs
  nlinarith

/-- Above the root a step strictly decreases and halves the distance to the root. -/
theorem next_sub_le_half (n x : Nat) (hx : Nat.sqrt n < x) :
    next n x < x ∧ next n x - Nat.sqrt n ≤ (x - Nat.sqrt n) / 2 := by
  have hlt := Nat.lt_succ_sqrt' n
  have hq : n / x ≤ Nat.sqrt n := by
    have : n / x < Nat.sqrt n + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ (Nat.sqrt n + 1) * x :=
        Nat.mul_le_mul_left _ hx
      rw [Nat.succ_eq_add_one, pow_two] at hlt
      omega
    omega
  unfold next
  omega

/-- After the first round: `z` at or above the root, `x` the step from `z`. -/
def Good (n : Nat) (p : Nat × Nat) : Prop :=
  Nat.sqrt n ≤ p.1 ∧ p.2 = next n p.1 ∧ 0 < p.1

/-- A round keeps `Good` and halves the distance of `z` to the root. -/
theorem bstep_good (n : Nat) (p : Nat × Nat) (hs : 0 < Nat.sqrt n) (h : Good n p) :
    Good n (bstep n p) ∧ (bstep n p).1 - Nat.sqrt n ≤ (p.1 - Nat.sqrt n) / 2 := by
  obtain ⟨hz, hx, hpos⟩ := h
  by_cases hgt : Nat.sqrt n < p.1
  · obtain ⟨hlt, hhalf⟩ := next_sub_le_half n p.1 hgt
    have hstep : bstep n p = (p.2, next n p.2) := by
      unfold bstep; rw [if_pos (by omega)]
    rw [hstep]
    have hle := sqrt_le_next n p.1 hpos
    refine ⟨⟨by simp only; omega, rfl, by simp only; omega⟩, by simp only; omega⟩
  · have heq : p.1 = Nat.sqrt n := by omega
    have hle := sqrt_le_next n p.1 hpos
    have hstep : bstep n p = p := by
      unfold bstep; rw [if_neg (by omega)]
    rw [hstep]
    exact ⟨⟨hz, hx, hpos⟩, by omega⟩

/-- `k` rounds from a `Good` state divide the distance to the root by `2^k`. -/
theorem iterate_good (n : Nat) (hs : 0 < Nat.sqrt n) (k : Nat) :
    ∀ p, Good n p → Good n ((bstep n)^[k] p) ∧
      ((bstep n)^[k] p).1 - Nat.sqrt n ≤ (p.1 - Nat.sqrt n) / 2 ^ k := by
  induction k with
  | zero => intro p h; exact ⟨h, by simp⟩
  | succ k ih =>
    intro p h
    obtain ⟨hg, hd⟩ := bstep_good n p hs h
    obtain ⟨hg', hd'⟩ := ih _ hg
    rw [Function.iterate_succ_apply]
    refine ⟨hg', le_trans hd' ?_⟩
    rw [pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right hd

/-- 256 rounds from the contract's start `(n, n/2 + 1)` reach the floor square root. -/
theorem converge (n : Nat) (h3 : 3 < n) (hn : n < 2 ^ 255) :
    ((bstep n)^[256] (n, n / 2 + 1)).1 = Nat.sqrt n := by
  have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsq := Nat.sqrt_le' n
  have hs1 : Nat.sqrt n ≤ n / 2 + 1 := by
    by_contra hc; push Not at hc
    have : (n / 2 + 2) * (n / 2 + 2) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hc hc
    have hm : n ≤ 2 * (n / 2) + 1 := by omega
    nlinarith
  have hfirst : bstep n (n, n / 2 + 1) = (n / 2 + 1, next n (n / 2 + 1)) := by
    unfold bstep; rw [if_pos (show n / 2 + 1 < n by omega)]
  rw [Function.iterate_succ_apply, hfirst]
  obtain ⟨⟨hge, -, -⟩, hd⟩ := iterate_good n (by omega) 255 (n / 2 + 1, next n (n / 2 + 1))
    ⟨hs1, rfl, Nat.succ_pos _⟩
  have hzero : (n / 2 + 1 - Nat.sqrt n) / 2 ^ 255 = 0 :=
    Nat.div_eq_of_lt (by omega)
  omega

/-- Every guess stays in `[1, n]`, so the contract's word arithmetic never wraps. -/
def Bnd (n : Nat) (p : Nat × Nat) : Prop := p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ n

theorem bstep_bnd (n : Nat) (h3 : 3 < n) (p : Nat × Nat) (h : Bnd n p) : Bnd n (bstep n p) := by
  obtain ⟨h1, h2, h2'⟩ := h
  unfold bstep
  split
  · have hle := sqrt_le_next n p.2 (by omega)
    have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
    have hdiv : n / p.2 ≤ n := Nat.div_le_self n p.2
    refine ⟨h2', by omega, ?_⟩
    show (n / p.2 + p.2) / 2 ≤ n
    omega
  · exact ⟨h1, h2, h2'⟩

open Verity in
/-- One round of the contract's loop, on words. -/
def ustep (n : Uint256) (p : Uint256 × Uint256) : Uint256 × Uint256 :=
  if p.2 < p.1 then (p.2, EVM.Uint256.div (EVM.Uint256.add (EVM.Uint256.div n p.2) p.2) 2)
  else p

open Verity in
/-- The word values of a pair. -/
def vals (p : Uint256 × Uint256) : Nat × Nat := (p.1.val, p.2.val)

open Verity in
theorem ustep_vals (n : Uint256) (hn : n.val < 2 ^ 255) (p : Uint256 × Uint256)
    (h : Bnd n.val (vals p)) : vals (ustep n p) = bstep n.val (vals p) := by
  obtain ⟨-, h2, h2'⟩ := h
  simp only [vals] at h2 h2'
  unfold ustep bstep vals
  by_cases hlt : p.2 < p.1
  · have hlt' : p.2.val < p.1.val := hlt
    rw [if_pos hlt, if_pos hlt']
    have hdiv : n.val / p.2.val ≤ n.val := Nat.div_le_self _ _
    have hm : Core.Uint256.modulus = 2 ^ 256 := rfl
    have h2v : (2 : Core.Uint256).val = 2 := rfl
    have hx0 : p.2.val ≠ 0 := by omega
    simp only [EVM.Uint256.div, EVM.Uint256.add, Core.Uint256.div, Core.Uint256.add,
      Core.Uint256.val_ofNat, hm, next, hx0, h2v, if_false, OfNat.ofNat_ne_zero]
    rw [Nat.mod_eq_of_lt (a := n.val / p.2.val) (by omega),
      Nat.mod_eq_of_lt (a := n.val / p.2.val + p.2.val) (by omega),
      Nat.mod_eq_of_lt (a := (n.val / p.2.val + p.2.val) / 2) (by omega)]
  · have hlt' : ¬ p.2.val < p.1.val := hlt
    rw [if_neg hlt, if_neg hlt']

open Verity in
theorem iterate_vals (n : Uint256) (hn : n.val < 2 ^ 255) (h3 : 3 < n.val) (k : Nat) :
    ∀ p, Bnd n.val (vals p) →
      vals ((ustep n)^[k] p) = (bstep n.val)^[k] (vals p) := by
  induction k with
  | zero => intro p _; rfl
  | succ k ih =>
    intro p h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ustep_vals n hn p h]
    apply ih
    rw [ustep_vals n hn p h]
    exact bstep_bnd _ h3 _ h

open Verity in
/-- A loop whose body only computes `f` returns the `k`-th iterate and keeps the state. -/
theorem loopList_pure {σ : Type} (f : σ → σ) (body : Nat → σ → Contract σ)
    (hb : ∀ i a, body i a = (Pure.pure (f a) : Contract σ)) (l : List Nat) :
    ∀ (init : σ) (s : ContractState),
      Contracts.loopList l init body s = .success (f^[l.length] init) s := by
  induction l with
  | nil => intro init s; rfl
  | cons x xs ih =>
    intro init s
    have := ih (f init) s
    simp only [Contracts.loopList, List.foldlM] at this ⊢
    show Verity.bind (body x init) _ s = _
    rw [hb]
    simp only [Verity.bind, List.length_cons, Function.iterate_succ_apply]
    exact this

open Verity in
/-- P1: for `n < 2^255`, `Pool.isqrt n` succeeds, leaves the state unchanged and returns the
floor square root, so `r * r ≤ n < (r + 1) * (r + 1)`. -/
theorem isqrt_eq_sqrt (n : Uint256) (hn : n.val < 2 ^ 255) (s : ContractState) :
    Pool.isqrt n s = .success (Core.Uint256.ofNat (Nat.sqrt n.val)) s := by
  by_cases h3 : n > 3
  · have h3' : 3 < n.val := h3
    unfold Pool.isqrt
    rw [if_pos h3]
    dsimp only
    simp only [Bind.bind, Verity.bind]
    rw [loopList_pure (ustep n) _ ?hb]
    · have hlen : (List.range (Core.Uint256.val 256)).length = 256 := by simp; rfl
      rw [hlen]
      have hm : Core.Uint256.modulus = 2 ^ 256 := rfl
      have hinit : vals (n, EVM.Uint256.add (EVM.Uint256.div n 2) 1) = (n.val, n.val / 2 + 1) := by
        have h2v : (2 : Core.Uint256).val = 2 := rfl
        simp only [vals, EVM.Uint256.add, EVM.Uint256.div, Core.Uint256.add, Core.Uint256.div,
          Core.Uint256.val_ofNat, hm, h2v, OfNat.ofNat_ne_zero, if_false]
        have h1v : (1 : Core.Uint256).val = 1 := rfl
        rw [h1v, Nat.mod_eq_of_lt (a := n.val / 2) (by omega),
          Nat.mod_eq_of_lt (a := n.val / 2 + 1) (by omega)]
      have hbnd : Bnd n.val (vals (n, EVM.Uint256.add (EVM.Uint256.div n 2) 1)) := by
        rw [hinit]; exact ⟨le_refl _, by omega, by omega⟩
      have hv := iterate_vals n hn h3' 256 _ hbnd
      rw [hinit] at hv
      have hz : ((ustep n)^[256] (n, EVM.Uint256.add (EVM.Uint256.div n 2) 1)).1.val =
          Nat.sqrt n.val := by
        have := congrArg Prod.fst hv
        simp only [vals] at this
        rw [this]; exact converge _ h3' hn
      generalize (ustep n)^[256] (n, EVM.Uint256.add (EVM.Uint256.div n 2) 1) = r at hz ⊢
      have hsq := Nat.sqrt_le' n.val
      have hlt := Nat.lt_succ_sqrt' n.val
      rw [pow_two] at hsq
      rw [Nat.succ_eq_add_one, pow_two] at hlt
      have hsle : Nat.sqrt n.val ≤ n.val := Nat.sqrt_le_self _
      have hexp : (Nat.sqrt n.val + 1) * (Nat.sqrt n.val + 1) =
          Nat.sqrt n.val * Nat.sqrt n.val + 2 * Nat.sqrt n.val + 1 := by ring
      have hmul : (EVM.Uint256.mul r.1 r.1).val = Nat.sqrt n.val * Nat.sqrt n.val := by
        simp only [EVM.Uint256.mul, Core.Uint256.mul, Core.Uint256.val_ofNat, hm, hz]
        exact Nat.mod_eq_of_lt (by omega)
      have hc1 : decide (EVM.Uint256.mul r.1 r.1 ≤ n) = true := by
        apply decide_eq_true; show (EVM.Uint256.mul r.1 r.1).val ≤ n.val; omega
      have hc2 : decide (EVM.Uint256.sub n (EVM.Uint256.mul r.1 r.1) ≤
          EVM.Uint256.mul 2 r.1) = true := by
        apply decide_eq_true
        show (EVM.Uint256.sub n (EVM.Uint256.mul r.1 r.1)).val ≤ (EVM.Uint256.mul 2 r.1).val
        have h2v : (2 : Core.Uint256).val = 2 := rfl
        have hsub : (EVM.Uint256.sub n (EVM.Uint256.mul r.1 r.1)).val =
            n.val - Nat.sqrt n.val * Nat.sqrt n.val := by
          rw [← hmul]; exact Core.Uint256.subNoWrap (by rw [hmul]; exact hsq)
        have hm2 : (EVM.Uint256.mul 2 r.1).val = 2 * Nat.sqrt n.val := by
          simp only [EVM.Uint256.mul, Core.Uint256.mul, Core.Uint256.val_ofNat, hm, hz, h2v]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hsub, hm2]; omega
      have hr1 : r.1 = Core.Uint256.ofNat (Nat.sqrt n.val) := by
        apply Core.Uint256.ext
        rw [hz, Core.Uint256.val_ofNat, hm, Nat.mod_eq_of_lt (by omega)]
      simp only [Verity.require, hc1, hc2, if_true, Pure.pure, Verity.pure]
      rw [hr1]
    · intro i a
      funext t
      unfold ustep
      split <;> rfl
  · have hle : n.val ≤ 3 := Nat.le_of_not_lt h3
    have hn : n = Core.Uint256.ofNat n.val := by
      apply Core.Uint256.ext
      rw [Core.Uint256.val_ofNat]; exact (Nat.mod_eq_of_lt n.isLt).symm
    generalize hk : n.val = k at hle hn
    rw [hn]
    have hs : ∀ m, m * m ≤ k → k < (m + 1) * (m + 1) → Nat.sqrt k = m :=
      fun m h1 h2 => (Nat.eq_sqrt.mpr ⟨h1, h2⟩).symm
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [hs 0 (by decide) (by decide)]; rfl
    · rw [hs 1 (by decide) (by decide)]; rfl
    · rw [hs 1 (by decide) (by decide)]; rfl
    · rw [hs 1 (by decide) (by decide)]; rfl

open Verity in
/-- P1: the pool's integer square root is exact: `r² ≤ n < (r + 1)²`, and it never reverts
(for `n < 2^255`; the pool calls it with `n < 2^224`). -/
theorem isqrt_floor (n : Uint256) (hn : n.val < 2 ^ 255) (s : ContractState) :
    ∃ r : Uint256, Pool.isqrt n s = .success r s ∧
      r.val * r.val ≤ n.val ∧ n.val < (r.val + 1) * (r.val + 1) := by
  refine ⟨_, isqrt_eq_sqrt n hn s, ?_⟩
  have hlt : Nat.sqrt n.val < 2 ^ 256 := lt_of_le_of_lt (Nat.sqrt_le_self _) (by omega)
  rw [Core.Uint256.val_ofNat, show Core.Uint256.modulus = 2 ^ 256 from rfl,
    Nat.mod_eq_of_lt hlt]
  exact ⟨Nat.sqrt_le n.val, Nat.lt_succ_sqrt n.val⟩

end Dex.Isqrt
