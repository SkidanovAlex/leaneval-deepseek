import Mathlib
import Submission.Work.Models.Port.BenderPairModels

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BST.sz_stdSol` — the standard solution in `Sz(2^(2n+1))`

The distinguished involution of the Suzuki 2-group relative to the Weyl element `w` is
`s₀ = u(0,1)` and the element `r₀ = u(1,0)` (whose inverse is `u(1,1)`) satisfies the
structure identity `w * s₀ * w = r₀⁻¹ * w * r₀`; moreover `(s₀ * w)⁵ = 1` and `s₀ * w ≠ 1`, so
`orderOf (s₀ * w) = 5`.

All entries of the matrices involved are `0` and `1` (the powers `1 ^ k`, `0 ^ k` for
`k = 2 ^ (n+1) ≥ 2` reduce to `1` and `0`), so the identities are characteristic independent
and are checked entrywise with `Matrix.mul_apply` and `Fin.sum_univ_four`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Matrix

namespace Work.PSU3.BST

/-- `u(0,1)` as a matrix. -/
private lemma szU_zero_one (n : ℕ) :
    Submission.Sz.szU n 0 1 = !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Sz.szU, zero_pow (show 2 ^ (n + 1) ≠ 0 by positivity),
      zero_pow (show 2 + 2 ^ (n + 1) ≠ 0 by positivity),
      zero_pow (show 1 + 2 ^ (n + 1) ≠ 0 by positivity)]

/-- `u(1,0)` as a matrix. -/
private lemma szU_one_zero (n : ℕ) :
    Submission.Sz.szU n 1 0 = !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Sz.szU, one_pow]

/-- `u(1,1)` as a matrix. -/
private lemma szU_one_one (n : ℕ) :
    Submission.Sz.szU n 1 1 = !![1, 1, 1, 1; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Sz.szU, one_pow, CharTwo.add_self_eq_zero]

/-- The structure identity at the matrix level:
`w * u(0,1) * w = u(1,1) * w * u(1,0)`, `w = szW`. -/
private lemma szW_conj_szU_zero_one (n : ℕ) :
    Submission.Sz.szW n * Submission.Sz.szU n 0 1 * Submission.Sz.szW n =
      Submission.Sz.szU n 1 1 * Submission.Sz.szW n * Submission.Sz.szU n 1 0 := by
  rw [szU_zero_one, szU_one_one, szU_one_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Sz.szW, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

/-- `(u(0,1) * w)⁵ = 1` at the matrix level. -/
private lemma szU_zero_one_mul_szW_pow_five (n : ℕ) :
    (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) = 1 := by
  rw [szU_zero_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Sz.szW, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero,
      Matrix.one_apply]

/-- `u(1,0) * u(1,1) = 1`. -/
private lemma szU_one_zero_mul_one_one (n : ℕ) :
    Submission.Sz.szU n 1 0 * Submission.Sz.szU n 1 1 = 1 := by
  rw [szU_one_zero, szU_one_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero, Matrix.one_apply]

/-- **The standard solution in `Sz(2^(2n+1))`**: `s₀ = u(0,1)`, `r₀ = u(1,0)` solve the
structure identity and `orderOf (s₀ * w) = 5`. -/
theorem sz_stdSol (n : ℕ) (hn : 1 ≤ n) :
    ∃ s₀ r₀ : LeanEval.GroupTheory.Defs.SzModel n,
      s₀ ∈ (Submission.Sz.szBenderPair n hn).U ∧ orderOf s₀ = 2 ∧
      r₀ ∈ (Submission.Sz.szBenderPair n hn).U ∧
      (Submission.Sz.szBenderPair n hn).w * s₀ * (Submission.Sz.szBenderPair n hn).w
        = r₀⁻¹ * (Submission.Sz.szBenderPair n hn).w * r₀ ∧
      orderOf (s₀ * (Submission.Sz.szBenderPair n hn).w) = 5 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- the three elements of the Suzuki 2-group, as elements of `SzModel n`
  set s₀ : LeanEval.GroupTheory.Defs.SzModel n := ⟨Submission.Sz.szUg n 0 1,
    Submission.Sz.szTwoGroup_le_szModel n ⟨0, 1, rfl⟩⟩ with hs₀
  set r₀ : LeanEval.GroupTheory.Defs.SzModel n := ⟨Submission.Sz.szUg n 1 0,
    Submission.Sz.szTwoGroup_le_szModel n ⟨1, 0, rfl⟩⟩ with hr₀
  set u₁₁ : LeanEval.GroupTheory.Defs.SzModel n := ⟨Submission.Sz.szUg n 1 1,
    Submission.Sz.szTwoGroup_le_szModel n ⟨1, 1, rfl⟩⟩ with hu₁₁
  have hs₀U : s₀ ∈ (Submission.Sz.szBenderPair n hn).U :=
    Subgroup.mem_subgroupOf.mpr ⟨0, 1, rfl⟩
  have hr₀U : r₀ ∈ (Submission.Sz.szBenderPair n hn).U :=
    Subgroup.mem_subgroupOf.mpr ⟨1, 0, rfl⟩
  -- `r₀⁻¹ = u(1,1)`
  have hr₀inv : r₀⁻¹ = u₁₁ := by
    apply Subtype.ext
    show (Submission.Sz.szUg n 1 0)⁻¹ = Submission.Sz.szUg n 1 1
    rw [← Submission.Sz.szUg_inv]
    norm_num
  -- the structure identity
  have hconj : (Submission.Sz.szBenderPair n hn).w * s₀ * (Submission.Sz.szBenderPair n hn).w
      = r₀⁻¹ * (Submission.Sz.szBenderPair n hn).w * r₀ := by
    rw [hr₀inv]
    apply Subtype.ext
    apply Units.ext
    show Submission.Sz.szW n * Submission.Sz.szU n 0 1 * Submission.Sz.szW n =
      Submission.Sz.szU n 1 1 * Submission.Sz.szW n * Submission.Sz.szU n 1 0
    exact szW_conj_szU_zero_one n
  -- `s₀² = 1`
  have hsq' : Submission.Sz.szUg n 0 1 * Submission.Sz.szUg n 0 1 = 1 := by
    simpa [pow_two] using Submission.Sz.szUg_zero_one_sq n
  have hsq : s₀ ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    show Submission.Sz.szUg n 0 1 * Submission.Sz.szUg n 0 1 = 1
    exact hsq'
  have hs₀ne : s₀ ≠ 1 := by
    intro h
    have h1 : Submission.Sz.szUg n 0 1 = 1 := by
      have hh := congrArg (fun z : LeanEval.GroupTheory.Defs.SzModel n =>
        (z : GL (Fin 4) (Submission.Sz.SzField n))) h
      simpa [hs₀] using hh
    have h2 : ((0 : Submission.Sz.SzField n), (1 : Submission.Sz.SzField n)) =
        ((0 : Submission.Sz.SzField n), (0 : Submission.Sz.SzField n)) :=
      Submission.Sz.szUg_injective n (by simpa using h1.trans (Submission.Sz.szUg_zero n).symm)
    exact one_ne_zero (Prod.ext_iff.mp h2).2
  -- `(s₀ * w)⁵ = 1`
  have hpow : (s₀ * (Submission.Sz.szBenderPair n hn).w) *
      (s₀ * (Submission.Sz.szBenderPair n hn).w) *
      (s₀ * (Submission.Sz.szBenderPair n hn).w) *
      (s₀ * (Submission.Sz.szBenderPair n hn).w) *
      (s₀ * (Submission.Sz.szBenderPair n hn).w) = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) *
        (Submission.Sz.szU n 0 1 * Submission.Sz.szW n) = 1
    exact szU_zero_one_mul_szW_pow_five n
  have hprod_ne : s₀ * (Submission.Sz.szBenderPair n hn).w ≠ 1 := by
    intro h1
    refine Submission.Sz.szWgM_notMem_szBorelS n ?_
    have h1' : s₀ * Submission.Sz.szWgM n = 1 := h1
    have h2 : Submission.Sz.szWgM n = s₀⁻¹ := by
      calc Submission.Sz.szWgM n = 1 * Submission.Sz.szWgM n := (one_mul _).symm
        _ = (s₀⁻¹ * s₀) * Submission.Sz.szWgM n := by rw [inv_mul_cancel]
        _ = s₀⁻¹ * (s₀ * Submission.Sz.szWgM n) := by rw [mul_assoc]
        _ = s₀⁻¹ * 1 := by rw [h1']
        _ = s₀⁻¹ := mul_one _
    rw [h2]
    exact Submission.Sz.szTwoGroupS_le_szBorelS n (Subgroup.inv_mem _ hs₀U)
  refine ⟨s₀, r₀, hs₀U, orderOf_eq_prime (by simpa [pow_two] using hsq) hs₀ne, hr₀U, hconj, ?_⟩
  have h5 : (s₀ * (Submission.Sz.szBenderPair n hn).w) ^ 5 = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hpow
  exact orderOf_eq_prime h5 hprod_ne

end Work.PSU3.BST
