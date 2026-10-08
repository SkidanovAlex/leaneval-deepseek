import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.involutions_B` — the involutions of the standard Borel of `SL(2,F)`

For `F` a finite field of characteristic `2`, the standard Borel `B` of `SL(2,F)` is the
subgroup of upper triangular matrices.  The involutions in `B` are exactly the non-trivial
elements of the unipotent radical `U` (the upper unitriangular matrices):

`involutions B = {x ∈ U | x ≠ 1}`.

* `⊇` is immediate: `x = 1 + b E₀₁` with `b ≠ 0` satisfies `x * x = 1` (`unip_mul_self`) and
  `x ≠ 1`, so `orderOf x = 2`, and `U ≤ B`.
* `⊆`: let `x ∈ B` with `x * x = 1`.  Writing `x = !![a, b; 0, d]`, the `(0,0)`- and
  `(1,1)`-entries of `x * x = 1` read `a * a = 1` and `d * d = 1`; in characteristic `2` a
  field has no non-trivial square root of `1` (`mul_self_eq_one_charTwo`), so `a = d = 1` and
  `x = 1 + b E₀₁ ∈ U` — the determinant condition being automatic.

Besides the target, the file provides the reusable statements `mul_self_eq_one_charTwo` and
`mem_U_of_mem_B_sq_eq_one` below.
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- In a field of characteristic `2`, the only solution of `a * a = 1` is `a = 1`
(the two roots of `X² - 1` have fused into the double root `1`). -/
lemma mul_self_eq_one_charTwo {a : F} (h : a * a = 1) : a = 1 := by
  have h2 : a ^ 2 = 1 := by rw [pow_two]; exact h
  rcases sq_eq_one_iff.mp h2 with h1 | h1
  · exact h1
  · rwa [CharTwo.neg_eq] at h1

/-- An upper triangular element of `SL(2,F)` (`F` of characteristic `2`) whose square is `1`
is upper unitriangular, i.e. lies in `U`. -/
lemma mem_U_of_mem_B_sq_eq_one {x : SL2 F} (hB : x ∈ B (F := F)) (hx : x * x = 1) :
    x ∈ U (F := F) := by
  set M : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hM
  have h10 : M 1 0 = 0 := hB
  -- `x * x = 1` read in matrix entries
  have hMM : M * M = 1 := by
    have h := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) hx
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
    rw [hM]; exact h
  -- the two diagonal entries of `x` have square `1`, hence equal `1`
  have h00 : M 0 0 * M 0 0 = 1 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) hMM
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10] using h
  have h11 : M 1 1 * M 1 1 = 1 := by
    have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 1 1) hMM
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10] using h
  have ha : M 0 0 = 1 := mul_self_eq_one_charTwo h00
  have hd : M 1 1 = 1 := mul_self_eq_one_charTwo h11
  -- so `x` is exactly the unipotent matrix `1 + (M 0 1) E₀₁`
  have hMeq : M = !![1, M 0 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, h10]
  refine ⟨M 0 1, ?_⟩
  apply Subtype.ext
  rw [unip_coe, ← hM]
  exact hMeq

theorem involutions_B {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Submission.Blueprint.involutions
        ((Work.Models.PSL2.B (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F))
      = {x : Work.Models.SL2 F | x ∈ Work.Models.PSL2.U (F := F) ∧ x ≠ 1} := by
  ext x
  change (x ∈ (B (F := F) : Set (SL2 F)) ∧ orderOf x = 2) ↔ (x ∈ U (F := F) ∧ x ≠ 1)
  constructor
  · -- `x ∈ B` of order `2` is unipotent and non-trivial
    rintro ⟨hxB, hx2⟩
    have hxne : x ≠ 1 := by intro h; rw [h] at hx2; simp at hx2
    have hx2sq : x * x = 1 := by
      have h : x ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hx2]
      simpa [pow_two] using h
    exact ⟨mem_U_of_mem_B_sq_eq_one hxB hx2sq, hxne⟩
  · -- a non-trivial unipotent matrix is an involution of `B`
    rintro ⟨hxU, hxne⟩
    rw [mem_U_iff] at hxU
    obtain ⟨b, rfl⟩ := hxU
    refine ⟨U_le_B (F := F) ⟨b, rfl⟩, ?_⟩
    refine orderOf_eq_prime ?_ hxne
    simpa [pow_two] using unip_mul_self b

end Work.Models.PSL2
