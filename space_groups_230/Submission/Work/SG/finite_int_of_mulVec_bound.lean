import Mathlib
import Submission.Work.SG.realize_defs

/-!
# Finitely many integer vectors map into a bounded box

If `M` is an invertible real `3 × 3` matrix and `K : Fin 3 → ℝ` is nonnegative, then only
finitely many integer vectors `n` have `M n` lying in the box `∏ j, [-K j, K j]`.

The argument is elementary and quantitative.  Write `C i = ∑ j, |M⁻¹ i j| * K j`.  For any `n`
in the set, `n = intVec n` is recovered from `M *ᵥ intVec n` by multiplying by `M⁻¹`, so

`|n i| = |∑ j, M⁻¹ i j * (M *ᵥ intVec n) j| ≤ ∑ j, |M⁻¹ i j| * K j = C i`,

using the triangle inequality and the coordinatewise hypothesis.  Hence every coordinate `n i`
lies in the finite interval of integers `[-⌈C i⌉, ⌈C i⌉]`, and the set is contained in the
finite product of these intervals.  (Nonnegativity of `K` is not actually needed for this;
it is part of the requested statement and is kept.)
-/

namespace Work.SG

open Matrix

set_option linter.unusedVariables false in
theorem finite_int_of_mulVec_bound (M : Work.SG.RMat) (hM : M.det ≠ 0) (K : Fin 3 → ℝ)
    (hK : ∀ j, 0 ≤ K j) :
    {n : Fin 3 → ℤ | ∀ j, |(Matrix.mulVec M (Work.SG.intVec n)) j| ≤ K j}.Finite := by
  classical
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  -- Coordinatewise real bound `C`.
  set C : Fin 3 → ℝ := fun i => ∑ j, |M⁻¹ i j| * K j with hC
  -- Every element of the set has `|n i| ≤ C i`.
  have hbound : ∀ n : Fin 3 → ℤ,
      (∀ j, |(Matrix.mulVec M (intVec n)) j| ≤ K j) → ∀ i, |(n i : ℝ)| ≤ C i := by
    intro n hn i
    have hrec : (n i : ℝ) = ∑ j, M⁻¹ i j * (Matrix.mulVec M (intVec n)) j := by
      have h1 : intVec n = Matrix.mulVec M⁻¹ (Matrix.mulVec M (intVec n)) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec]
      have h2 := congrFun h1 i
      simpa [intVec, Matrix.mulVec, dotProduct] using h2
    rw [hrec]
    calc |∑ j, M⁻¹ i j * (Matrix.mulVec M (intVec n)) j|
        ≤ ∑ j, |M⁻¹ i j * (Matrix.mulVec M (intVec n)) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |M⁻¹ i j| * |(Matrix.mulVec M (intVec n)) j| := by
          apply Finset.sum_congr rfl; intro j _; rw [abs_mul]
      _ ≤ ∑ j, |M⁻¹ i j| * K j := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hn j) (abs_nonneg _)
      _ = C i := by rw [hC]
  -- Integer coordinates lie in a finite interval.
  have hsub : {n : Fin 3 → ℤ | ∀ j, |(Matrix.mulVec M (intVec n)) j| ≤ K j}
      ⊆ Set.pi Set.univ (fun i => Set.Icc (-(Int.ceil (C i))) (Int.ceil (C i))) := by
    intro n hn i _
    have hb := hbound n hn i
    have hceil : ((|n i| : ℤ) : ℝ) ≤ (Int.ceil (C i) : ℝ) := by
      rw [Int.cast_abs]
      exact le_trans hb (Int.le_ceil (C i))
    have hle : |n i| ≤ Int.ceil (C i) := Int.cast_le.mp hceil
    exact Set.mem_Icc.mpr (abs_le.mp hle)
  exact (Set.Finite.pi (fun i => Set.finite_Icc _ _)).subset hsub

end Work.SG
