import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
open scoped BigOperators

namespace Commons.Analysis.Fourier

/-- Squared coordinate norm of a matrix-vector product, bounded by the squared Frobenius
norm of the matrix times the squared coordinate norm of the vector
(Cauchy–Schwarz). -/
lemma sum_sq_mulVec_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (y : ι → ℝ) :
    (∑ i : ι, ((A.mulVec y) i) ^ 2) ≤
      (∑ i : ι, ∑ j : ι, (A i j) ^ 2) * (∑ k : ι, (y k) ^ 2) := by
  calc
    (∑ i : ι, ((A.mulVec y) i) ^ 2)
        = ∑ i : ι, (∑ j : ι, A i j * y j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
    _ ≤ ∑ i : ι, ((∑ j : ι, (A i j) ^ 2) * (∑ k : ι, (y k) ^ 2)) := by
            exact Finset.sum_le_sum (fun i hi => by
              simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
                (fun j => A i j) (fun j => y j))
    _ = (∑ i : ι, ∑ j : ι, (A i j) ^ 2) * (∑ k : ι, (y k) ^ 2) := by
            rw [Finset.sum_mul]

/-- For an invertible real matrix `C`, the squared coordinate norm of `x` is bounded by a
constant multiple of the squared coordinate norm of `C.mulVec x`. -/
theorem sum_sq_le_const_sum_sq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.det ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : ι → ℝ,
      (∑ i : ι, (x i) ^ 2) ≤ a * (∑ i : ι, ((C.mulVec x) i) ^ 2) := by
  classical
  let A : Matrix ι ι ℝ := C⁻¹
  let b : ℝ := ∑ i : ι, ∑ j : ι, (A i j) ^ 2
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg (A i j)))
  refine ⟨b + 1, by nlinarith, ?_⟩
  intro x
  have hxinv : A.mulVec (C.mulVec x) = x := by
    dsimp [A]
    calc
      (C⁻¹).mulVec (C.mulVec x) = (C⁻¹ * C).mulVec x := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix ι ι ℝ).mulVec x := by
        rw [Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC)]
      _ = x := Matrix.one_mulVec x
  have hbd : (∑ i : ι, ((A.mulVec (C.mulVec x)) i) ^ 2) ≤
      b * (∑ i : ι, ((C.mulVec x) i) ^ 2) := by
    dsimp [b]
    exact sum_sq_mulVec_le A (C.mulVec x)
  have hbx : (∑ i : ι, (x i) ^ 2) ≤ b * (∑ i : ι, ((C.mulVec x) i) ^ 2) := by
    calc
      (∑ i : ι, (x i) ^ 2) = ∑ i : ι, ((A.mulVec (C.mulVec x)) i) ^ 2 := by rw [hxinv]
      _ ≤ b * (∑ i : ι, ((C.mulVec x) i) ^ 2) := hbd
  have hS : 0 ≤ ∑ i : ι, ((C.mulVec x) i) ^ 2 := by
    exact Finset.sum_nonneg (fun i hi => sq_nonneg ((C.mulVec x) i))
  calc
    (∑ i : ι, (x i) ^ 2) ≤ b * (∑ i : ι, ((C.mulVec x) i) ^ 2) := hbx
    _ ≤ (b + 1) * (∑ i : ι, ((C.mulVec x) i) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hS

end Commons.Analysis.Fourier