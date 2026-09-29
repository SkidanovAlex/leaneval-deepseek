import Mathlib

namespace Work.ZeroEst

open Finset

/-- Leibniz expansion of the determinant with the row-index convention
`det M = ∑ σ, sign σ * ∏ i, M i (σ i)` (Mathlib's `det_apply'` uses the
transposed convention `M (σ i) i`). -/
lemma det_apply_row {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  simp only [Matrix.transpose_apply]

/-- Cauchy--Binet in the "all minors" form: the determinant of the `r × r` product
`E * Y` of an `r × m` matrix with an `m × r` matrix is the sum, over all functions
`T : Fin r → Fin m`, of `(∏ a, E a (T a)) * det (Y.submatrix T id)`.  Terms with
non-injective `T` vanish (the corresponding minor of `Y` has a repeated row), so this
is Cauchy--Binet summed over all choice functions. -/
theorem det_mul_eq_sum_minors {r m : ℕ} (E : Matrix (Fin r) (Fin m) (PowerSeries ℚ))
    (Y : Matrix (Fin m) (Fin r) (PowerSeries ℚ)) :
    (E * Y).det
      = ∑ T : Fin r → Fin m,
          (∏ a : Fin r, E a (T a)) * (Y.submatrix T id).det := by
  -- Both sides expand to the *same* double sum over `(σ, T)`, hence are equal by
  -- commutativity of addition.
  have hL : (E * Y).det
      = ∑ σ : Equiv.Perm (Fin r), ∑ T : Fin r → Fin m,
          ((Equiv.Perm.sign σ : ℤ) : PowerSeries ℚ) * ∏ i, (E i (T i) * Y (T i) (σ i)) := by
    rw [det_apply_row]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Matrix.mul_apply]
    rw [Fintype.prod_sum]
    rw [Finset.mul_sum]
  have hR : (∑ T : Fin r → Fin m, (∏ a : Fin r, E a (T a)) * (Y.submatrix T id).det)
      = ∑ T : Fin r → Fin m, ∑ σ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign σ : ℤ) : PowerSeries ℚ) * ∏ i, (E i (T i) * Y (T i) (σ i)) := by
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [det_apply_row]
    simp only [Matrix.submatrix_apply, id_eq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.prod_mul_distrib]
    ring
  rw [hL, hR, Finset.sum_comm]

end Work.ZeroEst
