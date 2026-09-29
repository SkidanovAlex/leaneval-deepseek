import Mathlib
import Submission.Work.ZeroEst.mderiv_defs
import Submission.Commons.LinearAlgebra.Matrix.deriv_det

/-!
# `Work.ZeroEst.mderiv_adjugate_mul`

The identity relating the entrywise derivative of the adjugate of a matrix of power series to the
adjugate of the matrix and its derivative:

`(adj M)' · M = tr(adj M · M') • 1 - adj M · M'`,

i.e. the derivative of the "adjugate · matrix = det · 1" identity.  The main input is Jacobi's
formula `(det M)' = tr(adj M · M')` (`Commons.LinearAlgebra.Matrix.deriv_det`), which is available
for any commutative ring carrying a `Differential` structure.  We install the canonical differential
structure on `PowerSeries ℚ` given by the formal derivative.
-/

namespace Work.ZeroEst

open Polynomial PowerSeries Matrix

/-- The canonical `Differential` structure on `PowerSeries ℚ`, whose derivation is the formal
derivative `PowerSeries.derivative (R := ℚ)`.

The `letI` pins the `ℤ`-algebra structure used for the `Derivation` field of the `Differential`
class to `Ring.toIntAlgebra`; otherwise typeclass search picks `MvPowerSeries.instAlgebra`, which is
not definitionally equal to it. -/
noncomputable instance instDifferentialPowerSeriesRat : Differential (PowerSeries ℚ) :=
  letI : Algebra ℤ (PowerSeries ℚ) := Ring.toIntAlgebra _
  ⟨(PowerSeries.derivative (R := ℚ)).restrictScalars ℤ⟩

@[simp] lemma differential_deriv_powerSeries (f : PowerSeries ℚ) :
    Differential.deriv f = PowerSeries.derivative (R := ℚ) f := rfl

/-- Leibniz rule for the entrywise derivative of a product of matrices of power series. -/
lemma mderiv_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) :
    mderiv (A * B) = mderiv A * B + A * mderiv B := by
  ext i j
  simp only [mderiv_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [map_sum]
  have h : ∀ k, PowerSeries.derivative (R := ℚ) (A i k * B k j)
      = A i k * PowerSeries.derivative (R := ℚ) (B k j)
        + PowerSeries.derivative (R := ℚ) (A i k) * B k j := by
    intro k
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm (B k j)]
  simp only [h, Finset.sum_add_distrib]
  rw [add_comm]

/-- The entrywise derivative of a scalar multiple of the identity matrix. -/
lemma mderiv_smul_one {n : ℕ} (c : PowerSeries ℚ) :
    mderiv (c • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ)))
      = PowerSeries.derivative (R := ℚ) c • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) := by
  rw [Matrix.smul_one_eq_diagonal]
  change (Matrix.diagonal fun _ : Fin n => c).map (PowerSeries.derivative (R := ℚ))
      = PowerSeries.derivative (R := ℚ) c • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ))
  rw [Matrix.diagonal_map (map_zero _), Matrix.smul_one_eq_diagonal]

/-- **Jacobi's formula for the derivative of the determinant**, in the form needed below. -/
lemma derivative_det_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) :
    PowerSeries.derivative (R := ℚ) M.det = (M.adjugate * mderiv M).trace := by
  rw [← differential_deriv_powerSeries M.det, Commons.LinearAlgebra.Matrix.deriv_det M]
  rfl

theorem mderiv_adjugate_mul {n : ℕ} (M : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) :
    mderiv (M.adjugate) * M
      = (M.adjugate * mderiv M).trace • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ))
        - M.adjugate * mderiv M := by
  rw [eq_sub_iff_add_eq]
  calc mderiv (M.adjugate) * M + M.adjugate * mderiv M
      = mderiv (M.adjugate * M) := (mderiv_mul _ _).symm
    _ = mderiv (M.det • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ))) := by
          rw [Matrix.adjugate_mul]
    _ = PowerSeries.derivative (R := ℚ) M.det • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) :=
          mderiv_smul_one M.det
    _ = (M.adjugate * mderiv M).trace • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) := by
          rw [derivative_det_eq_trace]

end Work.ZeroEst
