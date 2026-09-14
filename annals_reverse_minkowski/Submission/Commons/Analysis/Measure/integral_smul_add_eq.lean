import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Commons.Analysis.Measure

open MeasureTheory

/-- **Change of variables for a dilation and translation of Lebesgue measure.**

For `ε > 0`, `x : EuclideanSpace ℝ (Fin n)` and integrable `f : EuclideanSpace ℝ (Fin n) → ℝ`,
`∫ y, f y = ε ^ n * ∫ z, f (x + ε • z)`.

Equivalently `∫ z, f (x + ε • z) = ε ^ (-(n : ℤ)) * ∫ y, f y`: this is the substitution
`y = x + ε z`, whose Jacobian is `ε ^ n` since `finrank ℝ (EuclideanSpace ℝ (Fin n)) = n`.

Suggested route: for `ε > 0` the map `T z = x + ε • z` is a homeomorphism of `EuclideanSpace ℝ (Fin n)`,
and `MeasureTheory.Measure.map T volume = (ENNReal.ofReal (ε ^ n))⁻¹ • volume` — equivalently
`MeasureTheory.Measure.addHaar_smul` gives `volume (ε • s) = |ε| ^ n * volume s` and Lebesgue
measure is translation invariant (`MeasureTheory.Measure.map_add_right_eq_self` /
`MeasureTheory.Measure.map_add_left_eq_self`), so
`volume (T '' s) = ε ^ n * volume s`; then apply
`MeasureTheory.MeasurePreserving.integral_comp` (or `MeasureTheory.integral_map`) to the
homeomorphism `T` and its inverse, using that `T '' univ = univ`.  A direct proof via
`MeasureTheory.lintegral_map` / `setLIntegral` together with `Measure.addHaar_smul` is equally fine.
(When `n = 0` the statement is trivial.) -/
theorem integral_smul_add_eq (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f) :
    (∫ y : EuclideanSpace ℝ (Fin n), f y) = ε ^ n * ∫ z, f (x + ε • z) := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  -- Substitution `y = x + ε • z`: dilate by `ε` (Jacobian `ε ^ n`) then translate by `x`.
  have key : (∫ z : EuclideanSpace ℝ (Fin n), f (x + ε • z))
      = (ε ^ n)⁻¹ * ∫ y : EuclideanSpace ℝ (Fin n), f y := by
    rw [show (∫ z : EuclideanSpace ℝ (Fin n), f (x + ε • z))
        = ∫ z, (fun w => f (x + w)) (ε • z) from rfl]
    -- dilation: `∫ z, g (ε • z) = |(ε ^ finrank)⁻¹| • ∫ w, g w`
    rw [Measure.integral_comp_smul volume (fun w : EuclideanSpace ℝ (Fin n) => f (x + w)) ε]
    rw [finrank_euclideanSpace]
    simp only [Fintype.card_fin]
    -- translation by `x` does not change the integral
    rw [integral_add_left_eq_self f x]
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hε.le n))]
    rfl
  rw [key, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hε0), one_mul]

end Commons.Analysis.Measure