import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Commons.Analysis.Fourier.norm_sum_sq_le_of_bounded_overlap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Plancherel's theorem for an L¹ ∩ L² function on ℝ³

If `f : EuclideanSpace ℝ (Fin 3) → ℂ` is both integrable and square-integrable, then the `L²`
norm of its Fourier transform equals the `L²` norm of `f`:

`∫ ξ, ‖𝓕 f ξ‖² = ∫ x, ‖f x‖²`.

This is the classical Plancherel theorem in the case of a function lying in `L¹ ∩ L²`, where
the Fourier transform `𝓕 f` may be taken to be the pointwise Fourier integral
`ξ ↦ ∫ x, 𝐞 (-⟪x, ξ⟫) • f x`.

It is an immediate corollary of the general finite-dimensional statement
`Commons.Analysis.Fourier.integral_norm_sq_eq_integral_fourier_norm_sq`, proved by identifying
the `L¹` and `L²` representatives in `L²` and appealing to the fact that the `L²` Fourier
transform is a linear isometry (`Lp.norm_fourier_eq`).
-/

open MeasureTheory
open scoped FourierTransform

namespace Commons.Analysis.Fourier

theorem integral_norm_sq_fourier_l1l2 {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf1 : MeasureTheory.Integrable f) (hf2 : MeasureTheory.MemLp f 2) :
    (∫ ξ : EuclideanSpace ℝ (Fin 3),
        ‖(FourierTransform.fourier f : EuclideanSpace ℝ (Fin 3) → ℂ) ξ‖ ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ^ 2 := by
  have h1 : MeasureTheory.MemLp f 1 (MeasureTheory.volume : MeasureTheory.Measure
      (EuclideanSpace ℝ (Fin 3))) := memLp_one_iff_integrable.2 hf1
  exact (integral_norm_sq_eq_integral_fourier_norm_sq h1 hf2).symm

end Commons.Analysis.Fourier
