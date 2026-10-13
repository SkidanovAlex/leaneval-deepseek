import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Gaussian integral on `ℝ³`

`∫ w : ℝ³, exp (-‖w‖ ^ 2) = π * √π`.

The type `R3 = EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, and the map
`WithLp.toLp 2` from `Fin 3 → ℝ` to `R3` is volume preserving
(`PiLp.volume_preserving_toLp`).  On `Fin 3 → ℝ` the Gaussian splits as a product over
the three coordinates (`integral_fintype_prod_volume_eq_pow`), and each factor is the
one-dimensional Gaussian integral `∫ x, exp (-x ^ 2) = √π` (`integral_gaussian`).
-/

open MeasureTheory

namespace Work.FTS.PressureOn.Green

theorem integral_exp_neg_normSq_R3 :
    ∫ w : Work.FTS.PressureOn.R3, Real.exp (-(‖w‖ ^ 2)) = Real.pi * Real.sqrt Real.pi := by
  -- Move from `EuclideanSpace ℝ (Fin 3)` to `Fin 3 → ℝ` (volume preserving).
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  -- Write the Gaussian as a product over the three coordinates.
  have hpoint : (fun x : Fin 3 → ℝ =>
        Real.exp (-(‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ^ 2)))
      = fun x => ∏ i, Real.exp (-((x i) ^ 2)) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_neg_distrib]
  rw [hpoint]
  -- Fubini in three variables.
  rw [integral_fintype_prod_volume_eq_pow (f := fun x : ℝ => Real.exp (-(x ^ 2)))]
  rw [Fintype.card_fin]
  have hg : (∫ x : ℝ, Real.exp (-(x ^ 2))) = Real.sqrt Real.pi := by
    simpa using integral_gaussian 1
  rw [hg, pow_three, ← mul_assoc, Real.mul_self_sqrt Real.pi_nonneg]

end Work.FTS.PressureOn.Green
