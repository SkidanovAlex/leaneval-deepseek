import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.pairRung

open MeasureTheory
open scoped Real ENNReal

/-- In dimension three the singular weight `‖q‖⁻²` is integrable on any ball
(the radial majorant is `r ^ (3 - 1) * r ^ (-2) = r ^ (-1)`, integrable near `0`). -/
private lemma integrableOn_invSqNorm_ball (R : ℝ) :
    IntegrableOn (fun q : EuclideanSpace ℝ (Fin 3) => (‖q‖ ^ 2)⁻¹)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) volume := by
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := EuclideanSpace ℝ (Fin 3))
    (F := ℝ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (f := fun q => (‖q‖ ^ 2)⁻¹) (C := 1) (α := 2) (r := R) ?_ ?_ ?_ ?_
  · rw [finrank_euclideanSpace]; norm_num
  · rw [finrank_euclideanSpace]; norm_num
  · filter_upwards with x
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), one_mul,
      Real.rpow_neg (norm_nonneg x), Real.rpow_two]
  · exact ((continuous_norm.pow 2).measurable.inv).aestronglyMeasurable

/-- The `ℝ≥0∞`-valued integral of `‖q‖⁻²` over a ball is finite. -/
private lemma setLIntegral_invSqNorm_ball_lt_top (R : ℝ) :
    (∫⁻ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        ENNReal.ofReal ((‖q‖ ^ 2)⁻¹)) < ⊤ :=
  (integrableOn_invSqNorm_ball R).setLIntegral_lt_top

theorem term1SetLinBall {g : EuclideanSpace ℝ (Fin 3) → ℝ} {C R : ℝ}
    (hC : 0 ≤ C) (hg : ∀ q, |g q| ≤ C) :
    (∫⁻ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)) < ⊤ := by
  have hsquare : ∀ q : EuclideanSpace ℝ (Fin 3), g q ^ 2 ≤ C ^ 2 := by
    intro q
    obtain ⟨h1, h2⟩ := abs_le.mp (hg q)
    exact sq_le_sq' h1 h2
  have hcmp : ∀ q : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((‖q‖ ^ 2)⁻¹) := by
    intro q
    calc ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2)
        = ENNReal.ofReal (g q ^ 2) * ENNReal.ofReal ((‖q‖ ^ 2)⁻¹) := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((‖q‖ ^ 2)⁻¹) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (hsquare q)) _
  calc (∫⁻ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
          ENNReal.ofReal (g q ^ 2 / ‖q‖ ^ 2))
      ≤ ∫⁻ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
          ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((‖q‖ ^ 2)⁻¹) :=
        lintegral_mono hcmp
    _ = ENNReal.ofReal (C ^ 2) * (∫⁻ q in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
          ENNReal.ofReal ((‖q‖ ^ 2)⁻¹)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (setLIntegral_invSqNorm_ball_lt_top R)

end Work.BoseFixB1B.pairRung
