import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxA0.W1L2Infra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory
open scoped ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The integral of `(g (x - y))^2` over the cube `acube s` is at most the full
`L²`-mass of `g`: the substitution `y ↦ z = x - y` maps the cube onto the
translate `x - acube s`, and the integral of a nonnegative function over any
such set is bounded by its integral over all of `ℝ³`. -/
theorem fibre_bound {s : ℝ} (hs : 0 < s)
    {g : ℝ³ → ℝ} (hg : Measurable g)
    (hint : MeasureTheory.Integrable (fun z : ℝ³ => (g z) ^ 2))
    (x : ℝ³) :
    (∫⁻ y in Submission.BoseGases.acube s, ENNReal.ofReal ((g (x - y)) ^ 2))
      ≤ ENNReal.ofReal (∫ z : ℝ³, (g z) ^ 2) := by
  -- translation invariance of Lebesgue measure: `y ↦ x - y` is measure preserving
  have htrans : ∫⁻ y, ENNReal.ofReal ((g (x - y)) ^ 2)
      = ∫⁻ y, ENNReal.ofReal ((g y) ^ 2) := by
    rw [show (fun y : ℝ³ => ENNReal.ofReal ((g (x - y)) ^ 2))
        = (fun y : ℝ³ => ENNReal.ofReal ((g (-(y + -x))) ^ 2)) by
      funext y; congr 1; congr 1; abel]
    rw [MeasureTheory.lintegral_add_right_eq_self
      (fun w : ℝ³ => ENNReal.ofReal ((g (-w)) ^ 2)) (-x)]
    exact MeasureTheory.lintegral_neg_eq_self (fun w : ℝ³ => ENNReal.ofReal ((g w) ^ 2))
  calc ∫⁻ y in Submission.BoseGases.acube s, ENNReal.ofReal ((g (x - y)) ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal ((g (x - y)) ^ 2) :=
        MeasureTheory.setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ENNReal.ofReal ((g y) ^ 2) := htrans
    _ = ENNReal.ofReal (∫ z : ℝ³, (g z) ^ 2) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall (fun z => sq_nonneg (g z)))]

end Work.SmallBoxA0
