import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- **Expansion of the box integral of `(f - c g)²`.**

For continuous `f`, `g` and a compact `P`, the square `(f - c * g)²` expands under the
integral:

    ∫_P (f - c g)² = ∫_P f² - 2 c ∫_P f g + c² ∫_P g² .

This is the algebraic half of the identity
`boxTrialForm c P h g = ∫_P (h - c g)² + c * ∑_k ∫_P (∂_k g)²`, and, as there, the
compactness of `P` is exactly what makes every summand integrable (continuous on a
compact set). -/
theorem integral_sq_sub_mul {P : Set ℝ³} (hK : IsCompact P) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    (∫ x in P, (f x - c * g x) ^ 2)
      = (∫ x in P, (f x) ^ 2) - 2 * c * (∫ x in P, f x * g x)
        + c ^ 2 * (∫ x in P, (g x) ^ 2) := by
  -- Continuity on the compact `P` gives integrability of everything we integrate.
  have hInt : ∀ u : ℝ³ → ℝ, Continuous u → IntegrableOn u P volume :=
    fun u hu => hu.continuousOn.integrableOn_compact hK
  have hA : IntegrableOn (fun x : ℝ³ => (f x) ^ 2) P volume := hInt _ (hf.pow 2)
  have h2cB : IntegrableOn (fun x : ℝ³ => 2 * c * (f x * g x)) P volume :=
    hInt _ (continuous_const.mul (hf.mul hg))
  have hX : IntegrableOn (fun x : ℝ³ => (f x) ^ 2 - 2 * c * (f x * g x)) P volume :=
    hInt _ ((hf.pow 2).sub (continuous_const.mul (hf.mul hg)))
  have hY : IntegrableOn (fun x : ℝ³ => c ^ 2 * (g x) ^ 2) P volume :=
    hInt _ (continuous_const.mul (hg.pow 2))
  -- The integrand is expanded pointwise.
  have step0 : (∫ x in P, (f x - c * g x) ^ 2)
      = ∫ x in P, ((f x) ^ 2 - 2 * c * (f x * g x) + c ^ 2 * (g x) ^ 2) := by
    apply MeasureTheory.setIntegral_congr_fun hK.measurableSet
    intro x _
    ring
  -- Linearity of the integral on the expansion.
  have step1 : (∫ x in P, ((f x) ^ 2 - 2 * c * (f x * g x) + c ^ 2 * (g x) ^ 2))
      = (∫ x in P, ((f x) ^ 2 - 2 * c * (f x * g x))) + (∫ x in P, c ^ 2 * (g x) ^ 2) :=
    MeasureTheory.integral_add hX hY
  have step2 : (∫ x in P, ((f x) ^ 2 - 2 * c * (f x * g x)))
      = (∫ x in P, (f x) ^ 2) - (∫ x in P, 2 * c * (f x * g x)) :=
    MeasureTheory.integral_sub hA h2cB
  have step3 : (∫ x in P, 2 * c * (f x * g x)) = 2 * c * (∫ x in P, f x * g x) :=
    MeasureTheory.integral_const_mul (2 * c) (fun x => f x * g x)
  have step4 : (∫ x in P, c ^ 2 * (g x) ^ 2) = c ^ 2 * (∫ x in P, (g x) ^ 2) :=
    MeasureTheory.integral_const_mul (c ^ 2) (fun x => (g x) ^ 2)
  rw [step0, step1, step2, step3, step4]

end Work.BoseFixB1S
