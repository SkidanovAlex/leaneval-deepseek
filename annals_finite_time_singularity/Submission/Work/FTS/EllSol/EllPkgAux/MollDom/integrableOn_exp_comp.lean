import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set

/-- If `F` is integrable on every compact interval `[c, d]` with `0 < c`, then the composition
`t ↦ F (exp t)` is integrable on every compact interval `[a, b]`.  This is the change of variables
`u = exp t` (`du = u dt`, i.e. `dt = du / u`): on `[a, b]` the factor `1 / exp t` is bounded by
`1 / exp a`, so it is harmless.

The substitution is performed with the interval-integral change-of-variables lemma
`intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg` (monotone version, `f' = exp ≥ 0`),
applied to `g u = F u / u`; then `(g ∘ exp) t * exp t = F (exp t)`. -/
theorem integrableOn_exp_comp {F : ℝ → ℝ}
    (hF : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn F (Set.Icc a b)) (a b : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => F (Real.exp t)) (Set.Icc a b) MeasureTheory.volume := by
  by_cases hab : a ≤ b
  · -- `F` is integrable on `[exp a, exp b]`, hence so is `u ↦ F u / u`, since `1/u ≤ 1/exp a`
    -- there.
    have hcd : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
    have hFcd : MeasureTheory.IntegrableOn F (Set.Icc (Real.exp a) (Real.exp b)) :=
      hF _ _ (Real.exp_pos a) hcd
    have hcont : ContinuousOn (fun u : ℝ => u⁻¹) (Set.Icc (Real.exp a) (Real.exp b)) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos a) hx.1)
    have hdiv : MeasureTheory.IntegrableOn (fun u : ℝ => F u / u)
        (Set.Icc (Real.exp a) (Real.exp b)) := by
      simpa [div_eq_mul_inv] using hFcd.mul_continuousOn hcont isCompact_Icc
    -- pass from `Icc` to `Ioc` (they differ by the null set `{exp a}`) to match the
    -- `IntervalIntegrable` API, which is stated with `uIoc`.
    have hdivIoc : MeasureTheory.IntegrableOn (fun u : ℝ => F u / u)
        (Set.Ioc (Real.exp a) (Real.exp b)) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mp hdiv
    have hII_div : IntervalIntegrable (fun u : ℝ => F u / u)
        MeasureTheory.volume (Real.exp a) (Real.exp b) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hcd]
      exact hdivIoc
    -- change of variables `u = exp t`: `(g ∘ exp) t * exp t` is interval integrable
    have hII_comp : IntervalIntegrable
        (fun x : ℝ => (F (Real.exp x) / Real.exp x) * Real.exp x) MeasureTheory.volume a b :=
      (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
        (a := a) (b := b) (f := Real.exp) (f' := Real.exp) (g := fun u : ℝ => F u / u)
        Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
        (fun x _ => (Real.exp_pos x).le)).mpr hII_div
    -- and the factor `exp x` cancels against the `1 / exp x` coming from `g`
    have hII_F : IntervalIntegrable (fun x : ℝ => F (Real.exp x)) MeasureTheory.volume a b := by
      refine IntervalIntegrable.congr ?_ hII_comp
      intro x hx
      simp only [div_mul_cancel₀ _ (Real.exp_ne_zero x)]
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab] at hII_F
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr hII_F
  · -- degenerate case: `Icc a b = ∅`
    rw [Set.Icc_eq_empty_iff.mpr hab]
    exact integrableOn_empty

end Work.FTS.EllSol.EllPkgAux.MollDom
