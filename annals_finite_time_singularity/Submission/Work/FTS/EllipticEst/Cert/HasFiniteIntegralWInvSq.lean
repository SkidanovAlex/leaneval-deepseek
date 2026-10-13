import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology
open MeasureTheory Set Filter

/-- The weight `(r w(r))^{-2}` is finitely integrable on `(0,∞)`: with `w r = (1+r)²/r²` one has
`(r w r)^{-1} = r/(1+r)²`, so the integrand is `r²/(1+r)⁴ ≤ (1+r)^{-2}`, and `(1+r)^{-1}` is the
antiderivative of `(1+r)^{-2}` with limit `0` at `∞`, whence `(1+r)^{-2}` is integrable on
`(0,∞)` by the derivative criterion `integrableOn_Ioi_deriv_of_nonneg`. -/
theorem HasFiniteIntegralWInvSq :
    MeasureTheory.HasFiniteIntegral (fun r : ℝ => ((r * Work.Spaces.w r)⁻¹) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hfun : (fun r : ℝ => ((r * Work.Spaces.w r)⁻¹) ^ 2)
      = fun r : ℝ => (r / (1 + r) ^ 2) ^ 2 := by
    funext r
    by_cases hr : r = 0
    · subst hr; simp [Work.Spaces.w]
    · have h1 : r * ((1 + r) ^ 2 / r ^ 2) = (1 + r) ^ 2 / r := by
        field_simp
      simp only [Work.Spaces.w, h1, inv_div]
  rw [hfun]
  apply Integrable.hasFiniteIntegral
  have hg : IntegrableOn (fun r : ℝ => ((1 + r) ^ 2)⁻¹) (Set.Ioi 0) := by
    refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (l := 0)
      (g := fun r : ℝ => -((1 + r)⁻¹)) (g' := fun r : ℝ => ((1 + r) ^ 2)⁻¹) ?_ ?_ ?_ ?_
    · have hcont : ContinuousOn (fun r : ℝ => -((1 + r)⁻¹)) (Set.Ici (0:ℝ)) := by
        refine ContinuousOn.neg ?_
        refine ContinuousOn.inv₀ (continuousOn_const.add continuousOn_id) ?_
        intro x hx
        simp only [Set.mem_Ici] at hx
        positivity
      exact hcont.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
    · intro x hx
      have hx0 : (0 : ℝ) < 1 + x := by simp only [Set.mem_Ioi] at hx; linarith
      have h1 : HasDerivAt (fun r : ℝ => 1 + r) 1 x := by
        simpa using (hasDerivAt_id x).const_add (1 : ℝ)
      have h2 : HasDerivAt (fun r : ℝ => (1 + r)⁻¹) (-(((1 + x) ^ 2)⁻¹)) x := by
        have h := h1.inv hx0.ne'
        convert h using 1
        field_simp
      simpa only [Pi.neg_def, neg_neg] using h2.neg
    · intro x hx
      positivity
    · have hlin : Tendsto (fun r : ℝ => (1 : ℝ) + r) atTop atTop :=
        tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
      have ht : Tendsto (fun r : ℝ => (1 + r)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hlin
      simpa only [Pi.neg_def, neg_zero] using ht.neg
  refine hg.mono' ?_ ?_
  · have hmeas : Measurable (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hrp : (0 : ℝ) < r := hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ((1 + r) ^ 2) ^ 2)]
    have hkey : ((1 + r) ^ 2)⁻¹ * ((1 + r) ^ 2) ^ 2 = (1 + r) ^ 2 := by
      field_simp
    rw [hkey]
    nlinarith

end Work.FTS.EllipticEst.Cert
