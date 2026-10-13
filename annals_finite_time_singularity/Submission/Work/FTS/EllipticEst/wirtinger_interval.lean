import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.wirt_deriv_sq_integrable
import Submission.Work.FTS.EllipticEst.wirt_G_integrable
import Submission.Work.FTS.EllipticEst.wirt_phi_deriv
import Submission.Work.FTS.EllipticEst.wirt_phi_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter intervalIntegral

namespace Work.FTS.EllipticEst

/-- **Wirtinger's inequality on an interval, in the `r`-parametrised form.**  If `r > 0` with
`r * (b - a) = π` and `u` is `C²` on `[a,b]` with `u a = u b = 0`, then
`r² ∫ u² ≤ ∫ u'²`.  The proof uses the auxiliary function
`Φ x = r * u x ^ 2 * cot (r * (x - a))`, which vanishes at both endpoints and satisfies
`Φ' = u'² - r² u² - ((u' sin - u r cos) / sin)²` on `(a,b)`; integrating the identity and
dropping the nonnegative square gives the claim. -/
theorem wirtinger_interval_aux {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    r ^ 2 * (∫ θ in a..b, (u θ) ^ 2) ≤ ∫ θ in a..b, (deriv u θ) ^ 2 := by
  set Phi : ℝ → ℝ :=
    fun x => r * (u x) ^ 2 * (Real.cos (r * (x - a)) / Real.sin (r * (x - a))) with hPhi
  set G : ℝ → ℝ := fun x => ((deriv u x * Real.sin (r * (x - a))
      - u x * (r * Real.cos (r * (x - a)))) / Real.sin (r * (x - a))) ^ 2 with hG
  set f : ℝ → ℝ := fun x => (deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2 - G x with hf
  have hA : IntervalIntegrable (fun x => (deriv u x) ^ 2) volume a b :=
    wirt_deriv_sq_integrable hab hu
  have hB : IntervalIntegrable (fun x => r ^ 2 * (u x) ^ 2) volume a b :=
    ((hu.continuousOn.pow 2).const_mul (r ^ 2)).intervalIntegrable_of_Icc hab.le
  have hGi : IntervalIntegrable G volume a b := by
    rw [hG]; exact wirt_G_integrable hab hr hrb hu ha hb
  have hf_int : IntervalIntegrable f volume a b := by
    rw [hf]
    exact (hA.sub hB).sub hGi
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt Phi (f x) x := by
    intro x hx
    rw [hPhi, hf, hG]
    exact wirt_phi_deriv hab hr hrb hu x hx
  obtain ⟨hta, htb⟩ := wirt_phi_tendsto hab hr hrb hu ha hb
  have hta' : Tendsto Phi (nhdsWithin a (Set.Ioi a)) (nhds 0) := by rw [hPhi]; exact hta
  have htb' : Tendsto Phi (nhdsWithin b (Set.Iio b)) (nhds 0) := by rw [hPhi]; exact htb
  have hFTC : ∫ x in a..b, f x = 0 := by
    rw [integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hf_int hta' htb']
    ring
  have hnonneg : 0 ≤ ∫ x in a..b, G x := by
    refine integral_nonneg hab.le (fun x hx => ?_)
    rw [hG]; positivity
  have hpt : ∀ x, f x + G x = (deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2 := by
    intro x; rw [hf]; ring
  have h1 : (∫ x in a..b, ((deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2))
      = (∫ x in a..b, f x) + (∫ x in a..b, G x) := by
    rw [← intervalIntegral.integral_add hf_int hGi]
    exact (intervalIntegral.integral_congr (fun x _ => hpt x)).symm
  have h2 : (∫ x in a..b, ((deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2))
      = (∫ x in a..b, (deriv u x) ^ 2) - ∫ x in a..b, r ^ 2 * (u x) ^ 2 := by
    rw [intervalIntegral.integral_sub hA hB]
  have h3 : (∫ x in a..b, r ^ 2 * (u x) ^ 2) = r ^ 2 * ∫ x in a..b, (u x) ^ 2 :=
    intervalIntegral.integral_const_mul (r ^ 2) (fun x => (u x) ^ 2)
  have key : r ^ 2 * (∫ x in a..b, (u x) ^ 2) ≤ ∫ x in a..b, (deriv u x) ^ 2 := by
    have h := h1
    rw [h2, h3, hFTC, zero_add] at h
    linarith [hnonneg]
  exact key

/-- **Wirtinger's inequality on an interval.** For a `C²` function `u` on `[a,b]` with
`u a = u b = 0`, `(π/(b-a))² ∫ u² ≤ ∫ u'²`. -/
theorem wirtinger_interval {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    (π / (b - a)) ^ 2 * (∫ θ in a..b, (u θ) ^ 2) ≤ ∫ θ in a..b, (deriv u θ) ^ 2 := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hr : 0 < π / (b - a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hrb : π / (b - a) * (b - a) = π := div_mul_cancel₀ π hne
  simpa using wirtinger_interval_aux hab hr hrb hu ha hb

end Work.FTS.EllipticEst
