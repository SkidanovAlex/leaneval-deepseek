import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Filter

theorem cs_limit_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {h w : α → ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x)
    (hA : ∀ k, AEStronglyMeasurable (fun x => f k x * w x) μ)
    (hB : AEStronglyMeasurable (fun x => h x / w x) μ)
    (hAint : ∀ k, Integrable (fun x => (f k x * w x) ^ 2) μ)
    (hBint : Integrable (fun x => (h x / w x) ^ 2) μ)
    (hlim : Filter.Tendsto (fun k => ∫ x, (f k x * w x) ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x, f k x * h x ∂μ) Filter.atTop (nhds 0) := by
  -- Off the null set where `w = 0` the two products `f k * h` and `(f k * w) * (h / w)` agree.
  have h_ae : ∀ᵐ x ∂μ, ∀ k, (f k x * w x) * (h x / w x) = f k x * h x := by
    filter_upwards [hwpos] with x hx k
    have hx0 : w x ≠ 0 := ne_of_gt hx
    field_simp
  have h_int_eq : ∀ k, (∫ x, f k x * h x ∂μ)
      = ∫ x, (f k x * w x) * (h x / w x) ∂μ := fun k =>
    integral_congr_ae (h_ae.mono fun _ hx => (hx k).symm)
  -- Cauchy–Schwarz (Hölder with `p = q = 2`).
  have h_bound : ∀ k, |∫ x, f k x * h x ∂μ|
      ≤ Real.sqrt (∫ x, (f k x * w x) ^ 2 ∂μ) * Real.sqrt (∫ x, (h x / w x) ^ 2 ∂μ) := by
    intro k
    rw [h_int_eq k]
    exact Work.Blocks.IMC.cs_integral_mul_le μ (hA k) hB (hAint k) hBint
  -- The dominating sequence tends to zero: the first factor does, the second is constant.
  have h_g : Tendsto (fun k => Real.sqrt (∫ x, (f k x * w x) ^ 2 ∂μ)
      * Real.sqrt (∫ x, (h x / w x) ^ 2 ∂μ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => Real.sqrt (∫ x, (f k x * w x) ^ 2 ∂μ)) atTop (nhds 0) := by
      have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
      simpa only [Function.comp_def, Real.sqrt_zero] using hcomp
    simpa using h1.mul_const (Real.sqrt (∫ x, (h x / w x) ^ 2 ∂μ))
  exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact h_bound k) h_g

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
