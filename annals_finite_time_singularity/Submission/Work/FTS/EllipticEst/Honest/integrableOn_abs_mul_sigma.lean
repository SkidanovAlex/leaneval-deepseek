import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem integrableOn_abs_mul_sigma {s : Set ℝ} {p q σ : ℝ → ℝ} (hσ : ∀ θ ∈ s, 0 ≤ σ θ)
    (hp : MeasureTheory.IntegrableOn (fun θ => p θ ^ 2 * σ θ) s)
    (hq : MeasureTheory.IntegrableOn (fun θ => q θ ^ 2 * σ θ) s) :
    MeasureTheory.IntegrableOn (fun θ => |p θ * q θ * σ θ|) s := by
  -- The hypotheses on the weighted squares are what drives the proof: the pointwise bound
  --   `|p q σ| = √(|p²σ| · |q²σ|) ≤ (|p²σ| + |q²σ|) / 2`
  -- holds for *all* `θ` (AM–GM on `|p²σ|, |q²σ| ≥ 0`), so no sign information on `σ` is needed;
  -- in particular `hσ` is not used, and `s` need not be measurable.
  have := hσ
  have hX : MeasureTheory.Integrable (fun θ => |p θ ^ 2 * σ θ|) (MeasureTheory.volume.restrict s) := by
    simpa only [Real.norm_eq_abs] using hp.abs
  have hY : MeasureTheory.Integrable (fun θ => |q θ ^ 2 * σ θ|) (MeasureTheory.volume.restrict s) := by
    simpa only [Real.norm_eq_abs] using hq.abs
  have hg : MeasureTheory.Integrable (fun θ => (|p θ ^ 2 * σ θ| + |q θ ^ 2 * σ θ|) / 2)
      (MeasureTheory.volume.restrict s) := (hX.add hY).div_const 2
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => Real.sqrt (|p θ ^ 2 * σ θ| * |q θ ^ 2 * σ θ|))
      (MeasureTheory.volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict s),
      ‖Real.sqrt (|p θ ^ 2 * σ θ| * |q θ ^ 2 * σ θ|)‖
        ≤ (|p θ ^ 2 * σ θ| + |q θ ^ 2 * σ θ|) / 2 := by
    filter_upwards with θ
    have hX0 : 0 ≤ |p θ ^ 2 * σ θ| := abs_nonneg _
    have hY0 : 0 ≤ |q θ ^ 2 * σ θ| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h2 : 2 * Real.sqrt (|p θ ^ 2 * σ θ|) * Real.sqrt (|q θ ^ 2 * σ θ|)
        ≤ (Real.sqrt (|p θ ^ 2 * σ θ|)) ^ 2 + (Real.sqrt (|q θ ^ 2 * σ θ|)) ^ 2 :=
      two_mul_le_add_sq _ _
    rw [Real.sq_sqrt hX0, Real.sq_sqrt hY0] at h2
    rw [Real.sqrt_mul hX0]
    linarith
  have hInt : MeasureTheory.Integrable
      (fun θ => Real.sqrt (|p θ ^ 2 * σ θ| * |q θ ^ 2 * σ θ|))
      (MeasureTheory.volume.restrict s) := MeasureTheory.Integrable.mono' hg hmeas hbound
  refine MeasureTheory.Integrable.congr hInt ?_
  filter_upwards with θ
  rw [← abs_mul,
    show p θ ^ 2 * σ θ * (q θ ^ 2 * σ θ) = (p θ * q θ * σ θ) ^ 2 from by ring]
  rw [abs_of_nonneg (sq_nonneg _), Real.sqrt_sq_eq_abs]

end Work.FTS.EllipticEst.Honest
