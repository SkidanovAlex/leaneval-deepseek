import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.Elliptic

/-- A function which is continuous on an open interval `(a, b)` and bounded there
by a constant `C` is interval integrable on `[a, b]`.

The function need not be continuous (or even well behaved) at the endpoints:
the point `b` is a null set for Lebesgue measure, so continuity on `(a, b)`
suffices for almost-everywhere strong measurability, and the bound holds
almost everywhere. Since `volume (Ioc a b) = b - a < ∞`, the integrability
criterion `IntegrableOn.of_bound` applies. -/
theorem intervalIntegrable_of_continuousOn_Ioo_of_bound {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo a b)) (C : ℝ) (hC : ∀ x ∈ Set.Ioo a b, |g x| ≤ C) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  refine IntegrableOn.of_bound ?_ ?_ C ?_
  · -- finiteness of the measure of `Ioc a b`
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · -- almost-everywhere strong measurability, from continuity on the open interval
    have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioo a b)) :=
      hg.aestronglyMeasurable measurableSet_Ioo
    rwa [restrict_Ioo_eq_restrict_Ioc] at h1
  · -- the bound holds almost everywhere on `Ioc a b`
    have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo a b)), ‖g x‖ ≤ C :=
      (ae_restrict_mem measurableSet_Ioo).mono (fun x hx => by
        simpa [Real.norm_eq_abs] using hC x hx)
    rwa [restrict_Ioo_eq_restrict_Ioc] at h1

end Work.Elliptic
