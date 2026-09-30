import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Matrix

/-- The Vaaler "inner" count
`y ↦ ∫ x, 1_{∀ i, |(B x + B' y)_i| ≤ 1/2}(x) dx` is a measurable function of `y`.

The integrand, viewed as a function of the pair `(x, y)`, is the indicator of a closed
(hence Borel measurable) set, so it is jointly measurable.  The Bochner integral of a
jointly measurable function in one variable is again measurable
(`MeasureTheory.StronglyMeasurable.integral_prod_left`). -/
theorem vaalerInner_measurable {n k m : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (Bp : Matrix (Fin n) (Fin m) ℝ) :
    Measurable (fun y : Fin m → ℝ =>
      ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)) := by
  -- The affine map `p ↦ B *ᵥ p.1 + Bp *ᵥ p.2` is continuous.
  have hcont : Continuous (fun p : (Fin k → ℝ) × (Fin m → ℝ) => B.mulVec p.1 + Bp.mulVec p.2) := by
    fun_prop
  -- Hence its preimage of the closed unit box is closed, hence measurable.
  have hcl : IsClosed {p : (Fin k → ℝ) × (Fin m → ℝ) | ∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2} := by
    rw [show {p : (Fin k → ℝ) × (Fin m → ℝ) | ∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2}
        = ⋂ i, {p | |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2} by ext p; simp]
    exact isClosed_iInter fun i => isClosed_le (((continuous_apply i).comp hcont).abs) continuous_const
  -- The uncurried integrand is the indicator of that set, hence measurable.
  have hmeas : Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) =>
      (if (∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2) then (1:ℝ) else 0)) := by
    have h_eq : (fun p : (Fin k → ℝ) × (Fin m → ℝ) =>
        (if (∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2) then (1:ℝ) else 0))
        = Set.indicator
            {p : (Fin k → ℝ) × (Fin m → ℝ) | ∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2}
            (fun _ => (1:ℝ)) := by
      funext p
      rw [Set.indicator_apply]
      by_cases h : (∀ i, |(B.mulVec p.1 + Bp.mulVec p.2) i| ≤ 1/2) <;> simp
    rw [h_eq]
    exact Measurable.indicator measurable_const hcl.measurableSet
  -- Integrate the jointly measurable integrand in `x`: the result is measurable in `y`.
  exact (hmeas.stronglyMeasurable.integral_prod_left).measurable

end Work.BW
