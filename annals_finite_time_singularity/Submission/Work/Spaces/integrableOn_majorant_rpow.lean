import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory Set

/-- The function `θ ↦ (π/4)^p * (θ^(-p) + (π/2 - θ)^(-p))` is integrable on `[0, π/2]`
for `p ∈ (0,1)`: both singular terms are `rpow`-integrable since the exponent `-p`
satisfies `-1 < -p`. -/
theorem integrableOn_majorant_rpow (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  have hp : -1 < -p := by linarith
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ (-p)) (Set.Icc 0 (Real.pi / 2)) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hpi]
    exact intervalIntegral.intervalIntegrable_rpow' hp
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-p)) (Set.Icc 0 (Real.pi / 2)) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hpi]
    simpa using
      (IntervalIntegrable.comp_sub_left_iff (f := fun θ : ℝ => θ ^ (-p)) (Real.pi / 2)
        (a := Real.pi / 2) (b := 0)).mpr
        (intervalIntegral.intervalIntegrable_rpow' hp).symm
  have hsum : MeasureTheory.IntegrableOn
      (fun θ : ℝ => θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) (Set.Icc 0 (Real.pi / 2)) :=
    h1.add h2
  exact hsum.const_mul ((Real.pi / 4) ^ p)

end Work.Spaces
