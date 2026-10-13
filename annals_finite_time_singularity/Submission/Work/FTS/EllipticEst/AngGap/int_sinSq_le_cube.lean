import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst.AngGap

/-- For `v ∈ [0, π/4]`, the integral `∫_0^v sin²(2t) dt` is bounded by
`4 (π/4)³ sin³(2v)`.

Chain of inequalities:
`∫_0^v sin²(2t) dt ≤ ∫_0^v 4v² = 4v³ ≤ 4 (π/4)³ sin³(2v)`,
where the first step uses `sin²(2t) ≤ (2t)² ≤ (2v)²` for `t ∈ [0,v]`, and the
last step uses Jordan's inequality `sin x ≥ (2/π) x` on `[0, π/2]`. -/
theorem int_sinSq_le_cube (v : ℝ) (hv : v ∈ Set.Icc 0 (π / 4)) :
    ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2 ≤ 4 * (π / 4) ^ 3 * (Real.sin (2 * v)) ^ 3 := by
  have hv0 : 0 ≤ v := hv.1
  have h2v_nn : 0 ≤ 2 * v := by linarith
  have h2v_le : 2 * v ≤ π / 2 := by linarith [hv.2]
  -- Step 1: pointwise bound `sin²(2t) ≤ 4v²` on `[0,v]`.
  have hmono : ∀ t ∈ Set.Icc (0 : ℝ) v, (Real.sin (2 * t)) ^ 2 ≤ 4 * v ^ 2 := by
    intro t ht
    have h2t0 : 0 ≤ 2 * t := by linarith [ht.1]
    have h2tv : 2 * t ≤ 2 * v := by linarith [ht.2]
    calc (Real.sin (2 * t)) ^ 2 ≤ (2 * t) ^ 2 := Real.sin_sq_le_sq
      _ ≤ (2 * v) ^ 2 := pow_le_pow_left₀ h2t0 h2tv 2
      _ = 4 * v ^ 2 := by ring
  have hcont : Continuous fun t : ℝ => (Real.sin (2 * t)) ^ 2 := by fun_prop
  have hint : ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2 ≤ ∫ t in (0 : ℝ)..v, (4 * v ^ 2) :=
    intervalIntegral.integral_mono_on hv0 (hcont.intervalIntegrable _ _)
      intervalIntegrable_const hmono
  have h1 : ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2 ≤ 4 * v ^ 3 := by
    calc ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2 ≤ ∫ t in (0 : ℝ)..v, (4 * v ^ 2) := hint
      _ = 4 * v ^ 3 := by rw [intervalIntegral.integral_const]; ring
  -- Step 2: `v ≤ (π/4) sin(2v)` from Jordan's inequality.
  have key : (2 : ℝ) / π * (2 * v) ≤ Real.sin (2 * v) := Real.mul_le_sin h2v_nn h2v_le
  have key2 : 4 * v / π ≤ Real.sin (2 * v) := by
    have heq : (2 : ℝ) / π * (2 * v) = 4 * v / π := by ring
    rwa [heq] at key
  have h4 : 4 * v ≤ π * Real.sin (2 * v) := by
    have := (div_le_iff₀ Real.pi_pos).mp key2
    linarith
  have hv_le : v ≤ π / 4 * Real.sin (2 * v) := by nlinarith [h4]
  have hcube : v ^ 3 ≤ (π / 4) ^ 3 * (Real.sin (2 * v)) ^ 3 := by
    have := pow_le_pow_left₀ hv0 hv_le 3
    rwa [mul_pow] at this
  calc ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2 ≤ 4 * v ^ 3 := h1
    _ ≤ 4 * (π / 4) ^ 3 * (Real.sin (2 * v)) ^ 3 := by nlinarith [hcube]

end Work.FTS.EllipticEst.AngGap
