import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set intervalIntegral

namespace Work.Spaces

/-- Evaluating the majorant integral of `sin_rpow_le_majorant`:
for `0 < p < 1` one has
`∫₀^{π/2} (π/4)^p (θ^{-p} + (π/2 - θ)^{-p}) dθ = π (1/2)^p / (1 - p)`. -/
theorem integral_majorant_rpow (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ θ in Set.Icc (0 : ℝ) (π / 2), ((π / 4) ^ p * (θ ^ (-p) + (π / 2 - θ) ^ (-p)))
      = π * (1 / 2) ^ p / (1 - p) := by
  have h0le : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hp : -1 < -p := by linarith
  -- Integrability of the two summands on `[0, π/2]`.
  have hf : IntervalIntegrable (fun x : ℝ => x ^ (-p)) volume (0 : ℝ) (π / 2) :=
    intervalIntegrable_rpow' hp
  have hg : IntervalIntegrable (fun x : ℝ => (π / 2 - x) ^ (-p)) volume (0 : ℝ) (π / 2) := by
    have h := (hf.comp_sub_left (π / 2)).symm
    simpa using h
  -- `∫₀^{π/2} θ^{-p} dθ = (π/2)^{1-p} / (1 - p)`.
  have h1 : (∫ θ in (0 : ℝ)..(π / 2), θ ^ (-p)) = (π / 2) ^ (1 - p) / (1 - p) := by
    rw [integral_rpow (Or.inl hp)]
    rw [show (-p + 1 : ℝ) = 1 - p by ring]
    rw [Real.zero_rpow (by intro h; linarith)]
    ring
  -- The reflected integral is the same by the substitution `θ ↦ π/2 - θ`.
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), (π / 2 - θ) ^ (-p)) = (π / 2) ^ (1 - p) / (1 - p) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-p)) (π / 2)]
    simp only [sub_self, sub_zero]
    exact h1
  -- Pass from the set integral over `Icc 0 (π/2)` to the interval integral `0..π/2`.
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0le]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hf hg, h1, h2]
  -- Pure `rpow` bookkeeping: `(π/2)^{1-p} = (π/2) · ((π/2)^p)⁻¹`, and
  -- `(π/4)^p · ((π/2)^p)⁻¹ = (1/2)^p`.
  have h2p : (π / 2 : ℝ) ^ (1 - p) = (π / 2) * ((π / 2) ^ p)⁻¹ := by
    rw [show (1 : ℝ) - p = 1 + (-p) by ring, Real.rpow_add (by linarith [Real.pi_pos]),
      Real.rpow_one, Real.rpow_neg (by linarith [Real.pi_pos])]
  have h3 : (π / 4 : ℝ) ^ p * ((π / 2) ^ p)⁻¹ = (1 / 2 : ℝ) ^ p := by
    rw [← div_eq_mul_inv, ← Real.div_rpow (by positivity) (by positivity) p]
    congr 1
    field_simp
    ring
  have hmain : (π / 4) ^ p * (2 * (π / 2) ^ (1 - p)) = π * (1 / 2) ^ p := by
    rw [h2p]
    calc (π / 4) ^ p * (2 * ((π / 2) * ((π / 2) ^ p)⁻¹))
        = 2 * ((π / 2) * ((π / 4) ^ p * ((π / 2) ^ p)⁻¹)) := by ring
      _ = 2 * ((π / 2) * (1 / 2) ^ p) := by rw [h3]
      _ = π * (1 / 2) ^ p := by ring
  have key : (2 * (π / 4) ^ p * (π / 2) ^ (1 - p)) = π * (1 / 2) ^ p := by
    rw [show (2 : ℝ) * (π / 4) ^ p * (π / 2) ^ (1 - p)
        = (π / 4) ^ p * (2 * (π / 2) ^ (1 - p)) by ring]
    exact hmain
  have e1 : (π / 2) ^ (1 - p) / (1 - p) + (π / 2) ^ (1 - p) / (1 - p)
      = 2 * ((π / 2) ^ (1 - p) / (1 - p)) := by ring
  have e2 : (π / 4) ^ p * (2 * ((π / 2) ^ (1 - p) / (1 - p)))
      = (2 * (π / 4) ^ p * (π / 2) ^ (1 - p)) / (1 - p) := by ring
  rw [e1, e2, key]

end Work.Spaces
