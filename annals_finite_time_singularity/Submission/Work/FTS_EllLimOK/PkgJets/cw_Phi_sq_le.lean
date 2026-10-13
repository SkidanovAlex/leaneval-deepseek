import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.PkgJets.CosWeightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

theorem cw_Phi_sq_le : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
    cwPhi θ ^ (2 : ℕ) ≤ 10 ^ (4 : ℕ) * cwG θ * cwB θ := by
  intro θ hθ
  obtain ⟨hθ0, hθ2⟩ := hθ
  -- positivity of the two basic factors
  have hA : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hC : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  -- the elementary trigonometric bound `sin(2θ)² ≤ 4 cos(θ)²`
  have hkey : Real.sin (2 * θ) ^ 2 ≤ 4 * (Real.cos θ) ^ 2 := by
    have hsq : Real.sin (2 * θ) ^ 2 = 4 * (Real.sin θ) ^ 2 * (Real.cos θ) ^ 2 := by
      rw [Real.sin_two_mul]; ring
    rw [hsq]
    nlinarith [Real.sin_sq_le_one θ, sq_nonneg (Real.cos θ)]
  have hmul : 2500 * Real.sin (2 * θ) ^ 2 ≤ 10 ^ (4 : ℕ) * (Real.cos θ) ^ 2 := by
    nlinarith [hkey]
  -- split the power `sin(2θ)^{1-η} = sin(2θ) · sin(2θ)^{-η}`
  have hsplit : Real.sin (2 * θ) ^ (1 - Work.Spaces.eta)
      = Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
      Real.rpow_add hA, Real.rpow_one]
  -- put both sides into a comparable shape
  have hleft : cwPhi θ ^ (2 : ℕ)
      = 2500 * Real.sin (2 * θ) ^ 2
          * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2
          / (Real.cos θ) ^ (8 : ℕ) := by
    simp only [cwPhi]
    rw [hsplit]
    field_simp
    ring
  have hright : 10 ^ (4 : ℕ) * cwG θ * cwB θ
      = 10 ^ (4 : ℕ) * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2
          / (Real.cos θ) ^ (6 : ℕ) := by
    simp only [cwG, cwB]
    field_simp
  rw [hleft, hright]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (Real.cos θ) ^ (8 : ℕ))
    (by positivity : (0 : ℝ) < (Real.cos θ) ^ (6 : ℕ))]
  -- clear the `sin(2θ)^{-η}` and the denominators
  have h2 : 2500 * Real.sin (2 * θ) ^ 2
        * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2
      ≤ 10 ^ (4 : ℕ) * (Real.cos θ) ^ 2
        * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2 :=
    mul_le_mul_of_nonneg_right hmul (by positivity)
  have h2b : 2500 * Real.sin (2 * θ) ^ 2
        * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2 * (Real.cos θ) ^ (6 : ℕ)
      ≤ 10 ^ (4 : ℕ) * (Real.cos θ) ^ 2
        * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2 * (Real.cos θ) ^ (6 : ℕ) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h3 : 10 ^ (4 : ℕ) * (Real.cos θ) ^ 2
        * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2 * (Real.cos θ) ^ (6 : ℕ)
      = 10 ^ (4 : ℕ) * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) ^ 2
        * (Real.cos θ) ^ (8 : ℕ) := by ring
  linarith [h2b, h3]

end Work.FTS_EllLimOK.PkgJets
