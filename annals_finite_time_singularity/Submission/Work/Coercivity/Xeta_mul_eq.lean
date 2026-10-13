import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.H1IPAddDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The pointwise identity `Xeta a · Xeta b = a · b · lamEta` on the angular domain
`Iθ = [0, π/2]`: the square of the `η`-weight `w/√(sin 2θ⁽η⁾)` reproduces the weight
`lamEta = w²·sin(2θ)^(-η)`.  This is what lets the `ℋ¹` pairing `∫ a·b·ρη` be rewritten
as the `L²` pairing `∫ Xeta a · Xeta b` of the weighted blocks. -/
theorem Xeta_mul_eq (a b : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Xeta a z θ * Xeta b z θ = a z θ * b z θ * lamEta z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : (Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2 = Real.sin (2 * θ) ^ Spaces.eta := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  have hkey : (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2
      = Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-Spaces.eta) := by
    rw [div_pow, hsq, Real.rpow_neg hs]
    ring
  rw [Xeta, Xeta, lamEta]
  rw [← hkey]
  ring

end Work.Coercivity
