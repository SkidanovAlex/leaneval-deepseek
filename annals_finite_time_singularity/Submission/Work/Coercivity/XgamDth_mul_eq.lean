/-
# The `D_θ`-blocks multiply to the weight `ργ`

`XgamDth α f = D_θ f · W` is the `D_θ`-block of the `ℋ¹` integrand, where
`W = w · w_θ` and `w_θ(θ) = sin(2θ)^{-γ/2}`.  On `Iθ`,
`XgamDth α a · XgamDth α b = (D_θ a · D_θ b) · ργ`
with `ργ = w²·sin(2θ)^{-γ} = lamGam α`, because the two `w`-factors give `w²` and the two
`sin(2θ)^{-γ/2}`-factors give `sin(2θ)^{-γ}` (the `rpow_neg_sq` identity, valid for
`sin(2θ) ≥ 0`, which holds on `Iθ`).  Note that at the endpoints of `Iθ`, where
`sin(2θ) = 0`, both sides still agree because of the explicit `D_θ`-factors
`sin(2θ)` and the quadratic `w²`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.rpow_neg_sq

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

/-- The squared angular weight: `w_θ(θ)² = sin(2θ)^{-γ}` for `θ ∈ Iθ`. -/
theorem wTheta_mul_self (α θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.wTheta α θ * Spaces.wTheta α θ = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h := rpow_neg_sq (Real.sin (2 * θ)) (Spaces.gam α) hs0
  rw [Spaces.wTheta, ← sq]
  exact h

/-- The product weight `W = w·w_θ` of the `D_θ`-blocks squares to the `D_θ`-pairing
weight `ργ = lamGam α`. -/
theorem Wt_mul_self (α z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.Wt α z θ * Spaces.Wt α z θ = lamGam α z θ := by
  rw [Spaces.Wt, lamGam]
  rw [show (Spaces.w z * Spaces.wTheta α θ) * (Spaces.w z * Spaces.wTheta α θ)
      = (Spaces.w z) ^ 2 * (Spaces.wTheta α θ * Spaces.wTheta α θ) by ring]
  rw [wTheta_mul_self α θ hθ]

/-- The two `D_θ`-blocks multiply to `D_θ a · D_θ b · ργ`. -/
theorem XgamDth_mul_eq (α : ℝ) (a b : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    XgamDth α a z θ * XgamDth α b z θ
      = Spaces.Dth a z θ * Spaces.Dth b z θ * lamGam α z θ := by
  simp only [XgamDth]
  calc (Spaces.Dth a z θ * Spaces.Wt α z θ) * (Spaces.Dth b z θ * Spaces.Wt α z θ)
      = (Spaces.Dth a z θ * Spaces.Dth b z θ) * (Spaces.Wt α z θ * Spaces.Wt α z θ) := by
        ring
    _ = (Spaces.Dth a z θ * Spaces.Dth b z θ) * lamGam α z θ := by
        rw [Wt_mul_self α z θ hθ]
    _ = Spaces.Dth a z θ * Spaces.Dth b z θ * lamGam α z θ := by ring

end Work.Coercivity
