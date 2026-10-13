import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Honest.I4IntervalIdentity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the `I₄` slice objects on a closed sub-interval

Given `Φ` of class `C²` on the open quadrant `(0, π/2)` and `0 < δ ≤ θ₁ < π/2`, all five
slice objects of the honest `I₄` estimate — `Φ`, `ψ = Φ/cos θ`, `ψ'`, the weight
`σ = sin(2θ)^{-99/100}` and the coefficient `Σ = (1-η)cos²θ + (3+η)sin²θ` — are continuous
on the closed interval `[δ, θ₁]`.

The substance is that `[δ, θ₁]` is a compact sub-interval of the *open* quadrant, so
`Φ ∈ C²` on a neighbourhood of it; the only non-trivial component is the derivative of the
quotient `ψ`, which is `ContinuousOn` by `continuousOn_deriv_I4psi`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

theorem I4CrossCont (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    ContinuousOn Φ (Set.Icc δ θ₁) ∧ ContinuousOn (I4psi Φ) (Set.Icc δ θ₁)
      ∧ ContinuousOn (deriv (I4psi Φ)) (Set.Icc δ θ₁)
      ∧ ContinuousOn I4sig (Set.Icc δ θ₁) ∧ ContinuousOn I4Sig (Set.Icc δ θ₁) := by
  -- `[δ, θ₁]` sits inside the open quadrant, where `Φ` is `C²`
  have hIcc : Set.Icc δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hδ hx.1, lt_of_le_of_lt hx.2 hθ₁⟩
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Icc δ θ₁) :=
    Real.continuous_cos.continuousOn
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Icc δ θ₁) :=
    Real.continuous_sin.continuousOn
  refine ⟨hsm.continuousOn.mono hIcc, ?_, ?_, continuousOn_I4sig hδ hθ₁, ?_⟩
  · exact (contDiffOn_I4psi Φ hsm).continuousOn.mono hIcc
  · exact continuousOn_deriv_I4psi Φ hsm hIcc
  · change ContinuousOn
      (fun θ : ℝ => (1 - 99 / 100) * (Real.cos θ) ^ 2 + (3 + 99 / 100) * (Real.sin θ) ^ 2)
      (Set.Icc δ θ₁)
    exact (continuousOn_const.mul (hcos.pow 2)).add (continuousOn_const.mul (hsin.pow 2))

end Work.FTS.EllipticEst.Honest
