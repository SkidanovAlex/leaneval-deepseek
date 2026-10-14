import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.ThetaUnifPz
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
-- ===== merged: Submission.Work.FTS.EpsEngine.ClassCStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaUnifFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The family-uniform angular flatness**: the two `ε`-`δ` conditions of `ThetaUnif`, uniformly
in `z > 0` and in the curve parameter `s ∈ Icc 0 T`, for every slot `a + b ≤ k`. -/
structure ThetaUnifFam (α : ℝ) (k : ℕ) (T : ℝ) (H : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- angular vanishing at `θ → 0⁺`, uniformly in `z` and in `s`. -/
  t0 : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ → ∀ z : ℝ, 0 < z →
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ a b : ℕ, a + b ≤ k →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (H s) z θ) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → (π/2)⁻`, uniformly in `z` and in `s`. -/
  t1 : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 → Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ a b : ℕ, a + b ≤ k →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (H s) z θ) ^ 2 ≤ ε'

/-- The family form implies the memberwise form. -/
theorem ThetaUnifFam.pointwise {α : ℝ} {k : ℕ} {T : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (h : ThetaUnifFam α k T H) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ThetaUnif α k (H s) :=
  ⟨fun a b hab ε' hε' => by
      obtain ⟨δ, hδ, hp⟩ := h.t0 ε' hε'
      exact ⟨δ, hδ, fun θ hθ0 hθδ z hz => hp θ hθ0 hθδ z hz s hs a b hab⟩,
   fun a b hab ε' hε' => by
      obtain ⟨δ, hδ, hp⟩ := h.t1 ε' hε'
      exact ⟨δ, hδ, fun θ hθ2 hθδ z hz => hp θ hθ2 hθδ z hz s hs a b hab⟩⟩


end Work.FTS.EpsEngine
end
