import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_EllLimOK.IsBslSolPos_add` — additivity of the elliptic law `IsBslSolPos`

The law `IsBslSolPos α F Ψ` reads

  `∀ z > 0, ∀ θ ∈ (0, π/2), bslOp α Ψ z θ = F z θ`,  `Ψ z 0 = 0`,  `Ψ z (π/2) = 0` for `z ≥ 0`,
  `∀ θ ∈ Iθ, Ψ z θ → 0` as `z → ∞`.

Since `bslOp α` is a *linear* second order operator (`Work.Elliptic.bslOp_add`, whose only
extra hypothesis is joint `C²`-regularity of the two summands on the open quadrant), the first
clause is additive; the two Dirichlet clauses are values at `θ = 0` and `θ = π/2`, hence
additive; and the far-field decay is additive by `Filter.Tendsto.add`.

The pointwise form of the operator additivity on the open quadrant is recorded here as
`bslOp_add_of_contDiffOn` (it is the only `C²`-regularity bootstrap needed), and the open
quadrant is a neighbourhood of each of its points (`qd_mem_nhds`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Two elementary preliminaries -/

/-- The open quadrant is a neighbourhood of each of its points (`Qd` is `Ioi 0 ×ˢ Ioo 0 (π/2)`
by definition). -/
theorem qd_mem_nhds {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) :=
  (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ, hθ2⟩

/-- **Pointwise additivity of `bslOp` on the open quadrant**, from `C²`-regularity there.

This is `Work.Elliptic.bslOp_add` with the differentiability hypotheses discharged from the
`ContDiffOn` assumption on the open quadrant (where `cos θ ≠ 0` holds automatically). -/
theorem bslOp_add_of_contDiffOn {α : ℝ} {Ψ Φ : Fn}
    (hsΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd)
    (hsΦ : ContDiffOn ℝ 2 (Function.uncurry Φ) Work.Construction.Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Elliptic.bslOp α Ψ z θ + Work.Elliptic.bslOp α Φ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  exact Work.Elliptic.bslOp_add α Ψ Φ z θ hcos
    (hsΨ.contDiffAt (qd_mem_nhds hz hθ hθ2)) (hsΦ.contDiffAt (qd_mem_nhds hz hθ hθ2))

/-! ## The additivity of the law -/

/-- **`IsBslSolPos` is additive**: the sum of two solutions of the (PolarBSL) problem solves the
(PolarBSL) problem for the sum of the data.  All four clauses are handled by the corresponding
linearity: the equation by `bslOp_add_of_contDiffOn`, the two Dirichlet values by `add`, and the
far-field decay by `Filter.Tendsto.add`. -/
theorem IsBslSolPos_add {α : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (h₁ : Work.FTS.StrongGlobal.IsBslSolPos α F₁ Ψ₁)
    (h₂ : Work.FTS.StrongGlobal.IsBslSolPos α F₂ Ψ₂)
    (hs₁ : ContDiffOn ℝ 2 (Function.uncurry Ψ₁) Work.Construction.Qd)
    (hs₂ : ContDiffOn ℝ 2 (Function.uncurry Ψ₂) Work.Construction.Qd) :
    Work.FTS.StrongGlobal.IsBslSolPos α (fun z θ => F₁ z θ + F₂ z θ)
      (fun z θ => Ψ₁ z θ + Ψ₂ z θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ hθ2
    rw [bslOp_add_of_contDiffOn hs₁ hs₂ hz hθ hθ2, h₁.1 z hz θ hθ hθ2, h₂.1 z hz θ hθ hθ2]
  · intro z hz
    show Ψ₁ z 0 + Ψ₂ z 0 = 0
    rw [h₁.2.1 z hz, h₂.2.1 z hz, add_zero]
  · intro z hz
    show Ψ₁ z (π / 2) + Ψ₂ z (π / 2) = 0
    rw [h₁.2.2.1 z hz, h₂.2.2.1 z hz, add_zero]
  · intro θ hθ
    simpa using (h₁.2.2.2 θ hθ).add (h₂.2.2.2 θ hθ)

end Work.FTS_EllLimOK
