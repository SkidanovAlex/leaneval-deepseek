/-
Copyright: work module for the Elgindi finite-time singularity project.

# Dilation invariance of the weak level-`2` class in the radial variable

The target of this file is `Work.H2W.PsiSlices.weakPos2_dilate`: for `0 < lam` the dilated datum
`(F(lam·,·), Ψ(lam·,·))` of a member of the weak class `Work.FTS.EllipticEst.WeakPos2 α` is again
a member.  The class has eight conjuncts, and they split as follows.

* **The equation.**  `bslOp α` is an Euler-type operator: `bslOp α (Ψ(lam·)) (z) = bslOp α Ψ (lam z)`
  (`DilateOps.bslOp_dilate`), because `pzIter n (Ψ(lam·)) = lam^n · (pzIter n Ψ)(lam·)`
  (unconditional, since the chain rule for `deriv` holds with no differentiability hypothesis:
  `DilateOps.dilate_pzIter`) and the `α = 0` angular part is *definitionally* dilation invariant.
* **The boundary values** at `θ = 0, π/2` and the **decay** at `z → ∞` are evaluated at the dilated
  point / composed with the dilation.
* **The two moment conditions** `OrthCond` are integrals in `θ` at *fixed* `z` (`Fstar`), so they
  transfer verbatim (`DilateOps.OrthCond_dilate`).
* **The smoothness on the open quadrant** is precomposition with the smooth self-map
  `(z,θ) ↦ (lam z, θ)` of the half-strip into itself
  (`Work.H2W.PsiSlices.contDiffOn_uncurry_dilate`).
* **`HkMem α 2 F`** is the only conjunct with content: `HkIntegrand` carries the weight `w z`,
  so the terms of the dilated integrand differ from the terms of the integrand at `lam z` by the
  ratio `w z / w (lam z)`, bounded by `max(lam²,1)`; then `ζ = lam z` is a substitution of the
  half-line (and `w 0 = 0` makes `z = 0` harmless).  This is
  `Work.H2W.PsiSlices.HkMem_dilate`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.H2W.PsiSlices.DilateOps
import Submission.Work.H2W.PsiSlices.contDiffOn_uncurry_dilate
import Submission.Work.H2W.PsiSlices.HkMem_dilate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

set_option autoImplicit false

/-- **Dilation invariance of the weak class in the radial variable.**  For `0 < lam`, the dilated
datum `(F(lam·,·), Ψ(lam·,·))` of a member of `WeakPos2` is again a member: the elliptic operator
`bslOp α` is an Euler-type operator and is invariant under `z ↦ lam·z`
(`z²∂_z²(Ψ(lam·)) (z) = (lam·z)²∂_z²Ψ(lam·z)`, `z∂_z(Ψ(lam·))(z) = lam·z·∂_zΨ(lam·z)`), the
boundary values and the decay in `z` are preserved, the two angular moment conditions are
*fixed-`z`* integrals and so transfer verbatim, and `HkMem α 2 (F(lam·,·))` transfers by the weight
comparison `w(ζ/lam) ≤ max(lam²,1)·w(ζ)` (`Work.Spaces.w`) together with the substitution
`ζ = lam·z` (with `w 0 = 0` making `z = 0` harmless).  This is the structural input of the
covariance reduction: it shows the conclusion of `pzIterSliceIntegrable` needs only be proved at
the single point `z = 1`. -/
theorem weakPos2_dilate {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.WeakPos2 α F Ψ) {lam : ℝ} (hlam : 0 < lam) :
    Work.FTS.EllipticEst.WeakPos2 α (fun z θ => F (lam * z) θ)
      (fun z θ => Ψ (lam * z) θ) := by
  obtain ⟨hEq, h0, hp2, hdec, hOF, hOP, hsm, hmF⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ0 hθ1
    rw [show Work.Elliptic.bslOp α (fun z θ => Ψ (lam * z) θ) z θ
          = Work.Elliptic.bslOp α Ψ (lam * z) θ from
        congrFun (congrFun (bslOp_dilate α lam Ψ) z) θ]
    exact hEq (lam * z) (mul_pos hlam hz) θ hθ0 hθ1
  · intro z
    exact h0 (lam * z)
  · intro z
    exact hp2 (lam * z)
  · intro θ hθ
    exact (hdec θ hθ).comp (Filter.tendsto_id.const_mul_atTop hlam)
  · exact OrthCond_dilate F lam hOF
  · exact OrthCond_dilate Ψ lam hOP
  · exact contDiffOn_uncurry_dilate Ψ hlam hsm
  · exact HkMem_dilate hmF hlam

end Work.H2W.PsiSlices
