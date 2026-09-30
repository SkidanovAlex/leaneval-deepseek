import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.lorentz_hypOfUHS_self

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The derivative of the Möbius action on the upper half space model

`mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` is the action of a Lorentz matrix `A` on the upper half
space model of hyperbolic 4-space, obtained by conjugating the linear action of `A` on the ambient
Lorentz space `ℝ^{1,4}`— restricted to the hyperboloid — with the upper half space chart
`hypOfUHS` and its inverse `uhsOfHyp`.

This file computes its Fréchet derivative: for `q` in the upper half space (`0 < q 3`) and `A` in
the (orthochronous) Lorentz group, the derivative of `mobius A` at `q` is the composite

`dUhsOfHyp Q ∘ A ∘ dHypOfUHS q`, where `Q = A *ᵥ hypOfUHS q`,

i.e. the explicit chart differential `dHypOfUHS q`, followed by the linear action of `A`, followed
by the explicit differential `dUhsOfHyp Q` of the inverse chart.  In coordinates, for a tangent
vector `v`,

`fderiv ℝ (mobius A) q v = dUhsOfHyp (A *ᵥ hypOfUHS q) (A *ᵥ dHypOfUHS q v)`.

The proof is the chain rule `HasFDerivAt.comp` applied to the two explicit differentiability
results `hasFDerivAt_hypOfUHS` and `hasFDerivAt_uhsOfHyp`.  The only geometric input is that `A`
carries the upper sheet into itself (`mulVec_mem_upperSheet`), so that the intermediate point
`Q = A *ᵥ hypOfUHS q` again has positive height `Q₄ − Q₃ > 0` and `uhsOfHyp` is differentiable
there.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix
open Matrix

/-- **The derivative of the Möbius action.**  For a Lorentz matrix `A` and a point `q` of the
upper half space, the Fréchet derivative of `mobius A` at `q` applied to a tangent vector `v` is
`dUhsOfHyp (A *ᵥ hypOfUHS q) (A *ᵥ (dHypOfUHS q v))`: the explicit differential of the chart
`hypOfUHS`, the linear action of `A` on the ambient Lorentz space, and the explicit differential
of the inverse chart `uhsOfHyp` at the image point. -/
theorem fderiv_mobius_apply {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) {q : E4}
    (hq : 0 < q 3) (v : E4) :
    fderiv ℝ (mobius A) q v = dUhsOfHyp (A.mulVec (hypOfUHS q)) (A.mulVec (dHypOfUHS q v)) := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  -- `hypOfUHS q` lies on the hyperboloid, and so does its image `Q = A *ᵥ hypOfUHS q`
  have hP : hypOfUHS q ∈ upperSheet := ⟨lorentz_hypOfUHS_self hq3, hypOfUHS_four_pos hq⟩
  have hQ : A.mulVec (hypOfUHS q) ∈ upperSheet := mulVec_mem_upperSheet hA hP
  -- hence the height of `Q` does not vanish, and `uhsOfHyp` is differentiable at `Q`
  have hδ : (A.mulVec (hypOfUHS q)) 4 - (A.mulVec (hypOfUHS q)) 3 ≠ 0 :=
    ne_of_gt (upperSheet_four_sub_three_pos hQ)
  -- chain rule: `mobius A = uhsOfHyp ∘ (q ↦ A *ᵥ hypOfUHS q)`
  have h1 : HasFDerivAt (fun x : E4 => A.mulVec (hypOfUHS x))
      ((Matrix.mulVecLin A).toContinuousLinearMap.comp (dHypOfUHS q)) q :=
    (ContinuousLinearMap.hasFDerivAt ((Matrix.mulVecLin A).toContinuousLinearMap)
      (x := hypOfUHS q)).comp q (hasFDerivAt_hypOfUHS hq3)
  have h2 : HasFDerivAt uhsOfHyp (dUhsOfHyp (A.mulVec (hypOfUHS q))) (A.mulVec (hypOfUHS q)) :=
    hasFDerivAt_uhsOfHyp hδ
  have hcomp := h2.comp q h1
  have hf : mobius A = uhsOfHyp ∘ (fun x : E4 => A.mulVec (hypOfUHS x)) := rfl
  rw [hf, hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]

end Work.HypModel
