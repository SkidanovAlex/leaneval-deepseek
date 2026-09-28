import Mathlib
import Submission.Work.SSS.serreE1CruxDefs
import Submission.Work.SSS.sndToR_iotaTLinFace

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `i`-th face term of the lifted Eilenberg–Zilber chain, in terms of the face restriction
`Work.SSS.faceRestr` and the face inclusion `Work.SSS.pullFaceIncl`. -/
theorem iotaTLinFace_eq_faceRestr (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (i : Fin (s + 2)) (z : (Work.SSS.fibreCC p b).X t) :
    Work.SSS.iotaTLinFace p hfib s t b σ h i z
      = (ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceRestr p hfib s b σ h i ≫
            Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ i)).f (s + t)))
        (Work.SSS.ezElem p s t b z) := by
  -- `iotaTLinFace` is by definition the `ezFaceLift`-push-forward of the shuffle chain, which is
  -- by definition `ezElem`; and `ezFaceLift` is the face restriction followed by the face
  -- inclusion (`Work.SSS.ezFaceLift_eq_faceRestr_aux`).
  rw [show Work.SSS.iotaTLinFace p hfib s t b σ h i z
        = (ModuleCat.Hom.hom ((Work.SSS.sCCMap
            (Work.SSS.ezFaceLift p hfib s b σ h i)).f (s + t)))
            (Work.SSS.ezElem p s t b z) from rfl]
  rw [Work.SSS.ezFaceLift_eq_faceRestr_aux p hfib s b σ h i]

end Work.SSS
