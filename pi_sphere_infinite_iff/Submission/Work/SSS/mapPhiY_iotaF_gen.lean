import Mathlib
import Submission.Work.SSS.serreE1CruxD1
import Submission.Work.SSS.iotaT_eq_iotaTLin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `Work.SSS.mapPhiY` on the Eilenberg-Zilber chain `Work.SSS.iotaF` of a σ-piece: the value on a
chain `z` of the fibre is the second projection of `Work.SSS.iotaTLin`, projected to the graded
piece `grF`.

Route: `Work.SSS.iotaF = iotaT ≫ pieceπOf` (elementwise `Work.SSS.iotaF_gen`), and the degreewise
`Work.SSS.thetaPhi_mapPhiY_apply_f` gives `pieceπ ≫ mapPhiY = sCCMap (sndToR) ≫ grFι`; substitute
`Work.SSS.iotaT_eq_iotaTLin` for the value of `iotaT` on `z` (that is
`(sCCMap (ezSimplex ...)) (ezElem p s t b z)`, which is exactly
`Work.SSS.iotaTLin p hfib s t b (sigHat σ) h z` by definition). -/
theorem mapPhiY_iotaF_gen (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s + 1))
    (h : Work.SSS.sigmaVert (Work.SSS.sigHat σ) = b) (z : (Work.SSS.fibreCC p b).X t) :
    (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) (s + 1) σ).f ((s+1)+t)))
        ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) (s + 1) b (Work.SSS.sigHat σ) h t)) z)
      = (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (s + 1)).f ((s+1)+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f
            ((s+1)+t))) (Work.SSS.iotaTLin p hfib s t b (Work.SSS.sigHat σ) h z)) := by
  -- `iotaF` is `iotaT ≫ pieceπOf`, and `iotaT` on `z` is `iotaTLin` by definition.
  have hiota : (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (s + 1) b (Work.SSS.sigHat σ) h t)) z
      = ModuleCat.Hom.hom
          ((Work.SSS.pieceπOf (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).f ((s+1)+t))
          (Work.SSS.iotaTLin p hfib s t b (Work.SSS.sigHat σ) h z) := by
    simp only [Work.SSS.iotaF]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, Work.SSS.iotaT_eq_iotaTLin]
  rw [hiota]
  -- `pieceπOf (sSingP p) (sigHat σ)` is `pieceπ (sSingP p) (s+1) σ` by definition, for which
  -- `thetaPhi_mapPhiY_apply_f` gives the desired degreewise identity.
  have hkey : (Work.SSS.pieceπOf (Work.SSS.sSingP p) (Work.SSS.sigHat σ)).f ((s+1)+t) ≫
      (Work.SSS.mapPhiY (Work.SSS.sSingP p) (s+1) σ).f ((s+1)+t)
      = (Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t) ≫
        (Work.SSS.grFι (Work.SSS.sSingP p) (s+1)).f ((s+1)+t) :=
    Work.SSS.thetaPhi_mapPhiY_apply_f (Work.SSS.sSingP p) (s+1) ((s+1)+t) σ
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hkey]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end Work.SSS
