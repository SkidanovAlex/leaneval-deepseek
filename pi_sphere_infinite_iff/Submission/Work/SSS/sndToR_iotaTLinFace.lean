import Mathlib
import Submission.Work.SSS.serreE1CruxDefs
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.iotaTLinFace_eq

/-!
# The face terms of the boundary of the lifted `ι_σ`-chain

This file proves `Work.SSS.sndToR_iotaTLinFace`: for a nondegenerate `(s+1)`-simplex `σ` of
`Sing B`, a chain `z` of the fibre over `b = sigHat σ (v₀)` and a face index `i : Fin (s+2)`, the
`i`-th face term `iotaTLinFace` of the boundary of the lifted Eilenberg–Zilber chain `iotaTLin`,
pushed forward by the second projection `sndToR (sSingP p) σ` into the Serre filtration, is the
`incF (Fc p) s`-image of the `i`-th face chain `faceB`.

The proof is a short chain of rewrites:

* `ezFaceLift` is, by `faceLift_pullFaceIncl`, the composite `faceRestr ≫ pullFaceIncl`;
* `pullFaceIncl ≫ sndToR = faceC ≫ homOfLe` (`pullFaceIncl_sndToR_aux`);
* `sCCMap (homOfLe) = incF (serF _) s` (`sCCMap_homOfLe_serre_aux`, by `rfl`), and `Fc p` is
  definitionally `serF (sSingP p)`;
* `faceB` is *by definition* the `sCCMap (faceRestr ≫ faceC)`-image of `ezElem`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

/-- The face inclusions composed with the second projection into the filtration. -/
lemma pullFaceIncl_sndToR_aux {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (y : nIndex Y (s+1)) (i : Fin (s+2)) :
    pullFaceIncl f (nIndexSigma Y (s+1) y) i ≫ sndToR f y
      = sndToSerre f (SSet.stdSimplex.δ i ≫ nIndexSigma Y (s+1) y) (s+1)
          ((sndToSerre_range f).1 (SSet.stdSimplex.δ i ≫ nIndexSigma Y (s+1) y))
        ≫ Subfunctor.homOfLe (Work.StemsB.serreSubcomplex_mono f (Nat.le_succ (s+1))) := by
  apply (cancel_mono (Work.StemsB.serreSubcomplex f (s+1+1)).ι).1
  simp only [Category.assoc, Subfunctor.homOfLe_ι, sndToSerre_ι, sndToR_ι, pullFaceIncl_snd]

/-- The inclusion `R_{s+1} ⊆ R_{s+2}` as a chain map is `incF` of the Serre filtration. -/
lemma sCCMap_homOfLe_serre_aux {X Y : SSet.{0}} (f : X ⟶ Y) (s : ℕ) :
    sCCMap (Subfunctor.homOfLe (Work.StemsB.serreSubcomplex_mono f (Nat.le_succ (s+1))))
      = incF (serF f) s := rfl

/-- The `i`-th face of the Eilenberg–Zilber lift is the `i`-th face restriction followed by the
face inclusion. -/
lemma ezFaceLift_eq_faceRestr_aux {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (i : Fin (s + 2)) :
    ezFaceLift p hfib s b σ h i = faceRestr p hfib s b σ h i ≫ pullFaceIncl (sSingP p) σ i :=
  (faceLift_pullFaceIncl (sSingP p) σ
    (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) (s + 1) b σ h)
    (ezSimplex_fst (liftFam p hfib) (liftFam_proj p hfib) (s + 1) b σ h) i).symm

/-- **The face terms of the boundary of the lifted `ι_σ`-chain.**  For a nondegenerate `(s+1)`-simplex
`σ` of `Sing B` (with `sigHat σ = nIndexSigma (sSing B) (s+1) σ` the corresponding map
`Δ[s+1] ⟶ Sing B` and `b = sigHat σ (v₀)`), a chain `z` of the fibre over `b`, and `i : Fin (s+2)`,
the `i`-th face term `iotaTLinFace` of the boundary of the lifted Eilenberg–Zilber chain
`iotaTLin` (which lies in `C(T_{sigHat σ})`), pushed forward by the second projection
`sndToR (sSingP p) σ : T_{sigHat σ} ⟶ R_{s+2}`, is the `incF (Fc p) s`-image of the `i`-th face
chain `faceB` (which lies in `C(R_{s+1})`).

Route.  `Work.SSS.iotaTLinFace` is, by definition, `(sCCMap (ezFaceLift)) (ezElem)` where
`ezFaceLift = (δ i ⊗ 𝟙) ≫ ezSimplex_σ`; the auxiliary lemma `iotaTLinFace_eq_faceRestr` rewrites
this as `(sCCMap (faceRestr ≫ pullFaceIncl)) (ezElem)`, where `faceRestr` is `Work.SSS.faceRestr`
(the Mathlib-style `faceLift` of `ezSimplex_σ`) and `pullFaceIncl` is the face inclusion.  Then
```
(sCCMap (sndToR f σ)).f (s+t) ((sCCMap (faceRestr ≫ pullFaceIncl)).f (s+t) e)
  = (sCCMap ((faceRestr ≫ pullFaceIncl) ≫ sndToR f σ)).f (s+t) e          -- comp_f
  = (sCCMap (faceRestr ≫ (faceC ≫ homOfLe))).f (s+t) e                    -- pullFaceIncl_sndToR
  = (sCCMap homOfLe).f (s+t) ((sCCMap (faceRestr ≫ faceC)).f (s+t) e)     -- comp_f
  = (incF (Fc p) s).f (s+t) (faceB p hfib s t b (sigHat σ) h z i)
```
the last step because `sCCMap (Subfunctor.homOfLe (StemsB.serreSubcomplex_mono f (Nat.le_succ (s+1))))
= incF (serF f) s` holds by `rfl`, and `faceB` is *by definition*
`(sCCMap (faceRestr ≫ faceC)).f (s+t) (ezElem)`. -/
theorem sndToR_iotaTLinFace {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s + 1))
    (h : Work.SSS.sigmaVert (Work.SSS.sigHat σ) = b) (i : Fin (s + 2))
    (z : (Work.SSS.fibreCC p b).X t) :
    (ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f (s + t)))
        (Work.SSS.iotaTLinFace p hfib s t b (Work.SSS.sigHat σ) h i z)
      = (ModuleCat.Hom.hom ((Work.SSS.incF (Work.SSS.Fc p) s).f (s + t)))
          (Work.SSS.faceB p hfib s t b (Work.SSS.sigHat σ) h z i) := by
  have hcomp : sCCMap (ezFaceLift p hfib s b (sigHat σ) h i) ≫ sCCMap (sndToR (sSingP p) σ)
      = sCCMap (faceRestr p hfib s b (sigHat σ) h i ≫ faceC p s (sigHat σ) i)
        ≫ incF (Fc p) s := by
    conv_lhs => rw [ezFaceLift_eq_faceRestr_aux p hfib s b (sigHat σ) h i]
    conv_lhs => rw [sCCMap_comp']
    conv_lhs => rw [Category.assoc]
    conv_lhs => rw [← sCCMap_comp']
    conv_lhs => rw [pullFaceIncl_sndToR_aux (sSingP p) σ i]
    conv_lhs => rw [sCCMap_comp']
    conv_lhs => rw [sCCMap_homOfLe_serre_aux (sSingP p) s]
    conv_lhs => rw [← Category.assoc]
    conv_lhs => rw [← sCCMap_comp']
    rfl
  rw [show iotaTLinFace p hfib s t b (sigHat σ) h i z
        = (ModuleCat.Hom.hom ((sCCMap (ezFaceLift p hfib s b (sigHat σ) h i)).f (s + t)))
            (ezElem p s t b z) from rfl]
  rw [show faceB p hfib s t b (sigHat σ) h z i
        = (ModuleCat.Hom.hom ((sCCMap (faceRestr p hfib s b (sigHat σ) h i
              ≫ faceC p s (sigHat σ) i)).f (s + t)))
            (ezElem p s t b z) from rfl]
  rw [chainMap_comp_apply (sCCMap (ezFaceLift p hfib s b (sigHat σ) h i))
        (sCCMap (sndToR (sSingP p) σ)) (ezElem p s t b z)]
  rw [hcomp]
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end

end Work.SSS
