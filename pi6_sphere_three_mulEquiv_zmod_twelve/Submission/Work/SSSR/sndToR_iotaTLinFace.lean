import Mathlib
import Submission.Work.SSSR.serreE1CruxDefs
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.iotaTLinFace_eq
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

/-- The face inclusions composed with the second projection into the filtration. -/
lemma pullFaceIncl_sndToR_aux {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (y : nIndex Y (s+1)) (i : Fin (s+2)) :
    pullFaceIncl f (nIndexSigma Y (s+1) y) i ≫ sndToR f y
      = sndToSerre f (SSet.stdSimplex.δ i ≫ nIndexSigma Y (s+1) y) (s+1)
          ((sndToSerre_range f).1 (SSet.stdSimplex.δ i ≫ nIndexSigma Y (s+1) y))
        ≫ Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (s+1))) := by
  apply (cancel_mono (Work.SSSR.StemsB.serreSubcomplex f (s+1+1)).ι).1
  simp only [Category.assoc, Subfunctor.homOfLe_ι, sndToSerre_ι, sndToR_ι, pullFaceIncl_snd]

/-- The inclusion `R_{s+1} ⊆ R_{s+2}` as a chain map is `incF` of the Serre filtration. -/
lemma sCCMap_homOfLe_serre_aux {X Y : SSet.{0}} (f : X ⟶ Y) (s : ℕ) :
    sCCMap R (Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (s+1))))
      = incF (serF R f) s := rfl

/-- The `i`-th face of the Eilenberg–Zilber lift is the `i`-th face restriction followed by the
face inclusion. -/
lemma ezFaceLift_eq_faceRestr_aux {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
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

Route.  `Work.SSSR.iotaTLinFace` is, by definition, `(sCCMap R (ezFaceLift)) (ezElem)` where
`ezFaceLift = (δ i ⊗ 𝟙) ≫ ezSimplex_σ`; the auxiliary lemma `iotaTLinFace_eq_faceRestr` rewrites
this as `(sCCMap R (faceRestr ≫ pullFaceIncl)) (ezElem)`, where `faceRestr` is `Work.SSSR.faceRestr`
(the Mathlib-style `faceLift` of `ezSimplex_σ`) and `pullFaceIncl` is the face inclusion.  Then
```
(sCCMap R (sndToR f σ)).f (s+t) ((sCCMap R (faceRestr ≫ pullFaceIncl)).f (s+t) e)
  = (sCCMap R ((faceRestr ≫ pullFaceIncl) ≫ sndToR f σ)).f (s+t) e          -- comp_f
  = (sCCMap R (faceRestr ≫ (faceC ≫ homOfLe))).f (s+t) e                    -- pullFaceIncl_sndToR
  = (sCCMap R homOfLe).f (s+t) ((sCCMap R (faceRestr ≫ faceC)).f (s+t) e)     -- comp_f
  = (incF (Fc p) s).f (s+t) (faceB p hfib s t b (sigHat σ) h z i)
```
the last step because `sCCMap R (Subfunctor.homOfLe (StemsB.serreSubcomplex_mono f (Nat.le_succ (s+1))))
= incF (serF R f) s` holds by `rfl`, and `faceB` is *by definition*
`(sCCMap R (faceRestr ≫ faceC)).f (s+t) (ezElem)`. -/
theorem sndToR_iotaTLinFace {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (h : Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) = b) (i : Fin (s + 2))
    (z : (Work.SSSR.fibreCC p b).X t) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (s + t)))
        (Work.SSSR.iotaTLinFace p hfib s t b (Work.SSSR.sigHat σ) h i z)
      = (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.Fc p) s).f (s + t)))
          (Work.SSSR.faceB p hfib s t b (Work.SSSR.sigHat σ) h z i) := by
  have hcomp : sCCMap R (ezFaceLift p hfib s b (sigHat σ) h i) ≫ sCCMap R (sndToR (sSingP p) σ)
      = sCCMap R (faceRestr p hfib s b (sigHat σ) h i ≫ faceC p s (sigHat σ) i)
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
        = (ModuleCat.Hom.hom ((sCCMap R (ezFaceLift p hfib s b (sigHat σ) h i)).f (s + t)))
            (ezElem p s t b z) from rfl]
  rw [show faceB p hfib s t b (sigHat σ) h z i
        = (ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i
              ≫ faceC p s (sigHat σ) i)).f (s + t)))
            (ezElem p s t b z) from rfl]
  rw [chainMap_comp_apply (sCCMap R (ezFaceLift p hfib s b (sigHat σ) h i))
        (sCCMap R (sndToR (sSingP p) σ)) (ezElem p s t b z)]
  rw [hcomp]
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end

end Work.SSSR
