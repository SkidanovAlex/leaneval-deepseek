import Mathlib
import Submission.Work.SSS.hornCok_d_faceLift_chain
import Submission.Work.SSS.ezLinSnd_map_fst
import Submission.Work.SSS.iotaTLift_last_eq
import Submission.Work.SSS.serreE1Snd

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- **The `i`-th face term of `iotaTLin` in terms of the full lifted shuffle chain.**

`iotaTLinFace p hfib s t b σ h i z` is obtained by first restricting the Eilenberg–Zilber lift
`ezSimplex_σ` to the `i`-th face `δ i ⊗ₘ 𝟙` and then applying it to the shuffle chain of the
fundamental `s`-simplex `stdIdSimplex s`.  Since the lift is the composite
`(δ i ⊗ₘ 𝟙) ≫ ezSimplex_σ`, and since the shuffle chain is natural in the first variable
(`ezLinSnd_map_fst`), this equals applying the *full* lift `ezSimplex_σ` to the shuffle chain of the
`i`-th face `(Δ[s+1]).δ i (stdIdSimplex (s+1))` of the fundamental `(s+1)`-simplex. -/
theorem iotaTLinFace_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (i : Fin (s+2)) (z : (Work.SSS.fibreCC p b).X t) :
    Work.SSS.iotaTLinFace p hfib s t b σ h i z
      = (ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) (s+1) b σ h)).f (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.ezLinSnd s t
            (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
            (Work.SSS.sSing (Work.StemsB.fibre p b))
            ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}).δ i
              (Work.SSS.stdIdSimplex (s+1)))))) z) := by
  have hgen : (ModuleCat.Hom.hom ((Work.SSS.sCCMap
        ((SSet.stdSimplex.δ (n := s) i) ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))).f (s+t)))
        ((ModuleCat.Hom.hom (Work.SSS.ezLinSnd s t
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex s))) z)
      = (ModuleCat.Hom.hom (Work.SSS.ezLinSnd s t
          (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b))
          ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}).δ i
            (Work.SSS.stdIdSimplex (s+1))))) z := by
    have hh := Work.SSS.ezLinSnd_map_fst s t (SSet.stdSimplex.δ (n := s) i)
      (Work.SSS.stdIdSimplex s) z
    rw [← Work.SSS.delta_stdIdSimplex_eq s i] at hh
    exact hh
  rw [Work.SSS.iotaTLinFace, Work.SSS.ezFaceLift]
  rw [Work.SSS.sCCMap_comp', HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hgen]

end Work.SSS
