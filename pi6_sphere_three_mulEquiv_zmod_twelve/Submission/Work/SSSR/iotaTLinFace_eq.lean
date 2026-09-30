import Mathlib
import Submission.Work.SSSR.hornCok_d_faceLift_chain
import Submission.Work.SSSR.ezLinSnd_map_fst
import Submission.Work.SSSR.iotaTLift_last_eq
import Submission.Work.SSSR.serreE1Snd
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- **The `i`-th face term of `iotaTLin` in terms of the full lifted shuffle chain.**

`iotaTLinFace p hfib s t b σ h i z` is obtained by first restricting the Eilenberg–Zilber lift
`ezSimplex_σ` to the `i`-th face `δ i ⊗ₘ 𝟙` and then applying it to the shuffle chain of the
fundamental `s`-simplex `stdIdSimplex s`.  Since the lift is the composite
`(δ i ⊗ₘ 𝟙) ≫ ezSimplex_σ`, and since the shuffle chain is natural in the first variable
(`ezLinSnd_map_fst`), this equals applying the *full* lift `ezSimplex_σ` to the shuffle chain of the
`i`-th face `(Δ[s+1]).δ i (stdIdSimplex (s+1))` of the fundamental `(s+1)`-simplex. -/
theorem iotaTLinFace_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (i : Fin (s+2)) (z : (Work.SSSR.fibreCC p b).X t) :
    Work.SSSR.iotaTLinFace p hfib s t b σ h i z
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h)).f (s+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.ezLinSnd s t
            (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
            ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}).δ i
              (Work.SSSR.stdIdSimplex (s+1)))))) z) := by
  have hgen : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
        ((SSet.stdSimplex.δ (n := s) i) ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))).f (s+t)))
        ((ModuleCat.Hom.hom (Work.SSSR.ezLinSnd s t
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex s))) z)
      = (ModuleCat.Hom.hom (Work.SSSR.ezLinSnd s t
          (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}).δ i
            (Work.SSSR.stdIdSimplex (s+1))))) z := by
    have hh := Work.SSSR.ezLinSnd_map_fst s t (SSet.stdSimplex.δ (n := s) i)
      (Work.SSSR.stdIdSimplex s) z
    rw [← Work.SSSR.delta_stdIdSimplex_eq s i] at hh
    exact hh
  rw [Work.SSSR.iotaTLinFace, Work.SSSR.ezFaceLift]
  rw [Work.SSSR.sCCMap_comp', HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hgen]

end Work.SSSR
