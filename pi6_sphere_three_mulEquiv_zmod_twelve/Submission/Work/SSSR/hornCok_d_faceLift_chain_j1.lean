import Mathlib
import Submission.Work.SSSR.hornCok_d_faceLift_chain
import Submission.Work.SSSR.pieceIso_lift_genC
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- **The `hpeel` input of `Work.SSSR.pieceIso_peel` for an arbitrary CHAIN.**

This is the CHAIN-level version of `Work.SSSR.hornCok_d_faceLift_j1`
(`Submission/Work/SSS/pieceIso_lift_genC.lean`): the same statement with the simplex `τ` (and its
cycle hypothesis `hτ`) replaced by an arbitrary cycle CHAIN `z`, and the EZ chain `ezGen` replaced
by its linear extension `Work.SSSR.ezLinSnd`.  It is obtained from the PROVED
`Work.SSSR.hornCok_d_faceLift_chain` (whose conclusion is the same identity at the degrees
`(P+1)+t → P+t`) by the degree `castElem` bookkeeping already carried out in
`Work.SSSR.hornCok_d_faceLift_j1`: copy that proof verbatim (lines ~60-143 of
`Submission/Work/SSS/pieceIso_lift_genC.lean`), replacing `hornCok_d_faceLift` by
`hornCok_d_faceLift_chain`, `ezGen _ _ … τ` by `ezLinSnd _ _ … z`, and `τ`, `hτ` by `z`, `hz`. -/
lemma hornCok_d_faceLift_chain_j1 {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSSR.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f ((P+1)+t)))
            (Work.SSSR.ezLinSnd (P+1) t
              (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (P+1)) z)))
      = (-1 : ℤ)^(P+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1)))
                (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                  (by omega : P+t = (P+1)+t-1)
                  ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
                    (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                  (Work.SSSR.ezLinSnd P t
                    (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                    (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z))))) := by
  have h := Work.SSSR.hornCok_d_faceLift_chain p hfib P t b σ ez hez z hz
  have he : P+t = (P+1)+t-1 := by omega
  have hL : Work.SSSR.castElem (cokernel (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ ≫ Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)) he
        ((ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
            ((P+1)+t) (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f ((P+1)+t)))
              (Work.SSSR.ezLinSnd (P+1) t
                (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (P+1)) z))))
      = (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f ((P+1)+t)))
              (Work.SSSR.ezLinSnd (P+1) t
                (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (P+1)) z))) := by
    rw [Work.SSSR.StepAux.castElem_map]
    congr 1
    exact (Work.SSSR.StepAux.d_eq_castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
      he
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f ((P+1)+t)))
        (Work.SSSR.ezLinSnd (P+1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (P+1)) z))).symm
  have hR : Work.SSSR.castElem (cokernel (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ ≫ Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)) he
        ((ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) P σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez
                  (Fin.last (P+1)))).f (P+t)))
                (Work.SSSR.ezLinSnd P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z)))))
      = (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1)))
              (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                  (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                he
                ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
                  (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                (Work.SSSR.ezLinSnd P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z))))) := by
    rw [Work.SSSR.StepAux.castElem_map]
    congr 1
    rw [Work.SSSR.StepAux.castElem_map]
    congr 1
    rw [Work.SSSR.StepAux.castElem_map]
  have h2 := congrArg (Work.SSSR.castElem (cokernel (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ ≫ Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)) he) h
  rw [Work.SSSR.StepAux.castElem_zsmul] at h2
  rw [hL, hR] at h2
  exact h2

end Work.SSSR
