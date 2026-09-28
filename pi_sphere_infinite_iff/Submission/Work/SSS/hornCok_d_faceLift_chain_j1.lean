import Mathlib
import Submission.Work.SSS.hornCok_d_faceLift_chain
import Submission.Work.SSS.pieceIso_lift_genC

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- **The `hpeel` input of `Work.SSS.pieceIso_peel` for an arbitrary CHAIN.**

This is the CHAIN-level version of `Work.SSS.hornCok_d_faceLift_j1`
(`Submission/Work/SSS/pieceIso_lift_genC.lean`): the same statement with the simplex `τ` (and its
cycle hypothesis `hτ`) replaced by an arbitrary cycle CHAIN `z`, and the EZ chain `ezGen` replaced
by its linear extension `Work.SSS.ezLinSnd`.  It is obtained from the PROVED
`Work.SSS.hornCok_d_faceLift_chain` (whose conclusion is the same identity at the degrees
`(P+1)+t → P+t`) by the degree `castElem` bookkeeping already carried out in
`Work.SSS.hornCok_d_faceLift_j1`: copy that proof verbatim (lines ~60-143 of
`Submission/Work/SSS/pieceIso_lift_genC.lean`), replacing `hornCok_d_faceLift` by
`hornCok_d_faceLift_chain`, `ezGen _ _ … τ` by `ezLinSnd _ _ … z`, and `τ`, `hτ` by `z`, `hz`. -/
lemma hornCok_d_faceLift_chain_j1 {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
            (Work.SSS.ezLinSnd (P+1) t
              (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) z)))
      = (-1 : ℤ)^(P+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f ((P+1)+t-1)))
                (Work.SSS.castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                  (by omega : P+t = (P+1)+t-1)
                  ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                    (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                  (Work.SSS.ezLinSnd P t
                    (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                    (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z))))) := by
  have h := Work.SSS.hornCok_d_faceLift_chain p hfib P t b σ ez hez z hz
  have he : P+t = (P+1)+t-1 := by omega
  have hL : Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) he
        ((ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
              (Work.SSS.ezLinSnd (P+1) t
                (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) z))))
      = (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
              (Work.SSS.ezLinSnd (P+1) t
                (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) z))) := by
    rw [Work.SSS.StepAux.castElem_map]
    congr 1
    exact (Work.SSS.StepAux.d_eq_castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ))
      he
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
        (Work.SSS.ezLinSnd (P+1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) z))).symm
  have hR : Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) he
        ((ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez
                  (Fin.last (P+1)))).f (P+t)))
                (Work.SSS.ezLinSnd P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z)))))
      = (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f ((P+1)+t-1)))
              (Work.SSS.castElem (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                  (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)))
                he
                ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                  (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                (Work.SSS.ezLinSnd P t
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z))))) := by
    rw [Work.SSS.StepAux.castElem_map]
    congr 1
    rw [Work.SSS.StepAux.castElem_map]
    congr 1
    rw [Work.SSS.StepAux.castElem_map]
  have h2 := congrArg (Work.SSS.castElem (cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)) he) h
  rw [Work.SSS.StepAux.castElem_zsmul] at h2
  rw [hL, hR] at h2
  exact h2

end Work.SSS
