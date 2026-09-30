import Mathlib
import Submission.Work.Pi6.MSSK.peel_aux
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.serreE1StepAux
import Submission.Work.SSSR.pieceIso_peel
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The last-face peeling datum of a relative cycle

For a simplex `σ : Δ[P+1] ⟶ Sing B` and a *relative* cycle `c` of `T_σ` of degree `(P+1)+t` (i.e.
such that the projection of `c` to the σ-piece is a cycle), there is a chain `W` of the last-face
piece `T_{δ_last σ}` in degree `(P+1)+t-1` whose projection is a cycle and whose last-face chain
represents `(-1)^(P+1)` times the class of `∂c` in `C(∂T_σ)/C(Λ)`.

This is the input datum of `Work.SSSR.pieceIso_peel` and of `Work.Pi6.MSSK.capEdgeIdentity`; the
statement here keeps the last-face chain in degree `(P+1)+t-1` (the degree in which it is produced
by the snake/connecting-map construction), so that no degree transport is needed in the proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

namespace Peel

attribute [local implicit_reducible] Work.SSSR.pullAlong
attribute [local implicit_reducible] Work.SSSR.pieceHorn
attribute [local implicit_reducible] Work.SSSR.pieceLastFace
attribute [local implicit_reducible] Work.SSSR.bdryAlong

theorem peelData (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {P t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((P+1)+t))
    (hz : ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d ((P+1)+t) ((P+1)+t-1)).hom
        ((CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((P+1)+t) c) = 0) :
    ∃ W : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) σ))).X ((P+1)+t-1),
      (((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) σ)).d
          ((P+1)+t-1) ((P+1)+t-1-1)).hom
          ((CategoryTheory.Limits.cokernel.π (Work.SSSR.sCCMap R
            (Work.SSSR.bdryAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) σ)).ι)).f
              ((P+1)+t-1) W) = 0)
      ∧ (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
          (((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((P+1)+t) ((P+1)+t-1)).hom c)
        = (-1 : ℤ)^(P+1) •
            (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)))
              (((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f ((P+1)+t-1))
                ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1) W)) := by
  classical
  -- (1) the lift of `∂c` to `C(∂T_σ)`
  obtain ⟨y, hy⟩ := Peel.exists_lift_of_cokernel_cycle_K R
      (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ) ((P+1)+t) c (by
        show (cokernel (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ)).d
            ((P+1)+t) ((P+1)+t-1)
          ((cokernel.π (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ)).f ((P+1)+t) c) = 0
        exact hz)
  -- (2) `y` is a cycle
  have hyc : ((Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).d
        ((P+1)+t-1) ((P+1)+t-1-1)) y = 0 := by
    have hcomm := Peel.chainMap_comm_apply (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ)
      ((P+1)+t-1) ((P+1)+t-1-1) y
    have hzero : ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
          ((P+1)+t-1) ((P+1)+t-1-1))
        (((Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)) y) = 0 := by
      rw [hy]
      have hdd := HomologicalComplex.d_comp_d (Work.SSSR.sCC R
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) ((P+1)+t) ((P+1)+t-1) ((P+1)+t-1-1)
      rw [← ModuleCat.comp_apply, hdd]
      simp
    rw [hcomm] at hzero
    exact Peel.TIncl_f_injective (R := R) (Work.SSSR.sSingP p) σ ((P+1)+t-1-1)
      (by rw [hzero]; simp)
  -- (3) the class `u = bdryHornProj y` is a cycle
  have huc : ((Work.SSSR.pieceBdryHornC R (Work.SSSR.sSingP p) σ).d
        ((P+1)+t-1) ((P+1)+t-1-1))
      (((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)) y) = 0 := by
    rw [Peel.chainMap_comm_apply (Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ)
      ((P+1)+t-1) ((P+1)+t-1-1) y, hyc]
    simp
  -- (4) `φ.hom (ε • u)` is a cycle
  have hVc : ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)).d ((P+1)+t-1) ((P+1)+t-1-1))
      (((Work.SSSR.pieceBdryHornIsoIso (R := R) (Work.SSSR.sSingP p) P σ).hom.f ((P+1)+t-1))
        ((-1 : ℤ)^(P+1) • (((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
          ((P+1)+t-1)) y))) = 0 := by
    rw [Peel.chainMap_comm_apply
        ((Work.SSSR.pieceBdryHornIsoIso (R := R) (Work.SSSR.sSingP p) P σ).hom)
        ((P+1)+t-1) ((P+1)+t-1-1)
        ((-1 : ℤ)^(P+1) • (((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
          ((P+1)+t-1)) y))]
    rw [map_zsmul, huc]
    simp
  -- (5) a lift of `φ.hom (ε • u)` along the cokernel projection
  obtain ⟨W, hW⟩ := Peel.cokernel_π_f_surjective (R := R)
      (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ)) ((P+1)+t-1)
      (((Work.SSSR.pieceBdryHornIsoIso (R := R) (Work.SSSR.sSingP p) P σ).hom.f ((P+1)+t-1))
        ((-1 : ℤ)^(P+1) • (((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
          ((P+1)+t-1)) y)))
  refine ⟨W, ?_, ?_⟩
  · -- `π W` is a cycle
    rw [hW]
    exact hVc
  · -- the peeling equation
    have hsnake1 : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f
          ((P+1)+t-1)))
        (((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
          ((P+1)+t) ((P+1)+t-1)).hom c)
        = (ModuleCat.Hom.hom ((Work.SSSR.StepAux.snakeF (R := R) (Work.SSSR.sSingP p) P σ).f
            ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
            ((P+1)+t-1))) y) := by
      rw [← hy]
      exact Peel.snakeF_apply (R := R) (Work.SSSR.sSingP p) P ((P+1)+t-1) σ y
    have hsnake2 : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f
          ((P+1)+t-1)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f
          ((P+1)+t-1))) ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (R := R)
            (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1))) W))
        = (ModuleCat.Hom.hom ((Work.SSSR.StepAux.snakeF (R := R) (Work.SSSR.sSingP p) P σ).f
            ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
            ((P+1)+t-1))) ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (R := R)
              (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1))) W)) :=
      Peel.snakeF_apply (R := R) (Work.SSSR.sSingP p) P ((P+1)+t-1) σ
        ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1) W)
    have hiso := congrArg (fun φ => (ModuleCat.Hom.hom (φ.f ((P+1)+t-1))) W)
      (Work.SSSR.pieceBdryHornIsoIso_inv (R := R) (f := Work.SSSR.sSingP p) P σ)
    have hW' : (ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
          ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) P σ).f
            ((P+1)+t-1))) W)
        = (-1 : ℤ)^(P+1) • (ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R)
            (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)) y) :=
      hiso.symm.trans
        (show (ModuleCat.Hom.hom ((Work.SSSR.pieceBdryHornIsoIso (R := R)
              (Work.SSSR.sSingP p) P σ).inv.f ((P+1)+t-1)))
            ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π (Work.SSSR.TIncl (R := R)
              (Work.SSSR.sSingP p) (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ))).f
              ((P+1)+t-1))) W)
          = (-1 : ℤ)^(P+1) • (ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R)
              (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)) y) from by
          rw [hW]
          exact Peel.iso_inv_hom_apply (Work.SSSR.pieceBdryHornIsoIso (R := R)
            (Work.SSSR.sSingP p) P σ) ((P+1)+t-1)
            ((-1 : ℤ)^(P+1) • (ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R)
              (Work.SSSR.sSingP p) σ).f ((P+1)+t-1)) y)))
    rw [hsnake1, hsnake2, hW']
    exact ((congrArg (fun w => ((-1 : ℤ)^(P+1)) • w)
        (map_zsmul (ModuleCat.Hom.hom ((Work.SSSR.StepAux.snakeF (R := R)
          (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1))) ((-1 : ℤ)^(P+1))
          ((ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
            ((P+1)+t-1))) y))).trans
      (Peel.negOnePow_smul_smul (P+1) ((ModuleCat.Hom.hom ((Work.SSSR.StepAux.snakeF
        (R := R) (Work.SSSR.sSingP p) P σ).f ((P+1)+t-1)))
          ((ModuleCat.Hom.hom ((Work.SSSR.bdryHornProj (R := R) (Work.SSSR.sSingP p) σ).f
            ((P+1)+t-1))) y)))).symm

end Peel

end Work.Pi6.MSSK
