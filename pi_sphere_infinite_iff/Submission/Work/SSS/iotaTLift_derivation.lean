import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.KunnethEZ.ezChain_isCycle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

set_option maxHeartbeats 1600000

theorem iotaTLift_derivation {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t Q : ℕ) (b : B)
    (σ : Δ[t+1] ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋Q+1⦌)
    (hτ : (Work.SSS.fibreCC p b).d (Q+1) Q
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)
        (Work.SSS.iotaTLift p hfib (t+1) b σ h (Q+1) τ)
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
            (Work.KunnethEZ.rawX t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))))
              (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ)) := by
  classical
  unfold Work.SSS.iotaTLift
  set φ0 := Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) (t+1) b σ h) with hφ0
  have hτ' : (ConcreteCategory.hom
      (((Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex Work.KunnethEZ.ezR).d (Q+1) Q))
      (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ) = 0 := hτ
  -- (A) the Eilenberg–Zilber derivation identity on the generator, in the `P + q - 1` degree
  have hA : (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
        ((ConcreteCategory.hom ((Work.SSS.sCC
            (Δ[t+1] ⊗ Work.SSS.sSing (Work.StemsB.fibre p b))).d ((t+1)+(Q+1)) ((t+1)+(Q+1)-1)))
          (Work.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (t+1)) τ))
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
            (Work.KunnethEZ.rawX t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))))
              (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ)) := by
    rw [Work.KunnethEZ.d_ezGen t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
      (Work.SSS.stdIdSimplex (t+1)) τ]
    rw [Work.KunnethEZ.d_genC t Δ[t+1] (Work.SSS.stdIdSimplex (t+1))]
    rw [Work.KunnethEZ.rawX_sum_left]
    rw [hτ']
    simp only [Work.KunnethEZ.rawY, map_zero, zsmul_zero, add_zero]
    simp only [map_sum, map_zsmul]
  -- (B) `φ0` is a chain map: move the differential past it
  rw [show (ConcreteCategory.hom
        ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)))
        ((ConcreteCategory.hom (φ0.f ((t+1)+(Q+1))))
          (Work.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (t+1)) τ))
      = (ConcreteCategory.hom ((φ0.f ((t+1)+(Q+1))) ≫
          (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)))
        (Work.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (t+1)) τ)
      from by simp only [ModuleCat.hom_comp, LinearMap.comp_apply]]
  rw [HomologicalComplex.Hom.comm φ0 ((t+1)+(Q+1)) ((t+1)+Q)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hA

end Work.SSS
