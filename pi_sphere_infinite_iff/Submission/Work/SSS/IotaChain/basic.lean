import Mathlib
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.SSS.iotaF_isCycle
import Submission.Work.SSS.serreE1PieceIsoZero
import Submission.Work.SSS.serreE1StepAux
import Submission.Work.SSS.iotaTBdryHorn
import Submission.Work.SSS.iotaTBdryHornZero
import Submission.Work.SSS.iotaTLift_derivation
import Submission.Work.SSS.iotaTLift_last_eq
import Submission.Work.SSS.pieceBdryHornIsoIso_inv
import Submission.Work.SSS.sigmaVert_face
import Submission.Work.KunnethEZ.ezChain_isCycle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Transport of a finite linear combination along a degree equality. -/
lemma castElem_sum {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    {ι : Type} (s : Finset ι) (a : ι → ℤ) (w : ι → K.X i) :
    Work.SSS.castElem K h (∑ k ∈ s, a k • w k) = ∑ k ∈ s, a k • Work.SSS.castElem K h (w k) := by
  subst h; simp [Work.SSS.castElem]

/-- **Lemma A: the base case `s = 0` for an arbitrary chain.** -/
theorem serreE1PieceIsoZero_chain (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    ∀ (t : ℕ) (z : (Work.SSS.fibreCC p b).X t)
      (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
      (hy : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (0+t)
              ((ComplexShape.down ℕ).next (0+t))))
              ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
                (Work.SSS.liftFam_proj p hfib) 0 b σ h t)) z) = 0),
      (Work.SSS.fibreConj p h t)
        ((Work.SSS.serreE1PieceIso p hfib 0 t σ).hom
          (HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (0+t)
            ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).cyclesMk
              ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
                (Work.SSS.liftFam_proj p hfib) 0 b σ h t)) z)
              ((ComplexShape.down ℕ).next (0+t)) rfl hy)))
      = (1:ℤ) • ((Work.SSS.fibreCC p b).homologyπ t
            ((Work.SSS.fibreCC p b).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)) := by
  intro t z hz hy
  unfold Work.SSS.fibreConj
  rw [← Work.SSS.SZero.zc_sCCMap_fibreTrans p b σ h]
  subst h
  have hE : Work.SSS.sCCMap (Work.SSS.SZero.fibreTrans p (Work.SSS.sigmaVert σ) σ rfl)
      = 𝟙 (Work.SSS.fibreCC p (Work.SSS.sigmaVert σ)) := by
    rw [Work.SSS.SZero.fibreTrans]
    simp only [CategoryTheory.eqToHom_refl, Work.SSS.sCCMap, CategoryTheory.Functor.map_id]
  rw [hE]
  simp only [HomologicalComplex.homologyMap_id, CategoryTheory.id_apply]
  rw [one_smul]
  rw [Work.SSS.SZero.zc_serreE1PieceIso_zero_eq p hfib (Work.SSS.sigmaVert σ) σ rfl t]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.comp_apply]
  refine Work.SSS.SZero.zc_generic (Work.SSS.pieceAlongZeroIso p σ).hom (Nat.zero_add t)
    (((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
        (Work.SSS.sigmaVert σ) σ rfl t)) z) hy z ?_ hz
  rw [Work.KunnethEZ.chain_eq_sum_gen
    (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))) t z]
  simp only [map_sum, map_zsmul]
  rw [castElem_sum]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact Work.SSS.SZero.zc_apply_gen p hfib σ t x

end

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The Eilenberg–Zilber derivation for `iotaT`, keeping the `rawY` term.** -/
theorem iotaTLift_derivation_raw (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋Q+1⦌) :
    (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)
        (Work.SSS.iotaTLift p hfib (t+1) b σ h (Q+1) τ)
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
            (Work.KunnethEZ.rawX t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))))
              (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ))
        + (-1 : ℤ) ^ (t+1) •
          (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
            (Work.KunnethEZ.rawY t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom (((Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex
                Work.KunnethEZ.eZR).d (Q+1) Q))
                (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ))) := by
  classical
  unfold Work.SSS.iotaTLift
  set φ0 := Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) (t+1) b σ h) with hφ0
  have hA : (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
        ((ConcreteCategory.hom ((Work.SSS.sCC
            (Δ[t+1] ⊗ Work.SSS.sSing (Work.StemsB.fibre p b))).d ((t+1)+(Q+1)) ((t+1)+(Q+1)-1)))
          (Work.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (t+1)) τ))
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
            (Work.KunnethEZ.rawX t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))))
              (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ))
        + (-1 : ℤ) ^ (t+1) •
          (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
            (Work.KunnethEZ.rawY t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom (((Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex
                Work.KunnethEZ.eZR).d (Q+1) Q))
                (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ))) := by
    rw [Work.KunnethEZ.d_ezGen t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
      (Work.SSS.stdIdSimplex (t+1)) τ]
    rw [Work.KunnethEZ.d_genC t Δ[t+1] (Work.SSS.stdIdSimplex (t+1))]
    rw [Work.KunnethEZ.rawX_sum_left]
    simp only [map_add, map_sum, map_zsmul]
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

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `rawX` as a linear map in its second variable. -/
noncomputable def rawXLin (p q : ℕ) (X Y : SSet.{0}) (u : (X.chainComplex Work.KunnethEZ.eZR).X p) :
    (Y.chainComplex Work.KunnethEZ.eZR).X (q+1) →ₗ[ℤ]
      ((X ⊗ Y).chainComplex Work.KunnethEZ.eZR).X ((p+1)+(q+1)-1) :=
  (Work.KunnethEZ.rawXBilin p q X Y (Work.Cohomology.Crux33.coords X p u)) ∘ₗ
    (Work.Cohomology.Crux33.coords Y (q+1))

/-- `rawY` as a linear map in its second variable. -/
noncomputable def rawYLin (p q : ℕ) (X Y : SSet.{0}) (u : (X.chainComplex Work.KunnethEZ.eZR).X (p+1)) :
    (Y.chainComplex Work.KunnethEZ.eZR).X q →ₗ[ℤ]
      ((X ⊗ Y).chainComplex Work.KunnethEZ.eZR).X ((p+1)+(q+1)-1) :=
  (Work.KunnethEZ.rawYBilin p q X Y (Work.Cohomology.Crux33.coords X (p+1) u)) ∘ₗ
    (Work.Cohomology.Crux33.coords Y q)

lemma rawXLin_apply (p q : ℕ) (X Y : SSet.{0}) (u : (X.chainComplex Work.KunnethEZ.eZR).X p)
    (v : (Y.chainComplex Work.KunnethEZ.eZR).X (q+1)) :
    rawXLin p q X Y u v = Work.KunnethEZ.rawX p q X Y u v := rfl

lemma rawYLin_apply (p q : ℕ) (X Y : SSet.{0}) (u : (X.chainComplex Work.KunnethEZ.eZR).X (p+1))
    (v : (Y.chainComplex Work.KunnethEZ.eZR).X q) :
    rawYLin p q X Y u v = Work.KunnethEZ.rawY p q X Y u v := rfl

/-- `castElem` as the `hom` of an `eqToHom`. -/
lemma castElem_eq_eqToHom {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) :
    Work.SSS.castElem K h x = (eqToHom (congrArg (fun m => K.X m) h)).hom x := by
  subst h; simp [Work.SSS.castElem]

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `X`-boundary part of the derivation, as a linear map. -/
noncomputable def phiXLin (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    (Work.SSS.fibreCC p b).X (Q+1) →ₗ[ℤ]
      (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((t+1)+Q) :=
  ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
    ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q))) ∘ₗ
      rawXLin t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
        (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1)))))

/-- The `Y`-boundary part of the derivation, as a linear map. -/
noncomputable def phiYLin (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    (Work.SSS.fibreCC p b).X (Q+1) →ₗ[ℤ]
      (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((t+1)+Q) :=
  ((-1 : ℤ) ^ (t+1)) •
    (((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q))) ∘ₗ
      rawYLin t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
        (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1)))) ∘ₗ
      (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (Q+1) Q)))

/-- The `X`-boundary part of the derivation, as a morphism. -/
noncomputable def phiX (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    (Work.SSS.fibreCC p b).X (Q+1) ⟶
      (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((t+1)+Q) :=
  ModuleCat.ofHom (phiXLin p hfib t Q b σ h)

/-- The `Y`-boundary part of the derivation, as a morphism. -/
noncomputable def phiY (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    (Work.SSS.fibreCC p b).X (Q+1) ⟶
      (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((t+1)+Q) :=
  ModuleCat.ofHom (phiYLin p hfib t Q b σ h)

lemma phiX_apply (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋Q+1⦌) :
    (ModuleCat.Hom.hom (phiX p hfib t Q b σ h))
        ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ)) 1)
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (ConcreteCategory.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)))
            (Work.KunnethEZ.rawX t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))))
              (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ)) := by
  rw [phiX]
  change (phiXLin p hfib t Q b σ h)
      ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ)) 1) = _
  rw [phiXLin, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

lemma phiY_apply (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋Q+1⦌) :
    (ModuleCat.Hom.hom (phiY p hfib t Q b σ h))
        ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ)) 1)
      = (-1 : ℤ) ^ (t+1) •
          (ConcreteCategory.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)))
            (Work.KunnethEZ.rawY t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom (((Work.SSS.sSing (Work.StemsB.fibre p b)).chainComplex
                Work.KunnethEZ.eZR).d (Q+1) Q))
                (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ))) := by
  rw [phiY]
  change (phiYLin p hfib t Q b σ h)
      ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ)) 1) = _
  rw [phiYLin]
  rfl

theorem iotaT_deriv_mor (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h (Q+1)
        ≫ (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)
      = phiX p hfib t Q b σ h + phiY p hfib t Q b σ h := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply]
  rw [phiX_apply p hfib t Q b σ h τ, phiY_apply p hfib t Q b σ h τ]
  rw [show (ConcreteCategory.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (t+1) b σ h (Q+1)))
        ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ)) 1)
      = Work.SSS.iotaTLift p hfib (t+1) b σ h (Q+1) τ
      from Work.SSS.StepAux.iotaT_gen_apply p hfib (t+1) b σ h (Q+1) τ]
  exact iotaTLift_derivation_raw p hfib t Q b σ h τ

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The right-hand side of the boundary-mod-horn comparison, as a morphism. -/
noncomputable def phiRHS (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b) :
    (Work.SSS.fibreCC p b).X (Q+1) ⟶
      (CategoryTheory.Limits.cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
        ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X ((t+1)+Q) :=
  ((-1 : ℤ) ^ (t+1)) •
    (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) t b
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1)
      ≫ eqToHom (congrArg (fun m => (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X m)
          (by omega : t + (Q+1) = (t+1)+Q))
      ≫ (Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f ((t+1)+Q)
      ≫ (Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((t+1)+Q)
      ≫ (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q))

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem phiX_hornCok (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b) :
    phiX p hfib t Q b σ h ≫ (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)
      = phiRHS p hfib t Q b σ h h' := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [phiX_apply p hfib t Q b σ h τ]
  rw [map_sum]
  simp only [map_zsmul]
  rw [Finset.sum_eq_single (Fin.last (t+1))]
  · rw [show ((-1 : ℤ) ^ (((Fin.last (t+1) : Fin (t+2)) : ℕ))) = (-1 : ℤ) ^ (t+1) from by
      rw [Fin.val_last]]
    rw [Work.SSS.iotaTLift_last_eq p hfib t Q b σ h h' τ]
    congr 1
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Work.SSS.StepAux.iotaT_gen_apply p hfib t b
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ]
    rw [← castElem_eq_eqToHom]
  · intro i _ hi
    rw [Work.SSS.hornCokπ_rawX_eq_zero p hfib t Q b σ h i hi τ, zsmul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem hornCok_d_iotaT_chain_succ (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b)
    (z : (Work.SSS.fibreCC p b).X (Q+1))
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (Q+1) Q)) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((t+1)+(Q+1)) ((t+1)+Q)))
          ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) (t+1) b σ h (Q+1))) z))
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f ((t+1)+Q)))
                (Work.SSS.castElem
                  (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
                  (by omega : t + (Q+1) = (t+1)+Q)
                  ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
                    (Work.SSS.liftFam_proj p hfib) t b
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z)))) := by
  have h1 : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
        ((t+1)+(Q+1)) ((t+1)+Q)))
        ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) (t+1) b σ h (Q+1))) z)
      = (ModuleCat.Hom.hom (phiX p hfib t Q b σ h)) z
        + (ModuleCat.Hom.hom (phiY p hfib t Q b σ h)) z := by
    have hh := congrArg (fun (g : (Work.SSS.fibreCC p b).X (Q+1) ⟶
        (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X ((t+1)+Q)) =>
        (ModuleCat.Hom.hom g) z) (iotaT_deriv_mor p hfib t Q b σ h)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply]
      using hh
  rw [h1, map_add]
  have h2 : (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom (phiX p hfib t Q b σ h)) z)
      = (ModuleCat.Hom.hom (phiRHS p hfib t Q b σ h h')) z := by
    have hh := congrArg (fun (g : (Work.SSS.fibreCC p b).X (Q+1) ⟶
        (CategoryTheory.Limits.cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
          ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X ((t+1)+Q)) =>
        (ModuleCat.Hom.hom g) z) (phiX_hornCok p hfib t Q b σ h h')
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hphiY : (ModuleCat.Hom.hom (phiY p hfib t Q b σ h)) z
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)))
            (Work.KunnethEZ.rawY t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
              (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (Q+1) Q)) z)) := by
    rw [phiY, ModuleCat.hom_ofHom, phiYLin]
    rfl
  have hraw : Work.KunnethEZ.rawY t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
        (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1)))
        ((ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (Q+1) Q)) z) = 0 := by
    rw [hz]
    show rawYLin t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
      (Work.KunnethEZ.genC Δ[t+1] (Work.SSS.stdIdSimplex (t+1))) 0 = 0
    exact map_zero _
  have h3 : (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom (phiY p hfib t Q b σ h)) z) = 0 := by
    rw [hphiY, hraw, map_zero, zsmul_zero, map_zero]
  rw [h2, h3, add_zero]
  rw [show (ModuleCat.Hom.hom (phiRHS p hfib t Q b σ h h')) z
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f ((t+1)+Q)))
                (Work.SSS.castElem
                  (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
                  (by omega : t + (Q+1) = (t+1)+Q)
                  ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
                    (Work.SSS.liftFam_proj p hfib) t b
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z)))) from by
    unfold phiRHS
    change (-1 : ℤ)^(t+1) • (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
          ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom (eqToHom (congrArg (fun m => (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X m)
              (by omega : t + (Q+1) = (t+1)+Q))))
              ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
                t b (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z))))
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((t+1)+Q)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f ((t+1)+Q)))
                (Work.SSS.castElem
                  (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
                  (by omega : t + (Q+1) = (t+1)+Q)
                  ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
                    (Work.SSS.liftFam_proj p hfib) t b
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z))))
    rw [← castElem_eq_eqToHom]]

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The trivial degree cast at fibre degree zero. -/
lemma castElem_triv_zero {K : ChainComplex (ModuleCat ℤ) ℕ} (s : ℕ) (x : K.X (s+0)) :
    Work.SSS.castElem K (by omega : s+0 = (s+1)+0-1) x = x := by
  rw [castElem_eq_eqToHom]
  have hh : congrArg (fun m => K.X m) (by omega : s+0 = (s+1)+0-1) = rfl :=
    Subsingleton.elim _ _
  rw [hh, CategoryTheory.eqToHom_refl]
  rfl

end Work.SSS.IotaChain

namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem hornCok_d_iotaT_chain_zero (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) = b)
    (z : (Work.SSS.fibreCC p b).X 0)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d 0 ((ComplexShape.down ℕ).next 0))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f s))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (s+1) s))
          ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) (s+1) b σ h 0)) z))
      = (-1 : ℤ)^(s+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f s))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f s))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) s σ).f s))
                (Work.SSS.castElem
                  (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)))
                  (by omega : s + 0 = (s+1)+0-1)
                  ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
                    (Work.SSS.liftFam_proj p hfib) s b
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0)) z)))) := by
  rw [castElem_triv_zero s]
  have hmor : Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (s+1) b σ h 0
        ≫ (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (s+1) s
        ≫ (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f s
      = ((-1 : ℤ)^(s+1)) •
          (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b
              (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0
            ≫ (Work.SSS.lastFaceChain (Work.SSS.sSingP p) s σ).f s
            ≫ (Work.SSS.TIncl (Work.SSS.sSingP p) σ).f s
            ≫ (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f s) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul]
    rw [show (ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) (s+1) b σ h 0))
          ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ)) 1)
        = Work.SSS.iotaTLift p hfib (s+1) b σ h 0 τ
        from Work.SSS.StepAux.iotaT_gen_apply p hfib (s+1) b σ h 0 τ]
    change (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f s))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (s+1) s))
          (Work.SSS.iotaTLift p hfib (s+1) b σ h 0 τ))
      = (-1 : ℤ)^(s+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f s))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f s))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) s σ).f s))
                ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
                  (Work.SSS.liftFam_proj p hfib) s b
                  (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0))
                  ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
                    (R := ModuleCat.of ℤ ℤ) τ)) 1))))
    rw [show (ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0))
          ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ)) 1)
        = Work.SSS.iotaTLift p hfib s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0 τ
        from Work.SSS.StepAux.iotaT_gen_apply p hfib s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0 τ]
    exact Work.SSS.iotaTBdryHornZero p hfib s b σ h h' τ
  have hz' := congrArg (fun (g : (Work.SSS.fibreCC p b).X 0 ⟶
      (CategoryTheory.Limits.cokernel (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ
        ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)).X s) => (ModuleCat.Hom.hom g) z) hmor
  exact hz'

end Work.SSS.IotaChain
namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **Lemma B: the boundary of `iotaT` modulo the horn, for an arbitrary cycle `z`.** -/
theorem hornCok_d_iotaT_chain (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) = b)
    (z : (Work.SSS.fibreCC p b).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((s+1)+q-1)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((s+1)+q) ((s+1)+q-1)))
          ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) (s+1) b σ h q)) z))
      = (-1 : ℤ)^(s+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((s+1)+q-1)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((s+1)+q-1)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) s σ).f ((s+1)+q-1)))
                (Work.SSS.castElem
                  (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)))
                  (by omega : s + q = (s+1)+q-1)
                  ((ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
                    (Work.SSS.liftFam_proj p hfib) s b
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' q)) z)))) := by
  rcases q with _ | k
  · exact hornCok_d_iotaT_chain_zero p hfib s b σ h h' z hz
  · rw [ChainComplex.next_nat_succ] at hz
    exact hornCok_d_iotaT_chain_succ p hfib s k b σ h h' z hz

end Work.SSS.IotaChain
namespace Work.SSS.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **`iotaF` sends cycles to cycles**, for an arbitrary chain. -/
theorem iotaF_cycle (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (P t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P+t)
        ((ComplexShape.down ℕ).next (P+t))))
      ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) P b σ h t)) z) = 0 := by
  rcases t with _ | k
  · -- degree `0`: linearize from `iotaF_isCycle`
    rw [Work.KunnethEZ.chain_eq_sum_gen (Work.SSS.sSing (Work.StemsB.fibre p b)) 0 z]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_eq_zero
    intro τ _
    rw [show (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P+0)
          ((ComplexShape.down ℕ).next (P+0))))
          ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) P b σ h 0))
            ((ModuleCat.Hom.hom ((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) τ)) 1)) = 0 from
      Work.SSS.iotaF_isCycle p hfib P b σ h 0 τ (by
        rw [ChainComplex.next_nat_zero]
        rw [HomologicalComplex.shape (Work.SSS.fibreCC p b) 0 0
          (by rw [ComplexShape.down_Rel]; omega)]
        rfl)]
    exact zsmul_zero _
  · -- degree `k+1`: chain-map property of `iotaF`
    have hchain := Work.SSS.iotaF_chainMap p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) P b σ h k
    have h1 := congrArg (fun (g : (Work.SSS.fibreCC p b).X (k+1) ⟶
        (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).X (P + k)) => (ModuleCat.Hom.hom g) z) hchain
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul, map_zsmul] at h1
    change (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P + (k+1)) (P + k)))
        ((ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) P b σ h (k+1))) z)
      = (-1 : ℤ)^P • (ModuleCat.Hom.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) P b σ h k))
          ((ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (k+1) k)) z) at h1
    rw [ChainComplex.next_nat_succ] at hz
    rw [hz, map_zero, zsmul_zero] at h1
    rw [show (ComplexShape.down ℕ).next (P + (k+1)) = P + k from ChainComplex.next_nat_succ (P+k)]
    exact h1

end Work.SSS.IotaChain
