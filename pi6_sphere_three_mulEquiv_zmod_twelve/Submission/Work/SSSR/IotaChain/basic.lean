import Mathlib
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.iotaF_isCycle
import Submission.Work.SSSR.serreE1PieceIsoZero
import Submission.Work.SSSR.serreE1StepAux
import Submission.Work.SSSR.iotaTBdryHorn
import Submission.Work.SSSR.iotaTBdryHornZero
import Submission.Work.SSSR.iotaTLift_derivation
import Submission.Work.SSSR.iotaTLift_last_eq
import Submission.Work.SSSR.pieceBdryHornIsoIso_inv
import Submission.Work.SSSR.sigmaVert_face
import Submission.Work.SSSR.KunnethEZ.ezChain_isCycle
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Transport of a finite linear combination along a degree equality. -/
lemma castElem_sum {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    {ι : Type} (s : Finset ι) (a : ι → R) (w : ι → K.X i) :
    Work.SSSR.castElem K h (∑ k ∈ s, a k • w k) = ∑ k ∈ s, a k • Work.SSSR.castElem K h (w k) := by
  subst h; simp [Work.SSSR.castElem]

/-- **Lemma A: the base case `s = 0` for an arbitrary chain.** -/
theorem serreE1PieceIsoZero_chain (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    ∀ (t : ℕ) (z : (Work.SSSR.fibreCC p b).X t)
      (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
      (hy : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (0+t)
              ((ComplexShape.down ℕ).next (0+t))))
              ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
                (Work.SSSR.liftFam_proj p hfib) 0 b σ h t)) z) = 0),
      (Work.SSSR.fibreConj p h t)
        ((Work.SSSR.serreE1PieceIso p hfib 0 t σ).hom
          (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (0+t)
            ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
              ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
                (Work.SSSR.liftFam_proj p hfib) 0 b σ h t)) z)
              ((ComplexShape.down ℕ).next (0+t)) rfl hy)))
      = (1 : R) • ((Work.SSSR.fibreCC p b).homologyπ t
            ((Work.SSSR.fibreCC p b).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)) := by
  intro t z hz hy
  unfold Work.SSSR.fibreConj
  rw [← Work.SSSR.SZero.zc_sCCMap_fibreTrans p b σ h]
  subst h
  have hE : Work.SSSR.sCCMap R (Work.SSSR.SZero.fibreTrans p (Work.SSSR.sigmaVert σ) σ rfl)
      = 𝟙 (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)) := by
    rw [Work.SSSR.SZero.fibreTrans]
    simp only [CategoryTheory.eqToHom_refl, Work.SSSR.sCCMap, CategoryTheory.Functor.map_id]
  rw [hE]
  simp only [HomologicalComplex.homologyMap_id, CategoryTheory.id_apply]
  rw [one_smul]
  rw [Work.SSSR.SZero.zc_serreE1PieceIso_zero_eq p hfib (Work.SSSR.sigmaVert σ) σ rfl t]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.comp_apply]
  refine Work.SSSR.SZero.zc_generic (Work.SSSR.pieceAlongZeroIso p σ).hom (Nat.zero_add t)
    (((Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
        (Work.SSSR.sigmaVert σ) σ rfl t)) z) hy z ?_ hz
  rw [Work.SSSR.KunnethEZ.chain_eq_sum_gen
    (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) t z]
  simp only [map_sum, map_smul]
  rw [castElem_sum]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact Work.SSSR.SZero.zc_apply_gen p hfib σ t x

end

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The Eilenberg–Zilber derivation for `iotaT`, keeping the `rawY` term.** -/
theorem iotaTLift_derivation_raw (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋Q+1⦌) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)
        (Work.SSSR.iotaTLift p hfib (t+1) b σ h (Q+1) τ)
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
            (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))))
              (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))
        + (-1 : ℤ) ^ (t+1) •
          (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
            (Work.SSSR.KunnethEZ.rawY t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).chainComplex
                (Work.SSSR.KunnethEZ.eZR R)).d (Q+1) Q))
                (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))) := by
  classical
  unfold Work.SSSR.iotaTLift
  set φ0 := Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h) with hφ0
  have hA : (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
        ((ConcreteCategory.hom ((Work.SSSR.sCC R
            (Δ[t+1] ⊗ Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).d ((t+1)+(Q+1)) ((t+1)+(Q+1)-1)))
          (Work.SSSR.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (t+1)) τ))
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
            (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))))
              (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))
        + (-1 : ℤ) ^ (t+1) •
          (ConcreteCategory.hom (φ0.f ((t+1)+(Q+1)-1)))
            (Work.SSSR.KunnethEZ.rawY t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).chainComplex
                (Work.SSSR.KunnethEZ.eZR R)).d (Q+1) Q))
                (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))) := by
    rw [Work.SSSR.KunnethEZ.d_ezGen t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      (Work.SSSR.stdIdSimplex (t+1)) τ]
    rw [Work.SSSR.KunnethEZ.d_genC t Δ[t+1] (Work.SSSR.stdIdSimplex (t+1))]
    rw [Work.SSSR.KunnethEZ.rawX_sum_left_zsmul]
    simp only [map_add, map_sum, map_zsmul]
  rw [show (ConcreteCategory.hom
        ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)))
        ((ConcreteCategory.hom (φ0.f ((t+1)+(Q+1))))
          (Work.SSSR.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (t+1)) τ))
      = (ConcreteCategory.hom ((φ0.f ((t+1)+(Q+1))) ≫
          (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)))
        (Work.SSSR.Cohomology.Crux33.ezGen (t+1) (Q+1) Δ[t+1]
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (t+1)) τ)
      from by simp only [ModuleCat.hom_comp, LinearMap.comp_apply]]
  rw [HomologicalComplex.Hom.comm φ0 ((t+1)+(Q+1)) ((t+1)+Q)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hA

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `rawX` as a linear map in its second variable. -/
noncomputable def rawXLin (p q : ℕ) (X Y : SSet.{0}) (u : (X.chainComplex (Work.SSSR.KunnethEZ.eZR R)).X p) :
    (Y.chainComplex (Work.SSSR.KunnethEZ.eZR R)).X (q+1) →ₗ[R]
      ((X ⊗ Y).chainComplex (Work.SSSR.KunnethEZ.eZR R)).X ((p+1)+(q+1)-1) :=
  (Work.SSSR.KunnethEZ.rawXBilin p q X Y (Work.SSSR.Cohomology.Crux33.coords X p u)) ∘ₗ
    (Work.SSSR.Cohomology.Crux33.coords Y (q+1))

/-- `rawY` as a linear map in its second variable. -/
noncomputable def rawYLin (p q : ℕ) (X Y : SSet.{0}) (u : (X.chainComplex (Work.SSSR.KunnethEZ.eZR R)).X (p+1)) :
    (Y.chainComplex (Work.SSSR.KunnethEZ.eZR R)).X q →ₗ[R]
      ((X ⊗ Y).chainComplex (Work.SSSR.KunnethEZ.eZR R)).X ((p+1)+(q+1)-1) :=
  (Work.SSSR.KunnethEZ.rawYBilin p q X Y (Work.SSSR.Cohomology.Crux33.coords X (p+1) u)) ∘ₗ
    (Work.SSSR.Cohomology.Crux33.coords Y q)

/-- `castElem` as the `hom` of an `eqToHom`. -/
lemma castElem_eq_eqToHom {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) :
    Work.SSSR.castElem K h x = (eqToHom (congrArg (fun m => K.X m) h)).hom x := by
  subst h; simp [Work.SSSR.castElem]

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `X`-boundary part of the derivation, as a linear map. -/
noncomputable def phiXLin (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    (Work.SSSR.fibreCC (R := R) p b).X (Q+1) →ₗ[R]
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((t+1)+Q) :=
  ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
    ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q))) ∘ₗ
      rawXLin t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
        (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1)))))

/-- The `Y`-boundary part of the derivation, as a linear map. -/
noncomputable def phiYLin (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    (Work.SSSR.fibreCC (R := R) p b).X (Q+1) →ₗ[R]
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((t+1)+Q) :=
  ((-1 : ℤ) ^ (t+1)) •
    (((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q))) ∘ₗ
      rawYLin t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
        (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1)))) ∘ₗ
      (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d (Q+1) Q)))

/-- The `X`-boundary part of the derivation, as a morphism. -/
noncomputable def phiX (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    (Work.SSSR.fibreCC p b).X (Q+1) ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((t+1)+Q) :=
  ModuleCat.ofHom (phiXLin p hfib t Q b σ h)

/-- The `Y`-boundary part of the derivation, as a morphism. -/
noncomputable def phiY (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    (Work.SSSR.fibreCC p b).X (Q+1) ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((t+1)+Q) :=
  ModuleCat.ofHom (phiYLin p hfib t Q b σ h)

lemma phiX_apply (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋Q+1⦌) :
    (ModuleCat.Hom.hom (phiX p hfib t Q b σ h))
        ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of R R) τ)) 1)
      = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
          (ConcreteCategory.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)))
            (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))))
              (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ)) := by
  rw [phiX]
  change (phiXLin p hfib t Q b σ h)
      ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
        (R := ModuleCat.of R R) τ)) 1) = _
  rw [phiXLin, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

lemma phiY_apply (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋Q+1⦌) :
    (ModuleCat.Hom.hom (phiY p hfib t Q b σ h))
        ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of R R) τ)) 1)
      = (-1 : ℤ) ^ (t+1) •
          (ConcreteCategory.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)))
            (Work.SSSR.KunnethEZ.rawY t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).chainComplex
                (Work.SSSR.KunnethEZ.eZR R)).d (Q+1) Q))
                (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))) := by
  rw [phiY]
  change (phiYLin p hfib t Q b σ h)
      ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
        (R := ModuleCat.of R R) τ)) 1) = _
  rw [phiYLin]
  rfl

theorem iotaT_deriv_mor (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h (Q+1)
        ≫ (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q)
      = phiX p hfib t Q b σ h + phiY p hfib t Q b σ h := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply]
  rw [phiX_apply p hfib t Q b σ h τ, phiY_apply p hfib t Q b σ h τ]
  rw [show (ConcreteCategory.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h (Q+1)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of R R) τ)) 1)
      = Work.SSSR.iotaTLift p hfib (t+1) b σ h (Q+1) τ
      from Work.SSSR.StepAux.iotaT_gen_apply p hfib (t+1) b σ h (Q+1) τ]
  exact iotaTLift_derivation_raw p hfib t Q b σ h τ

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The right-hand side of the boundary-mod-horn comparison, as a morphism. -/
noncomputable def phiRHS (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b) :
    (Work.SSSR.fibreCC (R := R) p b).X (Q+1) ⟶
      (CategoryTheory.Limits.cokernel (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ
        ≫ Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)).X ((t+1)+Q) :=
  ((-1 : ℤ) ^ (t+1)) •
    (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) t b
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1)
      ≫ eqToHom (congrArg (fun m => (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X m)
          (by omega : t + (Q+1) = (t+1)+Q))
      ≫ (Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)
      ≫ (Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)
      ≫ (Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q))

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem phiX_hornCok (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b) :
    phiX (R := R) p hfib t Q b σ h ≫ (Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)
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
    rw [Work.SSSR.iotaTLift_last_eq p hfib t Q b σ h h' τ]
    congr 1
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [Work.SSSR.StepAux.iotaT_gen_apply p hfib t b
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ]
    rw [← castElem_eq_eqToHom]
  · intro i _ hi
    rw [Work.SSSR.hornCokπ_rawX_eq_zero p hfib t Q b σ h i hi τ, zsmul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem hornCok_d_iotaT_chain_succ (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b)
    (z : (Work.SSSR.fibreCC p b).X (Q+1))
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d (Q+1) Q)) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
            ((t+1)+(Q+1)) ((t+1)+Q)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h (Q+1))) z))
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)))
                (Work.SSSR.castElem
                  (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
                  (by omega : t + (Q+1) = (t+1)+Q)
                  ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
                    (Work.SSSR.liftFam_proj p hfib) t b
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z)))) := by
  have h1 : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
        ((t+1)+(Q+1)) ((t+1)+Q)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h (Q+1))) z)
      = (ModuleCat.Hom.hom (phiX p hfib t Q b σ h)) z
        + (ModuleCat.Hom.hom (phiY p hfib t Q b σ h)) z := by
    have hh := congrArg (fun (g : (Work.SSSR.fibreCC p b).X (Q+1) ⟶
        (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((t+1)+Q)) =>
        (ModuleCat.Hom.hom g) z) (iotaT_deriv_mor p hfib t Q b σ h)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply]
      using hh
  rw [h1, map_add]
  have h2 : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom (phiX p hfib t Q b σ h)) z)
      = (ModuleCat.Hom.hom (phiRHS p hfib t Q b σ h h')) z := by
    have hh := congrArg (fun (g : (Work.SSSR.fibreCC p b).X (Q+1) ⟶
        (CategoryTheory.Limits.cokernel (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ
          ≫ Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)).X ((t+1)+Q)) =>
        (ModuleCat.Hom.hom g) z) (phiX_hornCok p hfib t Q b σ h h')
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hphiY : (ModuleCat.Hom.hom (phiY p hfib t Q b σ h)) z
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)))
            (Work.SSSR.KunnethEZ.rawY t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
              (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1)))
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d (Q+1) Q)) z)) := by
    rw [phiY, ModuleCat.hom_ofHom, phiYLin]
    rfl
  have hraw : Work.SSSR.KunnethEZ.rawY t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
        (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1)))
        ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d (Q+1) Q)) z) = 0 := by
    rw [hz]
    show rawYLin t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      (Work.SSSR.KunnethEZ.genC Δ[t+1] (Work.SSSR.stdIdSimplex (t+1))) 0 = 0
    exact map_zero _
  have h3 : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom (phiY p hfib t Q b σ h)) z) = 0 := by
    rw [hphiY, hraw, map_zero, zsmul_zero, map_zero]
  rw [h2, h3, add_zero]
  rw [show (ModuleCat.Hom.hom (phiRHS p hfib t Q b σ h h')) z
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)))
                (Work.SSSR.castElem
                  (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
                  (by omega : t + (Q+1) = (t+1)+Q)
                  ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
                    (Work.SSSR.liftFam_proj p hfib) t b
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z)))) from by
    unfold phiRHS
    change (-1 : ℤ)^(t+1) • (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
          ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom (eqToHom (congrArg (fun m => (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X m)
              (by omega : t + (Q+1) = (t+1)+Q))))
              ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
                t b (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z))))
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)))
                (Work.SSSR.castElem
                  (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
                  (by omega : t + (Q+1) = (t+1)+Q)
                  ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
                    (Work.SSSR.liftFam_proj p hfib) t b
                    (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1))) z))))
    rw [← castElem_eq_eqToHom]]

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The trivial degree cast at fibre degree zero. -/
lemma castElem_triv_zero {K : ChainComplex (ModuleCat R) ℕ} (s : ℕ) (x : K.X (s+0)) :
    Work.SSSR.castElem K (by omega : s+0 = (s+1)+0-1) x = x := by
  rw [castElem_eq_eqToHom]
  have hh : congrArg (fun m => K.X m) (by omega : s+0 = (s+1)+0-1) = rfl :=
    Subsingleton.elim _ _
  rw [hh, CategoryTheory.eqToHom_refl]
  rfl

end Work.SSSR.IotaChain

namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem hornCok_d_iotaT_chain_zero (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) = b)
    (z : (Work.SSSR.fibreCC p b).X 0)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d 0 ((ComplexShape.down ℕ).next 0))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f s))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s+1) s))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h 0)) z))
      = (-1 : ℤ)^(s+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f s))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f s))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) s σ).f s))
                (Work.SSSR.castElem
                  (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)))
                  (by omega : s + 0 = (s+1)+0-1)
                  ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
                    (Work.SSSR.liftFam_proj p hfib) s b
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0)) z)))) := by
  rw [castElem_triv_zero s]
  have hmor : Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h 0
        ≫ (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s+1) s
        ≫ (Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f s
      = ((-1 : ℤ)^(s+1)) •
          (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b
              (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0
            ≫ (Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) s σ).f s
            ≫ (Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f s
            ≫ (Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f s) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul]
    rw [show (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h 0))
          ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of R R) τ)) 1)
        = Work.SSSR.iotaTLift p hfib (s+1) b σ h 0 τ
        from Work.SSSR.StepAux.iotaT_gen_apply p hfib (s+1) b σ h 0 τ]
    change (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f s))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (s+1) s))
          (Work.SSSR.iotaTLift p hfib (s+1) b σ h 0 τ))
      = (-1 : ℤ)^(s+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f s))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f s))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) s σ).f s))
                ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
                  (Work.SSSR.liftFam_proj p hfib) s b
                  (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0))
                  ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
                    (R := ModuleCat.of R R) τ)) 1))))
    rw [show (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0))
          ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of R R) τ)) 1)
        = Work.SSSR.iotaTLift p hfib s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0 τ
        from Work.SSSR.StepAux.iotaT_gen_apply p hfib s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' 0 τ]
    exact Work.SSSR.iotaTBdryHornZero p hfib s b σ h h' τ
  have hz' := congrArg (fun (g : (Work.SSSR.fibreCC p b).X 0 ⟶
      (CategoryTheory.Limits.cokernel (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ
        ≫ Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)).X s) => (ModuleCat.Hom.hom g) z) hmor
  exact hz'

end Work.SSSR.IotaChain
namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **Lemma B: the boundary of `iotaT` modulo the horn, for an arbitrary cycle `z`.** -/
theorem hornCok_d_iotaT_chain (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) = b)
    (z : (Work.SSSR.fibreCC p b).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((s+1)+q-1)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
            ((s+1)+q) ((s+1)+q-1)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h q)) z))
      = (-1 : ℤ)^(s+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((s+1)+q-1)))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((s+1)+q-1)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) s σ).f ((s+1)+q-1)))
                (Work.SSSR.castElem
                  (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)))
                  (by omega : s + q = (s+1)+q-1)
                  ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
                    (Work.SSSR.liftFam_proj p hfib) s b
                    (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' q)) z)))) := by
  rcases q with _ | k
  · exact hornCok_d_iotaT_chain_zero p hfib s b σ h h' z hz
  · rw [ChainComplex.next_nat_succ] at hz
    exact hornCok_d_iotaT_chain_succ p hfib s k b σ h h' z hz

end Work.SSSR.IotaChain
namespace Work.SSSR.IotaChain

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **`iotaF` sends cycles to cycles**, for an arbitrary chain. -/
theorem iotaF_cycle (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (P t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P+t)
        ((ComplexShape.down ℕ).next (P+t))))
      ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) P b σ h t)) z) = 0 := by
  rcases t with _ | k
  · -- degree `0`: linearize from `iotaF_isCycle`
    rw [Work.SSSR.KunnethEZ.chain_eq_sum_gen (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) 0 z]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro τ _
    rw [show (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P+0)
          ((ComplexShape.down ℕ).next (P+0))))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) P b σ h 0))
            ((ModuleCat.Hom.hom ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
              (R := ModuleCat.of R R) τ)) 1)) = 0 from
      Work.SSSR.iotaF_isCycle p hfib P b σ h 0 τ (by
        rw [ChainComplex.next_nat_zero]
        rw [HomologicalComplex.shape (Work.SSSR.fibreCC p b) 0 0
          (by rw [ComplexShape.down_Rel]; omega)]
        rfl)]
    exact smul_zero _
  · -- degree `k+1`: chain-map property of `iotaF`
    have hchain := Work.SSSR.iotaF_chainMap (R := R) p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) P b σ h k
    have h1 := congrArg (fun (g : (Work.SSSR.fibreCC p b).X (k+1) ⟶
        (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).X (P + k)) => (ModuleCat.Hom.hom g) z) hchain
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul, map_zsmul] at h1
    change (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P + (k+1)) (P + k)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) P b σ h (k+1))) z)
      = (-1 : ℤ)^P • (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) P b σ h k))
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d (k+1) k)) z) at h1
    rw [ChainComplex.next_nat_succ] at hz
    rw [hz, map_zero, zsmul_zero] at h1
    rw [show (ComplexShape.down ℕ).next (P + (k+1)) = P + k from ChainComplex.next_nat_succ (P+k)]
    exact h1

end Work.SSSR.IotaChain
