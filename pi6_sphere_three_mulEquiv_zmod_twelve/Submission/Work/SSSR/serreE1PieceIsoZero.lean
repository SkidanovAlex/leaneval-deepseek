import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.SZero.Defs
import Submission.Work.SSSR.SZero.ezGen_zero_eq_vertIncl
import Submission.Work.SSSR.SZero.castSimp_zSh_bHom
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.pieceBdryHornIso
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.KunnethEZ.EZGenX
import Submission.Work.SSSR.serreE1StepAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSSR.SZero
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

theorem zc_eqMpr_iso {A : ℕ → ModuleCat R} {B : ModuleCat R} {m n : ℕ} (h : m = n)
    (e : A n ≅ B) : Eq.mpr (congrArg (fun i => A i ≅ B) h) e = eqToIso (congrArg A h) ≪≫ e := by
  subst h
  simp

def zcCastCycles (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j) (x : K.cycles i) :
    K.cycles j :=
  (eqToHom (congrArg (fun m => K.cycles m) h)).hom x

theorem zc_castCycles_map {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    HomologicalComplex.cyclesMap φ j (zcCastCycles K h z)
      = zcCastCycles L h (HomologicalComplex.cyclesMap φ i z) := by
  subst h
  simp [zcCastCycles]

theorem zc_homologyMap_homologyπ {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) z)
      = (L.homologyπ i) (HomologicalComplex.cyclesMap φ i z) :=
  congrArg (fun (f : K.cycles i ⟶ L.homology i) => f z)
    (HomologicalComplex.homologyπ_naturality φ i)

theorem zc_eqToIso_homologyπ {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    (eqToIso (congrArg (fun m => K.homology m) h)).hom ((K.homologyπ i) z)
      = (K.homologyπ j) (zcCastCycles K h z) := by
  subst h
  simp [zcCastCycles]

theorem zc_iCycles_cyclesMk {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

theorem zc_d_map_eq_zero {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (x : K.X i) (hx : K.d i j x = 0) : L.d i j ((φ.f i) x) = 0 := by
  have h := congrArg (fun (g : K.X i ⟶ L.X j) => g x) (HomologicalComplex.Hom.comm φ i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hx, map_zero] at h
  exact h

theorem zc_d_castElem {K : ChainComplex (ModuleCat R) ℕ} {i i' j : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.d i' ((ComplexShape.down ℕ).next i') (Work.SSSR.castElem K h x) = 0 := by
  subst h
  rw [← hj] at hx
  simpa [Work.SSSR.castElem] using hx

theorem zc_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0)
    (hy : L.d i j ((φ.f i) x) = 0) :
    HomologicalComplex.cyclesMap φ i (K.cyclesMk x j hj hx)
      = L.cyclesMk ((φ.f i) x) j hj hy := by
  have hcm : L.iCycles i (HomologicalComplex.cyclesMap φ i (K.cyclesMk x j hj hx)) = (φ.f i) x := by
    have hh := congrArg (fun (g : K.cycles i ⟶ L.X i) => g (K.cyclesMk x j hj hx))
      (HomologicalComplex.cyclesMap_i (φ := φ) (i := i))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, CategoryTheory.ConcreteCategory.comp_apply,
      zc_iCycles_cyclesMk hj x hx] at hh ⊢
    exact hh
  refine (Preadditive.mono_iff_injective (L.iCycles i)).1 inferInstance ?_
  exact hcm.trans (zc_iCycles_cyclesMk hj ((φ.f i) x) hy).symm

theorem zc_castCycles_cyclesMk {K : ChainComplex (ModuleCat R) ℕ} {i i' j j' : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (hj' : (ComplexShape.down ℕ).next i' = j')
    (x : K.X i) (hx : K.d i j x = 0) (hx' : K.d i' j' (Work.SSSR.castElem K h x) = 0) :
    zcCastCycles K h (K.cyclesMk x j hj hx)
      = K.cyclesMk (Work.SSSR.castElem K h x) j' hj' hx' := by
  subst h
  have hjj : j = j' := hj.symm.trans hj'
  subst hjj
  refine (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance ?_
  change K.iCycles i (K.cyclesMk x j hj hx) = K.iCycles i (K.cyclesMk x j hj hx')
  rw [zc_iCycles_cyclesMk hj x hx]

/-! ## The transport of the fibre is the chain map `T.hom` -/

theorem zc_sCCFunctor_map_eqToHom {α : Type} (G : α → SSet.{0}) {a b : α} (h : a = b) :
    (Work.SSSR.sCCFunctor (R := R)).map (eqToHom (congrArg G h))
      = eqToHom (congrArg (fun x => (Work.SSSR.sCCFunctor (R := R)).obj (G x)) h) := by
  subst h
  simp

theorem zc_sCCMap_fibreTrans {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    Work.SSSR.sCCMap R (fibreTrans p b σ h)
      = (eqToIso (congrArg (fun x => Work.SSSR.fibreCC p x) h)).hom := by
  show Work.SSSR.sCCFunctor.map (eqToHom (congrArg (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h))
      = (eqToIso (congrArg (fun x => Work.SSSR.fibreCC p x) h)).hom
  rw [zc_sCCFunctor_map_eqToHom (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h,
    CategoryTheory.eqToIso.hom]

/-! ## The unfolding of `serreE1PieceIso` at `0` -/

theorem zc_serreE1PieceIso_zero_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ) :
    Work.SSSR.serreE1PieceIso p hfib 0 q σ =
      eqToIso (congrArg (fun i => (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homology i)
          (Nat.zero_add q)) ≪≫
        HomologicalComplex.homologyMapIso (Work.SSSR.pieceAlongZeroIso p σ) q := by
  rw [Work.SSSR.serreE1PieceIso.eq_1]
  exact zc_eqMpr_iso (A := fun i => (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homology i)
    (B := (Work.SSSR.Cohomology.singularChains R
      (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).homology q)
    (m := 0 + q) (n := q) (Nat.zero_add q)
    (HomologicalComplex.homologyMapIso (Work.SSSR.pieceAlongZeroIso p σ) q)

/-! ## `iotaF` on a generator -/

theorem zc_iotaF_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0 b σ h q)
        (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of R R) τ).hom 1)
      = (Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0 + q)
          (Work.SSSR.iotaTLift p hfib 0 b σ h q τ) := by
  have h1 := congrArg (fun (g : ModuleCat.of R R ⟶
      (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).X (0 + q)) => g.hom (1 : R))
    (Work.SSSR.iotaF_gen (p := p) (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
      0 b σ h q τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, Work.SSSR.eltHom_apply_one]
  rfl

theorem zc_cokerIso_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ ≫ (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom = 𝟙 _ := by
  haveI : IsIso (CategoryTheory.Limits.cokernel.π
      (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)) :=
    CategoryTheory.Limits.CokernelCofork.IsColimit.isIso_π
      (CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits.cokernel.π _)
        (CategoryTheory.Limits.cokernel.condition _))
      (CategoryTheory.Limits.cokernelIsCokernel _)
      (Work.SSSR.sCCMap_ι_eq_zero_of_eq_bot
        (Work.SSSR.bdryAlong_eq_bot_of_zero (Work.SSSR.sSingP p) σ))
  rw [show Work.SSSR.pieceAlongZeroCokerIso p σ
      = (CategoryTheory.asIso (CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι))).symm from rfl]
  rw [show Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ
      = (CategoryTheory.asIso (CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι))).hom from rfl]
  rw [← CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.self_symm_id, CategoryTheory.Iso.refl_hom]

theorem zc_pieceAlongZeroIso_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋q⦌) :
    ((Work.SSSR.pieceAlongZeroIso p σ).hom.f (0 + q))
        ((Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0 b σ h q)
          (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of R R) τ).hom 1))
      = (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          (Work.SSSR.iotaTLift p hfib 0 b σ h q τ) := by
  rw [zc_iotaF_apply p hfib b σ h q τ]
  have hfac : (Work.SSSR.pieceAlongZeroIso p σ).hom.f (0 + q)
      = (Work.SSSR.pieceAlongZeroCokerIso p σ).hom.f (0 + q) ≫
        (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q) := by
    rw [Work.SSSR.pieceAlongZeroIso]
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, HomologicalComplex.comp_f,
      CategoryTheory.eqToIso.hom, CategoryTheory.eqToHom_refl, HomologicalComplex.id_f,
      Category.comp_id, Work.SSSR.sCCMap]
  have hmor : (Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0 + q) ≫
      (Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom.f (0 + q) = 𝟙 _ := by
    have hh := congrArg (fun (g : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
        Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) => g.f (0 + q))
      (zc_cokerIso_comp p σ)
    simpa using hh
  have h2 : ((Work.SSSR.pieceAlongZeroCokerIso (R := R) p σ).hom.f (0 + q))
      ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (0 + q)
        (Work.SSSR.iotaTLift p hfib 0 b σ h q τ))
      = Work.SSSR.iotaTLift p hfib 0 b σ h q τ := by
    have hh := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + q) ⟶
        (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0 + q)) =>
      g (Work.SSSR.iotaTLift p hfib 0 b σ h q τ)) hmor
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, CategoryTheory.id_apply] using hh
  rw [hfac]
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply]
  rw [h2]
  rfl

theorem zc_castElem_sCC_ιChainComplex {X : SSet.{0}} {m n : ℕ} (h : m = n) (y : X _⦋m⦌) :
    (Work.SSSR.castElem (Work.SSSR.sCC R X) h) ((X.ιChainComplex (R := ModuleCat.of R R) y).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of R R) (castSimp h y)).hom 1 := by
  subst h
  simp [Work.SSSR.castElem, castSimp]

theorem zc_eqToHom_naturality {α : Type} {H : α → SSet.{0}} {Z : SSet.{0}} (J : ∀ i, H i ⟶ Z)
    {a b : α} (h : a = b) : eqToHom (congrArg H h) ≫ J b = J a := by
  subst h
  simp

theorem zc_eqToHom_symm_comp {α : Type} {H : α → SSet.{0}} {a b : α} (h : a = b) :
    eqToHom (congrArg H h.symm) ≫ eqToHom (congrArg H h) = 𝟙 (H b) := by
  subst h
  simp

theorem zc_phiAlong_comp_inv {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.phiAlong p σ ≫ (Work.SSSR.pullAlongVertexIsoIso p σ).hom = 𝟙 _ := by
  haveI := Work.SSSR.phiAlong_isIso p σ
  rw [Work.SSSR.pullAlongVertexIsoIso, CategoryTheory.Iso.symm_hom, CategoryTheory.asIso_inv]
  exact IsIso.hom_inv_id _

theorem zc_transport_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    eqToHom (congrArg (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h.symm) ≫
      fibreTrans p b σ h = 𝟙 _ := by
  rw [fibreTrans]
  exact zc_eqToHom_symm_comp (H := fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h

theorem zc_vertIncl_comp_lam {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    Work.SSSR.vertIncl p b 0 ≫
        (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0 b σ h ≫
          (Work.SSSR.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      = 𝟙 _ := by
  have hmain : Work.SSSR.vertIncl p b 0 ≫
        Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0 b σ h
      = eqToHom (congrArg (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h.symm) ≫
          Work.SSSR.phiAlong p σ := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [Category.assoc, Work.SSSR.ezSimplex_fst, Work.SSSR.vertIncl_fst, Category.assoc,
        Work.SSSR.phiAlong_fst]
      exact (zc_eqToHom_naturality (fun X => SSet.const (X := Work.SSSR.sSing
        (Work.SSSR.StemsB.fibre p X)) (Work.SSSR.ssetVertex 0)) h.symm).symm
    · rw [Category.assoc, Work.SSSR.ezSimplex_snd, Work.SSSR.liftFam_vert, Category.assoc,
        Work.SSSR.phiAlong_snd]
      exact (zc_eqToHom_naturality (fun X => Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p X))
        h.symm).symm
  rw [show Work.SSSR.vertIncl p b 0 ≫ (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) 0 b σ h ≫
        ((Work.SSSR.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h))
      = (Work.SSSR.vertIncl p b 0 ≫ Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) 0 b σ h) ≫
        ((Work.SSSR.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      from (Category.assoc _ _ _).symm]
  rw [hmain]
  rw [show (eqToHom (congrArg (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h.symm) ≫
        Work.SSSR.phiAlong p σ) ≫ ((Work.SSSR.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      = eqToHom (congrArg (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h.symm) ≫
        (Work.SSSR.phiAlong p σ ≫ ((Work.SSSR.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h))
      from Category.assoc _ _ _]
  rw [show Work.SSSR.phiAlong p σ ≫ ((Work.SSSR.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      = (Work.SSSR.phiAlong p σ ≫ (Work.SSSR.pullAlongVertexIsoIso p σ).hom) ≫ fibreTrans p b σ h
      from (Category.assoc _ _ _).symm]
  rw [zc_phiAlong_comp_inv, Category.id_comp, zc_transport_comp]

theorem zc_sCCMap_comp_apply {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (Work.SSSR.sCC R X).X n) :
    (Work.SSSR.sCCMap R k).f n ((Work.SSSR.sCCMap R g).f n x) = (Work.SSSR.sCCMap R (g ≫ k)).f n x := by
  rw [Work.SSSR.sCCMap_comp']; rfl

theorem zc_cyclesMk_congr {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) {x x' : K.X i} (heq : x = x')
    (hx : K.d i j x = 0) (hx' : K.d i j x' = 0) :
    K.cyclesMk x j hj hx = K.cyclesMk x' j hj hx' := by
  subst heq
  have hprov : hx' = hx := Subsingleton.elim hx' hx
  rw [hprov]

theorem zc_generic {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L)
    {i j : ℕ} (h : i = j) (x : K.X i) (hx : K.d i ((ComplexShape.down ℕ).next i) x = 0)
    (x'' : L.X j) (hx7 : Work.SSSR.castElem L h ((φ.f i) x) = x'')
    (hx'' : L.d j ((ComplexShape.down ℕ).next j) x'' = 0) :
    (HomologicalComplex.homologyMap φ j)
        ((eqToIso (congrArg (fun m => K.homology m) h)).hom
          ((K.homologyπ i)
            (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)))
      = L.homologyπ j (L.cyclesMk x'' ((ComplexShape.down ℕ).next j) rfl hx'') := by
  have hyA : L.d i ((ComplexShape.down ℕ).next i) ((φ.f i) x) = 0 :=
    zc_d_map_eq_zero φ x hx
  have hyB : L.d j ((ComplexShape.down ℕ).next j)
      (Work.SSSR.castElem L h ((φ.f i) x)) = 0 :=
    zc_d_castElem (K := L) h rfl ((φ.f i) x) hyA
  rw [zc_eqToIso_homologyπ h (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)]
  rw [zc_homologyMap_homologyπ φ j
    (zcCastCycles K h (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx))]
  rw [zc_castCycles_map φ h (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)]
  rw [zc_cyclesMap_cyclesMk φ rfl x hx hyA]
  rw [zc_castCycles_cyclesMk (K := L) h rfl rfl ((φ.f i) x) hyA hyB]
  exact congrArg (fun z => L.homologyπ j z)
    (zc_cyclesMk_congr (K := L) (i := j) rfl hx7 hyB hx'')

/-- In the case `h = rfl` (so `b = σ(v₀)`), the composite
`v₀ ≫ ι_Δ ≫ φ⁻¹` of the vertical vertex inclusion, the Eilenberg–Zilber lift of the vertex `σ` and
the inverse of `phiAlong` is the identity on `Sing F_b`. -/
theorem zc_vertIncl_comp_lam_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
        (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
            (Work.SSSR.sigmaVert σ) σ rfl ≫
          (Work.SSSR.pullAlongVertexIsoIso p σ).hom)
      = 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) := by
  have h1 := zc_vertIncl_comp_lam p hfib (Work.SSSR.sigmaVert σ) σ rfl
  have hc : fibreTrans p (Work.SSSR.sigmaVert σ) σ rfl
      = 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) := by
    rw [fibreTrans]
    simp only [CategoryTheory.eqToHom_refl]
  rw [hc, Category.comp_id] at h1
  exact h1

/-- **The chain-level computation of `Work.SSSR.serreE1PieceIsoZero`** in the case where the base
point is the vertex of `σ`: the composite of `(pieceAlongZeroIso p σ).hom` with the degree transport
`Nat.zero_add q` sends the Eilenberg–Zilber representative `Work.SSSR.iotaF … 0 b σ h q` of `τ` to
`τ`. -/
theorem zc_apply_gen {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (q : ℕ)
    (τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).obj
      (Opposite.op (SimplexCategory.mk q))) :
    Work.SSSR.castElem (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)) (Nat.zero_add q)
        (((Work.SSSR.pieceAlongZeroIso p σ).hom.f (0 + q))
          ((Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
              (Work.SSSR.sigmaVert σ) σ rfl q)
            (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).ιChainComplex
              (R := ModuleCat.of R R) τ).hom 1)))
      = (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).ιChainComplex
          (R := ModuleCat.of R R) τ).hom 1) := by
  set gg : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).X q :=
    (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of R R) τ).hom 1) with hgg
  set g0 : (Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).X
      (0 + q) :=
    (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of R R)
      ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).map
        (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
          (Work.SSSR.KunnethEZ.zSh q).2)) τ)).hom 1) with hg0
  have h1 : ((Work.SSSR.pieceAlongZeroIso p σ).hom.f (0 + q))
        ((Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
            (Work.SSSR.sigmaVert σ) σ rfl q) gg)
      = (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          (Work.SSSR.iotaTLift p hfib 0 (Work.SSSR.sigmaVert σ) σ rfl q τ) :=
    zc_pieceAlongZeroIso_apply p hfib (Work.SSSR.sigmaVert σ) σ rfl q τ
  have h2 : (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        (Work.SSSR.iotaTLift p hfib 0 (Work.SSSR.sigmaVert σ) σ rfl q τ)
      = (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q)
            (Work.SSSR.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0))
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
              (Work.SSSR.stdIdSimplex 0) τ)) :=
    congrArg
      (fun y => (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q) y)
      (show Work.SSSR.iotaTLift p hfib 0 (Work.SSSR.sigmaVert σ) σ rfl q τ
          = (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q)
              (Work.SSSR.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0))
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
                (Work.SSSR.stdIdSimplex 0) τ) from rfl)
  have h3 : (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q)
          (Work.SSSR.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0))
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))
            (Work.SSSR.stdIdSimplex 0) τ))
      = (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q)
            ((Work.SSSR.sCCMap R (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0)).f (0 + q) g0)) :=
    congrArg
      (fun y => (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q) y))
      (Work.SSSR.SZero.ezGen_zero_eq_vertIncl p (Work.SSSR.sigmaVert σ) q τ)
  have h4 : (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) 0 (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q)
          ((Work.SSSR.sCCMap R (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0)).f (0 + q) g0))
      = (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          ((Work.SSSR.sCCMap R (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
            Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
              (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q) g0) :=
    congrArg
      (fun y => (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q) y)
      (zc_sCCMap_comp_apply (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0)
        (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
          (Work.SSSR.sigmaVert σ) σ rfl) g0)
  have h5 : (Work.SSSR.sCCMap R ((Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSSR.sCCMap R (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
            Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
              (Work.SSSR.sigmaVert σ) σ rfl)).f (0 + q) g0)
      = (Work.SSSR.sCCMap R ((Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
            Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
              (Work.SSSR.sigmaVert σ) σ rfl) ≫
          (Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q) g0 :=
    zc_sCCMap_comp_apply
      (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
        Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
          (Work.SSSR.sigmaVert σ) σ rfl)
      ((Work.SSSR.pullAlongVertexIsoIso p σ).hom) g0
  have hcomp : (Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
        Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
          (Work.SSSR.sigmaVert σ) σ rfl) ≫ (Work.SSSR.pullAlongVertexIsoIso p σ).hom
      = 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))) := by
    rw [Category.assoc]
    exact zc_vertIncl_comp_lam_zero p hfib σ
  have h6 : (Work.SSSR.sCCMap R ((Work.SSSR.vertIncl p (Work.SSSR.sigmaVert σ) 0 ≫
          Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) 0
            (Work.SSSR.sigmaVert σ) σ rfl) ≫
        (Work.SSSR.pullAlongVertexIsoIso p σ).hom)).f (0 + q) g0
      = (Work.SSSR.sCCMap R (𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))))).f
          (0 + q) g0 :=
    congrArg (fun t => (Work.SSSR.sCCMap R t).f (0 + q) g0) hcomp
  have h7 : (Work.SSSR.sCCMap R (𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert σ))))).f (0 + q) g0 = g0 := by
    simp only [Work.SSSR.sCCMap, CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
      CategoryTheory.id_apply]
  have hcast : Work.SSSR.castElem (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)) (Nat.zero_add q)
        g0 = gg := by
    rw [hg0, zc_castElem_sCC_ιChainComplex (Nat.zero_add q)
      ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ))).map
        (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
          (Work.SSSR.KunnethEZ.zSh q).2)) τ),
      Work.SSSR.SZero.castSimp_zSh_bHom q τ, hgg]
  rw [h1, h2, h3, h4, h5, h6, h7]
  exact hcast

end

end Work.SSSR.SZero

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
end Work.SSSR
