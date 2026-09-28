import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.SZero.Defs
import Submission.Work.SSS.SZero.ezGen_zero_eq_vertIncl
import Submission.Work.SSS.SZero.castSimp_zSh_bHom
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.pieceBdryHornIso
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.KunnethEZ.EZGenX

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# The base case `P = 0` of the σ-piece connecting map

Auxiliary lemmas for `Work.SSS.serreE1PieceIsoZero`.  They are stated in the namespace
`Work.SSS.SZero` and concern the bookkeeping of the degree transports
(`Work.SSS.castElem`, `Work.SSS.SZero.castSimp`), the cycle/homology functors of a chain complex,
and the chain-level computation of the iterated connecting map on the Eilenberg–Zilber
representative `Work.SSS.iotaTLift p hfib 0 b σ h q τ` of a fibre class `τ`.
-/

namespace Work.SSS.SZero
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

theorem zc_eqMpr_iso {A : ℕ → ModuleCat ℤ} {B : ModuleCat ℤ} {m n : ℕ} (h : m = n)
    (e : A n ≅ B) : Eq.mpr (congrArg (fun i => A i ≅ B) h) e = eqToIso (congrArg A h) ≪≫ e := by
  subst h
  simp

theorem zc_castElem_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (x : K.X i) : Work.SSS.castElem L h ((φ.f i) x) = (φ.f j) (Work.SSS.castElem K h x) := by
  subst h
  simp [Work.SSS.castElem]

def zcCastCycles (K : ChainComplex (ModuleCat ℤ) ℕ) {i j : ℕ} (h : i = j) (x : K.cycles i) :
    K.cycles j :=
  (eqToHom (congrArg (fun m => K.cycles m) h)).hom x

theorem zc_iCycles_castCycles {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    K.iCycles j (zcCastCycles K h z) = Work.SSS.castElem K h (K.iCycles i z) := by
  subst h
  rfl

theorem zc_castCycles_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    HomologicalComplex.cyclesMap φ j (zcCastCycles K h z)
      = zcCastCycles L h (HomologicalComplex.cyclesMap φ i z) := by
  subst h
  simp [zcCastCycles]

theorem zc_homologyMap_homologyπ {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) z)
      = (L.homologyπ i) (HomologicalComplex.cyclesMap φ i z) :=
  congrArg (fun (f : K.cycles i ⟶ L.homology i) => f z)
    (HomologicalComplex.homologyπ_naturality φ i)

theorem zc_eqToIso_homologyπ {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    (eqToIso (congrArg (fun m => K.homology m) h)).hom ((K.homologyπ i) z)
      = (K.homologyπ j) (zcCastCycles K h z) := by
  subst h
  simp [zcCastCycles]

theorem zc_iCycles_cyclesMk {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

theorem zc_d_map_eq_zero {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (x : K.X i) (hx : K.d i j x = 0) : L.d i j ((φ.f i) x) = 0 := by
  have h := congrArg (fun (g : K.X i ⟶ L.X j) => g x) (HomologicalComplex.Hom.comm φ i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hx, map_zero] at h
  exact h

theorem zc_d_castElem {K : ChainComplex (ModuleCat ℤ) ℕ} {i i' j : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.d i' ((ComplexShape.down ℕ).next i') (Work.SSS.castElem K h x) = 0 := by
  subst h
  rw [← hj] at hx
  simpa [Work.SSS.castElem] using hx

theorem zc_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
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

theorem zc_castCycles_cyclesMk {K : ChainComplex (ModuleCat ℤ) ℕ} {i i' j j' : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (hj' : (ComplexShape.down ℕ).next i' = j')
    (x : K.X i) (hx : K.d i j x = 0) (hx' : K.d i' j' (Work.SSS.castElem K h x) = 0) :
    zcCastCycles K h (K.cyclesMk x j hj hx)
      = K.cyclesMk (Work.SSS.castElem K h x) j' hj' hx' := by
  subst h
  have hjj : j = j' := hj.symm.trans hj'
  subst hjj
  refine (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance ?_
  change K.iCycles i (K.cyclesMk x j hj hx) = K.iCycles i (K.cyclesMk x j hj hx')
  rw [zc_iCycles_cyclesMk hj x hx]

theorem zc_inv_f_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (π : K ⟶ L) [IsIso π] (n : ℕ)
    (x : K.X n) : ((CategoryTheory.inv π).f n) ((π.f n) x) = x := by
  have h : π ≫ CategoryTheory.inv π = 𝟙 K := IsIso.hom_inv_id π
  have h2 := congrArg (fun (g : K ⟶ K) => (g.f n) x) h
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, CategoryTheory.id_apply] at h2
  exact h2

/-! ## The transport of the fibre is the chain map `T.hom` -/

theorem zc_sCCFunctor_map_eqToHom {α : Type} (G : α → SSet.{0}) {a b : α} (h : a = b) :
    Work.SSS.sCCFunctor.map (eqToHom (congrArg G h))
      = eqToHom (congrArg (fun x => Work.SSS.sCCFunctor.obj (G x)) h) := by
  subst h
  simp

theorem zc_sCCMap_fibreTrans {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    Work.SSS.sCCMap (fibreTrans p b σ h)
      = (eqToIso (congrArg (fun x => Work.SSS.fibreCC p x) h)).hom := by
  show Work.SSS.sCCFunctor.map (eqToHom (congrArg (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h))
      = (eqToIso (congrArg (fun x => Work.SSS.fibreCC p x) h)).hom
  rw [zc_sCCFunctor_map_eqToHom (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h,
    CategoryTheory.eqToIso.hom]

/-! ## The unfolding of `serreE1PieceIso` at `0` -/

theorem zc_serreE1PieceIso_zero_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ) :
    Work.SSS.serreE1PieceIso p hfib 0 q σ =
      eqToIso (congrArg (fun i => (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).homology i)
          (Nat.zero_add q)) ≪≫
        HomologicalComplex.homologyMapIso (Work.SSS.pieceAlongZeroIso p σ) q := by
  rw [Work.SSS.serreE1PieceIso.eq_1]
  exact @zc_eqMpr_iso (fun i => (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).homology i)
    ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).homology q)
    (0 + q) q (Nat.zero_add q) (HomologicalComplex.homologyMapIso (Work.SSS.pieceAlongZeroIso p σ) q)

/-! ## `iotaF` on a generator -/

theorem zc_iotaF_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h q)
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1)
      = (Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0 + q)
          (Work.SSS.iotaTLift p hfib 0 b σ h q τ) := by
  have h1 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).X (0 + q)) => g.hom (1 : ℤ))
    (Work.SSS.iotaF_gen (p := p) (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
      0 b σ h q τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, Work.SSS.eltHom_apply_one]
  rfl

theorem zc_cokerIso_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.pieceπOf (Work.SSS.sSingP p) σ ≫ (Work.SSS.pieceAlongZeroCokerIso p σ).hom = 𝟙 _ := by
  haveI : IsIso (CategoryTheory.Limits.cokernel.π
      (Work.SSS.sCCMap (Work.SSS.bdryAlong (Work.SSS.sSingP p) σ).ι)) :=
    CategoryTheory.Limits.CokernelCofork.IsColimit.isIso_π
      (CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits.cokernel.π _)
        (CategoryTheory.Limits.cokernel.condition _))
      (CategoryTheory.Limits.cokernelIsCokernel _)
      (Work.SSS.sCCMap_ι_eq_zero_of_eq_bot
        (Work.SSS.bdryAlong_eq_bot_of_zero (Work.SSS.sSingP p) σ))
  rw [show Work.SSS.pieceAlongZeroCokerIso p σ
      = (CategoryTheory.asIso (CategoryTheory.Limits.cokernel.π
          (Work.SSS.sCCMap (Work.SSS.bdryAlong (Work.SSS.sSingP p) σ).ι))).symm from rfl]
  rw [show Work.SSS.pieceπOf (Work.SSS.sSingP p) σ
      = (CategoryTheory.asIso (CategoryTheory.Limits.cokernel.π
          (Work.SSS.sCCMap (Work.SSS.bdryAlong (Work.SSS.sSingP p) σ).ι))).hom from rfl]
  rw [← CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.self_symm_id, CategoryTheory.Iso.refl_hom]

theorem zc_pieceAlongZeroIso_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    ((Work.SSS.pieceAlongZeroIso p σ).hom.f (0 + q))
        ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h q)
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1))
      = (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          (Work.SSS.iotaTLift p hfib 0 b σ h q τ) := by
  rw [zc_iotaF_apply p hfib b σ h q τ]
  have hfac : (Work.SSS.pieceAlongZeroIso p σ).hom.f (0 + q)
      = (Work.SSS.pieceAlongZeroCokerIso p σ).hom.f (0 + q) ≫
        (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q) := by
    rw [Work.SSS.pieceAlongZeroIso]
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, HomologicalComplex.comp_f,
      CategoryTheory.eqToIso.hom, CategoryTheory.eqToHom_refl, HomologicalComplex.id_f,
      Category.comp_id, Work.SSS.sCCMap]
  have hmor : (Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0 + q) ≫
      (Work.SSS.pieceAlongZeroCokerIso p σ).hom.f (0 + q) = 𝟙 _ := by
    have hh := congrArg (fun (g : Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ) ⟶
        Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)) => g.f (0 + q))
      (zc_cokerIso_comp p σ)
    simpa using hh
  have h2 : ((Work.SSS.pieceAlongZeroCokerIso p σ).hom.f (0 + q))
      ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (0 + q)
        (Work.SSS.iotaTLift p hfib 0 b σ h q τ))
      = Work.SSS.iotaTLift p hfib 0 b σ h q τ := by
    have hh := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X (0 + q) ⟶
        (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X (0 + q)) =>
      g (Work.SSS.iotaTLift p hfib 0 b σ h q τ)) hmor
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, CategoryTheory.id_apply] using hh
  rw [hfac]
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply]
  rw [h2]
  rfl

/-! ## The Eilenberg-Zilber chain of `(v₀,τ)` -/

theorem zc_castElem_ιChainComplex {X : SSet.{0}} {m n : ℕ} (h : m = n) (y : X _⦋m⦌) :
    (Work.SSS.castElem (X.chainComplex (ModuleCat.of ℤ ℤ)) h)
        ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) y).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) (castSimp h y)).hom 1 := by
  subst h
  simp [Work.SSS.castElem, castSimp]

theorem zc_castElem_sCC_ιChainComplex {X : SSet.{0}} {m n : ℕ} (h : m = n) (y : X _⦋m⦌) :
    (Work.SSS.castElem (Work.SSS.sCC X) h) ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) y).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) (castSimp h y)).hom 1 := by
  subst h
  simp [Work.SSS.castElem, castSimp]

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
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.phiAlong p σ ≫ (Work.SSS.pullAlongVertexIsoIso p σ).hom = 𝟙 _ := by
  haveI := Work.SSS.phiAlong_isIso p σ
  rw [Work.SSS.pullAlongVertexIsoIso, CategoryTheory.Iso.symm_hom, CategoryTheory.asIso_inv]
  exact IsIso.hom_inv_id _

theorem zc_transport_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    eqToHom (congrArg (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h.symm) ≫
      fibreTrans p b σ h = 𝟙 _ := by
  rw [fibreTrans]
  exact zc_eqToHom_symm_comp (H := fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h

theorem zc_vertIncl_comp_lam {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    Work.SSS.vertIncl p b 0 ≫
        (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h ≫
          (Work.SSS.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      = 𝟙 _ := by
  have hmain : Work.SSS.vertIncl p b 0 ≫
        Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h
      = eqToHom (congrArg (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h.symm) ≫
          Work.SSS.phiAlong p σ := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [Category.assoc, Work.SSS.ezSimplex_fst, Work.SSS.vertIncl_fst, Category.assoc,
        Work.SSS.phiAlong_fst]
      exact (zc_eqToHom_naturality (fun X => SSet.const (X := Work.SSS.sSing
        (Work.StemsB.fibre p X)) (Work.SSS.ssetVertex 0)) h.symm).symm
    · rw [Category.assoc, Work.SSS.ezSimplex_snd, Work.SSS.liftFam_vert, Category.assoc,
        Work.SSS.phiAlong_snd]
      exact (zc_eqToHom_naturality (fun X => Work.SSS.sSingP (Work.StemsB.fibreIncl p X))
        h.symm).symm
  rw [show Work.SSS.vertIncl p b 0 ≫ (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) 0 b σ h ≫
        ((Work.SSS.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h))
      = (Work.SSS.vertIncl p b 0 ≫ Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) 0 b σ h) ≫
        ((Work.SSS.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      from (Category.assoc _ _ _).symm]
  rw [hmain]
  rw [show (eqToHom (congrArg (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h.symm) ≫
        Work.SSS.phiAlong p σ) ≫ ((Work.SSS.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      = eqToHom (congrArg (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h.symm) ≫
        (Work.SSS.phiAlong p σ ≫ ((Work.SSS.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h))
      from Category.assoc _ _ _]
  rw [show Work.SSS.phiAlong p σ ≫ ((Work.SSS.pullAlongVertexIsoIso p σ).hom ≫ fibreTrans p b σ h)
      = (Work.SSS.phiAlong p σ ≫ (Work.SSS.pullAlongVertexIsoIso p σ).hom) ≫ fibreTrans p b σ h
      from (Category.assoc _ _ _).symm]
  rw [zc_phiAlong_comp_inv, Category.id_comp, zc_transport_comp]

theorem zc_comp_f_apply {K L M : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (ψ : L ⟶ M)
    (n : ℕ) (x : K.X n) : (ψ.f n) ((φ.f n) x) = ((φ ≫ ψ).f n) x := by
  rw [HomologicalComplex.comp_f, CategoryTheory.comp_apply]

theorem zc_sCCMap_comp_apply {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (Work.SSS.sCC X).X n) :
    (Work.SSS.sCCMap k).f n ((Work.SSS.sCCMap g).f n x) = (Work.SSS.sCCMap (g ≫ k)).f n x := by
  rw [Work.SSS.sCCMap_comp']; rfl

theorem zc_sCCMap_comp_apply3 {X Y Z W : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) (l : Z ⟶ W)
    {n : ℕ} (x : (Work.SSS.sCC X).X n) :
    (Work.SSS.sCCMap l).f n ((Work.SSS.sCCMap k).f n ((Work.SSS.sCCMap g).f n x))
      = (Work.SSS.sCCMap (g ≫ k ≫ l)).f n x := by
  have h1 : (Work.SSS.sCCMap k).f n ((Work.SSS.sCCMap g).f n x)
      = (Work.SSS.sCCMap (g ≫ k)).f n x := by
    have h := congrArg (fun (t : Work.SSS.sCC X ⟶ Work.SSS.sCC Z) => (t.f n) x)
      (Work.SSS.sCCMap_comp' g k)
    simpa only [HomologicalComplex.comp_f, CategoryTheory.comp_apply] using h.symm
  have h2 : (Work.SSS.sCCMap l).f n ((Work.SSS.sCCMap (g ≫ k)).f n x)
      = (Work.SSS.sCCMap ((g ≫ k) ≫ l)).f n x := by
    have h := congrArg (fun (t : Work.SSS.sCC X ⟶ Work.SSS.sCC W) => (t.f n) x)
      (Work.SSS.sCCMap_comp' (g ≫ k) l)
    simpa only [HomologicalComplex.comp_f, CategoryTheory.comp_apply] using h.symm
  have h3 : (Work.SSS.sCCMap ((g ≫ k) ≫ l)).f n x
      = (Work.SSS.sCCMap (g ≫ k ≫ l)).f n x :=
    congrArg (fun (t : X ⟶ W) => (Work.SSS.sCCMap t).f n x) (Category.assoc g k l)
  exact (congrArg (fun z => (Work.SSS.sCCMap l).f n z) h1).trans (h2.trans h3)

theorem zc_cyclesMk_congr {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) {x x' : K.X i} (heq : x = x')
    (hx : K.d i j x = 0) (hx' : K.d i j x' = 0) :
    K.cyclesMk x j hj hx = K.cyclesMk x' j hj hx' := by
  subst heq
  have hprov : hx' = hx := Subsingleton.elim hx' hx
  rw [hprov]

/-- **Generic form of the calculation of `serreE1PieceIso` at `P = 0`.**

Let `φ : K ⟶ L` and `T : L ⟶ M` be chain maps, `h : i = j` an equality of degrees, and
`x : K.X i` a cycle of `K` in degree `i` (with cycle condition `hx`).  Assume that the transport of
`(φ ≫ T).f i x` from degree `i` to degree `j` equals a cycle `x''` of `M` in degree `j`
(hypothesis `hx7`, the chain-level content of the calculation), with `hx''` its cycle condition.
Then the composite of the degree transport `H_i(K) ≅ H_j(K)`, the homology map of `φ` and the
homology map of `T` sends the homology class of `x` to the homology class of `x''`. -/
theorem zc_key_generic {K L M : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (T : L ⟶ M)
    {i j : ℕ} (h : i = j) (x : K.X i) (hx : K.d i ((ComplexShape.down ℕ).next i) x = 0)
    (x'' : M.X j) (hx7 : Work.SSS.castElem M h ((φ ≫ T).f i x) = x'')
    (hx'' : M.d j ((ComplexShape.down ℕ).next j) x'' = 0) :
    (HomologicalComplex.homologyMap T j)
        ((HomologicalComplex.homologyMap φ j)
          ((eqToIso (congrArg (fun m => K.homology m) h)).hom
            ((K.homologyπ i)
              (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx))))
      = M.homologyπ j (M.cyclesMk x'' ((ComplexShape.down ℕ).next j) rfl hx'') := by
  have hyA : M.d i ((ComplexShape.down ℕ).next i) ((φ ≫ T).f i x) = 0 :=
    zc_d_map_eq_zero (φ ≫ T) x hx
  have hyB : M.d j ((ComplexShape.down ℕ).next j)
      (Work.SSS.castElem M h ((φ ≫ T).f i x)) = 0 :=
    zc_d_castElem (K := M) h rfl ((φ ≫ T).f i x) hyA
  rw [← CategoryTheory.comp_apply]
  rw [← HomologicalComplex.homologyMap_comp]
  rw [zc_eqToIso_homologyπ h (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)]
  rw [zc_homologyMap_homologyπ (φ ≫ T) j
    (zcCastCycles K h (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx))]
  rw [zc_castCycles_map (φ ≫ T) h (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)]
  rw [zc_cyclesMap_cyclesMk (φ ≫ T) rfl x hx hyA]
  rw [zc_castCycles_cyclesMk (K := M) h rfl rfl ((φ ≫ T).f i x) hyA hyB]
  exact congrArg (fun z => M.homologyπ j z)
    (zc_cyclesMk_congr (K := M) (i := j) rfl hx7 hyB hx'')

theorem zc_generic {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    {i j : ℕ} (h : i = j) (x : K.X i) (hx : K.d i ((ComplexShape.down ℕ).next i) x = 0)
    (x'' : L.X j) (hx7 : Work.SSS.castElem L h ((φ.f i) x) = x'')
    (hx'' : L.d j ((ComplexShape.down ℕ).next j) x'' = 0) :
    (HomologicalComplex.homologyMap φ j)
        ((eqToIso (congrArg (fun m => K.homology m) h)).hom
          ((K.homologyπ i)
            (K.cyclesMk x ((ComplexShape.down ℕ).next i) rfl hx)))
      = L.homologyπ j (L.cyclesMk x'' ((ComplexShape.down ℕ).next j) rfl hx'') := by
  have hyA : L.d i ((ComplexShape.down ℕ).next i) ((φ.f i) x) = 0 :=
    zc_d_map_eq_zero φ x hx
  have hyB : L.d j ((ComplexShape.down ℕ).next j)
      (Work.SSS.castElem L h ((φ.f i) x)) = 0 :=
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
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
        (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
            (Work.SSS.sigmaVert σ) σ rfl ≫
          (Work.SSS.pullAlongVertexIsoIso p σ).hom)
      = 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))) := by
  have h1 := zc_vertIncl_comp_lam p hfib (Work.SSS.sigmaVert σ) σ rfl
  have hc : fibreTrans p (Work.SSS.sigmaVert σ) σ rfl
      = 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))) := by
    rw [fibreTrans]
    simp only [CategoryTheory.eqToHom_refl]
  rw [hc, Category.comp_id] at h1
  exact h1

/-- **The chain-level computation of `Work.SSS.serreE1PieceIsoZero`** in the case where the base
point is the vertex of `σ`: the composite of `(pieceAlongZeroIso p σ).hom` with the degree transport
`Nat.zero_add q` sends the Eilenberg–Zilber representative `Work.SSS.iotaF … 0 b σ h q` of `τ` to
`τ`. -/
theorem zc_apply_gen {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (q : ℕ)
    (τ : (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).obj
      (Opposite.op (SimplexCategory.mk q))) :
    Work.SSS.castElem (Work.SSS.fibreCC p (Work.SSS.sigmaVert σ)) (Nat.zero_add q)
        (((Work.SSS.pieceAlongZeroIso p σ).hom.f (0 + q))
          ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
              (Work.SSS.sigmaVert σ) σ rfl q)
            (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) τ).hom 1)))
      = (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) := by
  set gg : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).X q :=
    (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) τ).hom 1) with hgg
  set g0 : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).X
      (0 + q) :=
    (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ)
      ((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).map
        (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
          (Work.KunnethEZ.zSh q).2)) τ)).hom 1) with hg0
  have h1 : ((Work.SSS.pieceAlongZeroIso p σ).hom.f (0 + q))
        ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
            (Work.SSS.sigmaVert σ) σ rfl q) gg)
      = (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          (Work.SSS.iotaTLift p hfib 0 (Work.SSS.sigmaVert σ) σ rfl q τ) :=
    zc_pieceAlongZeroIso_apply p hfib (Work.SSS.sigmaVert σ) σ rfl q τ
  have h2 : (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        (Work.SSS.iotaTLift p hfib 0 (Work.SSS.sigmaVert σ) σ rfl q τ)
      = (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q)
            (Work.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0))
              (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
              (Work.SSS.stdIdSimplex 0) τ)) :=
    congrArg
      (fun y => (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q) y)
      (show Work.SSS.iotaTLift p hfib 0 (Work.SSS.sigmaVert σ) σ rfl q τ
          = (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q)
              (Work.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0))
                (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
                (Work.SSS.stdIdSimplex 0) τ) from rfl)
  have h3 : (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q)
          (Work.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0))
            (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))
            (Work.SSS.stdIdSimplex 0) τ))
      = (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
              (Work.SSS.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q)
            ((Work.SSS.sCCMap (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0)).f (0 + q) g0)) :=
    congrArg
      (fun y => (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q) y))
      (Work.SSS.SZero.ezGen_zero_eq_vertIncl p (Work.SSS.sigmaVert σ) q τ)
  have h4 : (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) 0 (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q)
          ((Work.SSS.sCCMap (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0)).f (0 + q) g0))
      = (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          ((Work.SSS.sCCMap (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
            Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
              (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q) g0) :=
    congrArg
      (fun y => (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q) y)
      (zc_sCCMap_comp_apply (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0)
        (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
          (Work.SSS.sigmaVert σ) σ rfl) g0)
  have h5 : (Work.SSS.sCCMap ((Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q)
        ((Work.SSS.sCCMap (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
            Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
              (Work.SSS.sigmaVert σ) σ rfl)).f (0 + q) g0)
      = (Work.SSS.sCCMap ((Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
            Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
              (Work.SSS.sigmaVert σ) σ rfl) ≫
          (Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q) g0 :=
    zc_sCCMap_comp_apply
      (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
        Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
          (Work.SSS.sigmaVert σ) σ rfl)
      ((Work.SSS.pullAlongVertexIsoIso p σ).hom) g0
  have hcomp : (Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
        Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
          (Work.SSS.sigmaVert σ) σ rfl) ≫ (Work.SSS.pullAlongVertexIsoIso p σ).hom
      = 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))) := by
    rw [Category.assoc]
    exact zc_vertIncl_comp_lam_zero p hfib σ
  have h6 : (Work.SSS.sCCMap ((Work.SSS.vertIncl p (Work.SSS.sigmaVert σ) 0 ≫
          Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
            (Work.SSS.sigmaVert σ) σ rfl) ≫
        (Work.SSS.pullAlongVertexIsoIso p σ).hom)).f (0 + q) g0
      = (Work.SSS.sCCMap (𝟙 (Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))))).f
          (0 + q) g0 :=
    congrArg (fun t => (Work.SSS.sCCMap t).f (0 + q) g0) hcomp
  have h7 : (Work.SSS.sCCMap (𝟙 (Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert σ))))).f (0 + q) g0 = g0 := by
    simp only [Work.SSS.sCCMap, CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
      CategoryTheory.id_apply]
  have hcast : Work.SSS.castElem (Work.SSS.fibreCC p (Work.SSS.sigmaVert σ)) (Nat.zero_add q)
        g0 = gg := by
    rw [hg0, zc_castElem_sCC_ιChainComplex (Nat.zero_add q)
      ((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).map
        (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
          (Work.KunnethEZ.zSh q).2)) τ),
      Work.SSS.SZero.castSimp_zSh_bHom q τ, hgg]
  rw [h1, h2, h3, h4, h5, h6, h7]
  exact hcast

end

end Work.SSS.SZero

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

/-- **The base case `P = 0` of `Work.SSS.serreE1PieceIso_iota`.**  For a vertex `σ : Δ[0] ⟶ Sing B`
of the base, a point `b : B` with `sigmaVert σ = b` and a cycle `τ` of the fibre `F_b` in degree `q`,
the iterated connecting map `ε_σ = Work.SSS.serreE1PieceIso p hfib 0 q σ` sends the class of the
explicit cycle `ι_σ τ` to (`±`) the class of `τ` (after transporting `H_q(F_{σ(v₀)})` to `H_q(F_b)`
along `h`).  The sign is *uniform* in `q` and `τ`.

Here `∂T_σ = ⊥` for a vertex, so `Work.SSS.pieceAlongZeroIso p σ` identifies the piece with
`C(T_σ)`, which `Work.SSS.pullAlongVertexIsoIso` identifies with `C(F_{σ(v₀)})`; the EZ chain
`ι_σ τ = iotaTLift p hfib 0 b σ h q τ` is the shuffle chain of the constant `q`-simplex of `Δ[0]`
and `τ`, which is exactly the image of `τ` under the inclusion `Sing F_b ⟶ T_σ`
(`Work.SSS.liftFam_vert`, `Work.SSS.phiAlong_snd`), so the composite is the identity on chains.

Proof route: unfold `Work.SSS.serreE1PieceIso` at `0` (its successor-free branch is
`HomologicalComplex.homologyMapIso (pieceAlongZeroIso …)` up to the `Nat.zero_add` cast), rewrite
`Work.SSS.pieceAlongZeroIso` as `pieceAlongZeroCokerIso ≪≫ mapIso pullAlongVertexIsoIso ≪≫ eqToIso
rfl`, use that `(asIso (cokernel.π …)).inv ≫ cokernel.π … = 𝟙` to strip the cokernel projection
(everything is a quotient by `⊥`), and then compute `(pullAlongVertexIsoIso p σ).hom` on
`iotaTLift p hfib 0 b σ h q τ`: `iotaTLift` is `genP` of the constant `q`-simplex and `τ`
(`Work.KunnethEZ.ezGen_zero_single`), whose image under `sCCMap ezSimplex` is the simplex
`ezSimplex (vertIncl τ)` with second projection `Sing p (fibreIncl) τ`
(`Work.SSS.liftFam_vert`), and `Work.SSS.pullAlongVertexIsoIso` is `(asIso (phiAlong p σ)).symm`
with `Work.SSS.phiAlong_snd` saying exactly that this is `τ`.  Finally use
`HomologicalComplex.homologyπ_naturality` to descend to homology classes. -/
theorem serreE1PieceIsoZero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (q : ℕ) (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌)
        (hτ : (Work.SSS.fibreCC p b).d q ((ComplexShape.down ℕ).next q)
            (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0)
        (hcyc : (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (0+q)
            ((ComplexShape.down ℕ).next (0+q))
            ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h q)
              (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0),
      (HomologicalComplex.homologyMap
          (eqToIso (congrArg (Work.SSS.fibreCC p) h)).hom q)
        ((Work.SSS.serreE1PieceIso p hfib 0 q σ).hom
          (HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (0+q)
            (HomologicalComplex.cyclesMk (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ)
              ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h q)
                (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
                  (R := ModuleCat.of ℤ ℤ) τ).hom 1))
              ((ComplexShape.down ℕ).next (0+q)) rfl hcyc)))
      = c • HomologicalComplex.homologyπ (Work.SSS.fibreCC p b) q
          (HomologicalComplex.cyclesMk (Work.SSS.fibreCC p b)
            (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) τ).hom 1)
            ((ComplexShape.down ℕ).next q) rfl hτ) := by
  refine ⟨1, Or.inl rfl, fun q τ hτ hcyc => ?_⟩
  rw [← Work.SSS.SZero.zc_sCCMap_fibreTrans p b σ h]
  subst h
  have hE : Work.SSS.sCCMap (Work.SSS.SZero.fibreTrans p (Work.SSS.sigmaVert σ) σ rfl)
      = 𝟙 (Work.SSS.fibreCC p (Work.SSS.sigmaVert σ)) := by
    rw [Work.SSS.SZero.fibreTrans]
    simp only [CategoryTheory.eqToHom_refl, Work.SSS.sCCMap, CategoryTheory.Functor.map_id]
  rw [hE]
  simp only [HomologicalComplex.homologyMap_id, CategoryTheory.id_apply]
  rw [one_smul]
  rw [Work.SSS.SZero.zc_serreE1PieceIso_zero_eq p hfib (Work.SSS.sigmaVert σ) σ rfl q]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.comp_apply]
  exact Work.SSS.SZero.zc_generic (Work.SSS.pieceAlongZeroIso p σ).hom (Nat.zero_add q)
    ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
        (Work.SSS.sigmaVert σ) σ rfl q)
      (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1))
    hcyc
    (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) τ).hom 1)
    (Work.SSS.SZero.zc_apply_gen p hfib σ q τ)
    hτ

end Work.SSS
