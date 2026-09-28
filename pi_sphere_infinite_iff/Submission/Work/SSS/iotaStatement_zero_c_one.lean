import Mathlib
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.SZero.Defs
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.KunnethEZ.EZGenX

/-!
# The base case `P = 0` of `ε_σ ∘ ι_σ = ±𝟙`, with sign `c = 1`

This file proves `Work.SSS.iotaStatement_zero_c_one`: for a vertex `σ` of `Sing B` and a cycle `τ`
of the fibre `F_b`, the iterated last-face connecting map
`Work.SSS.serreE1PieceIso p hfib 0 q σ = H(pieceAlongZeroIso p σ)` sends the homology class of the
explicit Eilenberg–Zilber cycle
`Work.SSS.iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 b σ h q τ` to the class of `τ`,
with sign `+1` (no EZ shuffle sign is acquired at `P = 0`).

The argument is: the composite of the Eilenberg–Zilber chain map with the vertex identification is
the identity on chains, and the degree transport `Nat.zero_add q` is undone by the `(0,q)`-shuffle
reindexing lemma `izo_castSimp_zSh_bHom`.  All the elementary transport lemmas about
`Work.SSS.castElem`, `cycles`/`cyclesMap` and `sCCMap` are collected at the top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-! ## Elementary transports of chain complexes along degree equalities -/

theorem izo_eqMpr_iso {A : ℕ → ModuleCat ℤ} {B : ModuleCat ℤ} {m n : ℕ} (h : m = n)
    (e : A n ≅ B) : Eq.mpr (congrArg (fun i => A i ≅ B) h) e = eqToIso (congrArg A h) ≪≫ e := by
  subst h
  simp

theorem izo_castElem_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (x : K.X i) : castElem L h ((φ.f i) x) = (φ.f j) (castElem K h x) := by
  subst h
  simp [castElem]

/-- Transport of an element of the cycles of a chain complex along an equality of degrees. -/
def izoCastCycles (K : ChainComplex (ModuleCat ℤ) ℕ) {i j : ℕ} (h : i = j) (x : K.cycles i) :
    K.cycles j :=
  (eqToHom (congrArg (fun m => K.cycles m) h)).hom x

theorem izo_castCycles_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    HomologicalComplex.cyclesMap φ j (izoCastCycles K h z)
      = izoCastCycles L h (HomologicalComplex.cyclesMap φ i z) := by
  subst h
  simp [izoCastCycles]

theorem izo_homologyMap_homologyπ {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) z)
      = (L.homologyπ i) (HomologicalComplex.cyclesMap φ i z) :=
  congrArg (fun (f : K.cycles i ⟶ L.homology i) => f z)
    (HomologicalComplex.homologyπ_naturality φ i)

theorem izo_eqToIso_homologyπ {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    (eqToIso (congrArg (fun m => K.homology m) h)).hom ((K.homologyπ i) z)
      = (K.homologyπ j) (izoCastCycles K h z) := by
  subst h
  simp [izoCastCycles]

theorem izo_iCycles_cyclesMk {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

theorem izo_d_map_eq_zero {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (x : K.X i) (hx : K.d i j x = 0) : L.d i j ((φ.f i) x) = 0 := by
  have h := congrArg (fun (g : K.X i ⟶ L.X j) => g x) (HomologicalComplex.Hom.comm φ i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hx, map_zero] at h
  exact h

theorem izo_d_castElem {K : ChainComplex (ModuleCat ℤ) ℕ} {i i' j : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.d i' ((ComplexShape.down ℕ).next i') (castElem K h x) = 0 := by
  subst h
  rw [← hj] at hx
  simpa [castElem] using hx

theorem izo_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0)
    (hy : L.d i j ((φ.f i) x) = 0) :
    HomologicalComplex.cyclesMap φ i (K.cyclesMk x j hj hx) = L.cyclesMk ((φ.f i) x) j hj hy := by
  have hcm : L.iCycles i (HomologicalComplex.cyclesMap φ i (K.cyclesMk x j hj hx)) = (φ.f i) x := by
    have hh := congrArg (fun (g : K.cycles i ⟶ L.X i) => g (K.cyclesMk x j hj hx))
      (HomologicalComplex.cyclesMap_i (φ := φ) (i := i))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      izo_iCycles_cyclesMk hj x hx] at hh ⊢
    exact hh
  refine (Preadditive.mono_iff_injective (L.iCycles i)).1 inferInstance ?_
  exact hcm.trans (izo_iCycles_cyclesMk hj ((φ.f i) x) hy).symm

theorem izo_castCycles_cyclesMk {K : ChainComplex (ModuleCat ℤ) ℕ} {i i' j j' : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (hj' : (ComplexShape.down ℕ).next i' = j')
    (x : K.X i) (hx : K.d i j x = 0) (hx' : K.d i' j' (castElem K h x) = 0) :
    izoCastCycles K h (K.cyclesMk x j hj hx) = K.cyclesMk (castElem K h x) j' hj' hx' := by
  subst h
  have hjj : j = j' := hj.symm.trans hj'
  subst hjj
  refine (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance ?_
  change K.iCycles i (K.cyclesMk x j hj hx) = K.iCycles i (K.cyclesMk x j hj hx')
  rw [izo_iCycles_cyclesMk hj x hx']

/-- The abstract final step: if a chain map sends a transported cycle to a cycle, it sends the
homology class accordingly. -/
theorem izo_homology_apply {K Z : ChainComplex (ModuleCat ℤ) ℕ} (F : K ⟶ Z) {i j : ℕ} (h : i = j)
    (U : K.X i) (hx : K.d i ((ComplexShape.down ℕ).next i) U = 0)
    (z : Z.X j) (hz : Z.d j ((ComplexShape.down ℕ).next j) z = 0)
    (H : (F.f j) (castElem K h U) = z) :
    (HomologicalComplex.homologyMap F j)
        ((eqToIso (congrArg (fun m => K.homology m) h)).hom
          ((K.homologyπ i) (K.cyclesMk U ((ComplexShape.down ℕ).next i) rfl hx)))
      = (Z.homologyπ j) (Z.cyclesMk z ((ComplexShape.down ℕ).next j) rfl hz) := by
  rw [izo_eqToIso_homologyπ h (K.cyclesMk U ((ComplexShape.down ℕ).next i) rfl hx)]
  rw [izo_castCycles_cyclesMk h rfl rfl U hx (izo_d_castElem h rfl U hx)]
  rw [izo_homologyMap_homologyπ]
  rw [izo_cyclesMap_cyclesMk F rfl (castElem K h U) (izo_d_castElem h rfl U hx)
    (izo_d_map_eq_zero F (castElem K h U) (izo_d_castElem h rfl U hx))]
  refine congrArg (fun c => (Z.homologyπ j) c) ?_
  refine (Preadditive.mono_iff_injective (Z.iCycles j)).1 inferInstance ?_
  rw [HomologicalComplex.i_cyclesMk Z ((F.f j) (castElem K h U)) ((ComplexShape.down ℕ).next j) rfl
      (izo_d_map_eq_zero F (castElem K h U) (izo_d_castElem h rfl U hx)),
    HomologicalComplex.i_cyclesMk Z z ((ComplexShape.down ℕ).next j) rfl hz]
  exact H

/-! ## The transport of the fibre is the chain map `T.hom` -/

theorem izo_sCCFunctor_map_eqToHom {α : Type} (G : α → SSet.{0}) {a b : α} (h : a = b) :
    sCCFunctor.map (eqToHom (congrArg G h))
      = eqToHom (congrArg (fun x => sCCFunctor.obj (G x)) h) := by
  subst h
  simp

theorem izo_sCCMap_fibreTrans {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    sCCMap (Work.SSS.SZero.fibreTrans p b σ h)
      = (eqToIso (congrArg (fun x => fibreCC p x) h)).hom := by
  show sCCFunctor.map (eqToHom (congrArg (fun X => sSing (Work.StemsB.fibre p X)) h))
      = (eqToIso (congrArg (fun x => fibreCC p x) h)).hom
  rw [izo_sCCFunctor_map_eqToHom (fun X => sSing (Work.StemsB.fibre p X)) h,
    CategoryTheory.eqToIso.hom]

/-! ## The unfolding of `serreE1PieceIso` at `0` -/

theorem izo_serreE1PieceIso_zero_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) :
    serreE1PieceIso p hfib 0 q σ =
      eqToIso (congrArg (fun i => (pieceAlong (sSingP p) σ).homology i)
          (Nat.zero_add q)) ≪≫
        HomologicalComplex.homologyMapIso (pieceAlongZeroIso p σ) q := by
  rw [serreE1PieceIso.eq_1]
  exact @izo_eqMpr_iso (fun i => (pieceAlong (sSingP p) σ).homology i)
    ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.StemsB.fibre p (sigmaVert σ)))).homology q)
    (0 + q) q (Nat.zero_add q) (HomologicalComplex.homologyMapIso (pieceAlongZeroIso p σ) q)

/-! ## `iotaF` on a generator -/

theorem izo_iotaF_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ)
    (τ : sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    (iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 b σ h q)
        (((sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1)
      = (pieceπOf (sSingP p) σ).f (0 + q)
          (iotaTLift p hfib 0 b σ h q τ) := by
  have h1 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      (pieceAlong (sSingP p) σ).X (0 + q)) => g.hom (1 : ℤ))
    (iotaF_gen (p := p) (liftFam p hfib) (liftFam_proj p hfib) 0 b σ h q τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, eltHom_apply_one]
  rfl

theorem izo_cokerIso_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B) :
    pieceπOf (sSingP p) σ ≫ (pieceAlongZeroCokerIso p σ).hom = 𝟙 _ := by
  haveI : IsIso (cokernel.π (sCCMap (bdryAlong (sSingP p) σ).ι)) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (cokernel.π _) (cokernel.condition _))
      (cokernelIsCokernel _)
      (sCCMap_ι_eq_zero_of_eq_bot (bdryAlong_eq_bot_of_zero (sSingP p) σ))
  rw [show pieceAlongZeroCokerIso p σ
      = (asIso (cokernel.π (sCCMap (bdryAlong (sSingP p) σ).ι))).symm from rfl]
  rw [show pieceπOf (sSingP p) σ
      = (asIso (cokernel.π (sCCMap (bdryAlong (sSingP p) σ).ι))).hom from rfl]
  rw [← Iso.trans_hom, Iso.self_symm_id, Iso.refl_hom]

theorem izo_pieceAlongZeroIso_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ)
    (τ : sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    ((pieceAlongZeroIso p σ).hom.f (0 + q))
        ((iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 b σ h q)
          (((sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1))
      = (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0 + q)
          (iotaTLift p hfib 0 b σ h q τ) := by
  rw [izo_iotaF_apply p hfib b σ h q τ]
  have hfac : (pieceAlongZeroIso p σ).hom.f (0 + q)
      = (pieceAlongZeroCokerIso p σ).hom.f (0 + q) ≫
        (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0 + q) := by
    rw [pieceAlongZeroIso]
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, HomologicalComplex.comp_f,
      CategoryTheory.eqToIso.hom, CategoryTheory.eqToHom_refl, HomologicalComplex.id_f,
      Category.comp_id, sCCMap]
  have hmor : (pieceπOf (sSingP p) σ).f (0 + q) ≫
      (pieceAlongZeroCokerIso p σ).hom.f (0 + q) = 𝟙 _ := by
    have hh := congrArg (fun (g : sCC (pullAlong (sSingP p) σ) ⟶
        sCC (pullAlong (sSingP p) σ)) => g.f (0 + q)) (izo_cokerIso_comp p σ)
    simpa using hh
  have h2 : ((pieceAlongZeroCokerIso p σ).hom.f (0 + q))
      ((pieceπOf (sSingP p) σ).f (0 + q) (iotaTLift p hfib 0 b σ h q τ))
      = iotaTLift p hfib 0 b σ h q τ := by
    have hh := congrArg (fun (g : (sCC (pullAlong (sSingP p) σ)).X (0 + q) ⟶
        (sCC (pullAlong (sSingP p) σ)).X (0 + q)) =>
      g (iotaTLift p hfib 0 b σ h q τ)) hmor
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CategoryTheory.id_apply] using hh
  rw [hfac]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, CategoryTheory.id_apply]
  rw [h2]
  rfl

/-! ## `sCCMap` on a generator and its functoriality -/

theorem izo_sCCMap_apply_gen {X Y : SSet.{0}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (sCCMap f).f n ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)
      = (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (f.app (Opposite.op (SimplexCategory.mk n)) x)).hom 1 := by
  have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    g.hom (1 : ℤ)) (SSet.ι_chainComplexMap_f (f := f) (R := ModuleCat.of ℤ ℤ) (x := x))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

theorem izo_sCCMap_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sCCMap (f ≫ g) = sCCMap f ≫ sCCMap g := by
  simp only [sCCMap, CategoryTheory.Functor.map_comp]

theorem izo_sCCMap_id {X : SSet.{0}} : sCCMap (𝟙 X) = 𝟙 (sCC X) := by
  simp only [sCCMap, CategoryTheory.Functor.map_id]

theorem izo_sCCMap_apply_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (x : (sCC X).X n) :
    (sCCMap g).f n ((sCCMap f).f n x) = (sCCMap (f ≫ g)).f n x := by
  rw [izo_sCCMap_comp f g]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]

/-! ## The `(0,q)`-shuffle is the degree identification -/

theorem izo_pB_zSh (q : ℕ) (i : Fin (0 + q + 1)) :
    Work.Cohomology.Crux33.pB (Work.KunnethEZ.zSh q).1 i = i.val := by
  rw [Work.KunnethEZ.zSh]
  rw [Work.Cohomology.Crux33.pB]
  have hcard : (Finset.univ.filter (fun j : Fin (0 + q) => j.val < i.val)).card
      = Fintype.card {j : Fin (0 + q) // j.val < i.val} := by
    rw [Fintype.card_subtype]
  rw [hcard]
  have he : {j : Fin (0 + q) // j.val < i.val} ≃ Fin i.val :=
    { toFun := fun j => ⟨j.1.val, j.2⟩
      invFun := fun k => ⟨⟨k.1, by have := k.2; have := i.2; omega⟩, k.2⟩
      left_inv := fun j => by simp
      right_inv := fun k => by simp }
  rw [Fintype.card_congr he, Fintype.card_fin]

theorem izo_eqToHom_mk_val {m n : ℕ} (h : m = n) (i : Fin (m + 1)) :
    (((eqToHom (congrArg SimplexCategory.mk h)) : (⦋m⦌ ⟶ ⦋n⦌)) i).val = i.val := by
  subst h
  simp

theorem izo_bHom_zSh_eqToHom (q : ℕ) :
    Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1 (Work.KunnethEZ.zSh q).2 =
      eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  refine Fin.ext ?_
  show ((ConcreteCategory.hom (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
      (Work.KunnethEZ.zSh q).2)) i).val
    = (((eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q)) : (⦋0+q⦌ ⟶ ⦋q⦌)) i)).val
  rw [Work.Cohomology.Crux33.bHom_val (Work.KunnethEZ.zSh q).1 (Work.KunnethEZ.zSh q).2 i]
  rw [izo_pB_zSh q i]
  rw [izo_eqToHom_mk_val (Nat.zero_add q) i]

theorem izo_eqToHom_comp_bHom (q : ℕ) :
    eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q).symm) ≫
      Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1 (Work.KunnethEZ.zSh q).2
      = 𝟙 ⦋q⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  refine Fin.ext ?_
  show ((ConcreteCategory.hom (((eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q).symm)) :
      (⦋q⦌ ⟶ ⦋0+q⦌)) ≫
      Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1 (Work.KunnethEZ.zSh q).2)) i).val
    = (((𝟙 ⦋q⦌ : ⦋q⦌ ⟶ ⦋q⦌) i)).val
  rw [Work.KunnethEZ.comp_val]
  rw [Work.Cohomology.Crux33.bHom_val (Work.KunnethEZ.zSh q).1 (Work.KunnethEZ.zSh q).2]
  rw [izo_pB_zSh q]
  rw [izo_eqToHom_mk_val (Nat.zero_add q).symm i]
  rfl

theorem izo_castSimp_eq_map {Y : SSet.{0}} {m n : ℕ} (h : m = n) (x : Y _⦋m⦌) :
    Work.SSS.SZero.castSimp h x
      = Y.map (Quiver.Hom.op (eqToHom (congrArg SimplexCategory.mk h.symm))) x := by
  subst h
  simp [Work.SSS.SZero.castSimp]

theorem izo_castSimp_zSh_bHom {Y : SSet.{0}} (q : ℕ) (τ : Y _⦋q⦌) :
    Work.SSS.SZero.castSimp (Nat.zero_add q)
      (Y.map (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
        (Work.KunnethEZ.zSh q).2)) τ) = τ := by
  rw [izo_castSimp_eq_map]
  rw [← Work.KunnethEZ.map_op_comp]
  rw [izo_eqToHom_comp_bHom q]
  simp

theorem izo_castElem_ιChainComplex {X : SSet.{0}} {m n : ℕ} (h : m = n) (y : X _⦋m⦌) :
    castElem (X.chainComplex (ModuleCat.of ℤ ℤ)) h
        ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) y).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) (Work.SSS.SZero.castSimp h y)).hom 1 := by
  subst h
  simp [castElem, Work.SSS.SZero.castSimp]

/-! ## The Eilenberg–Zilber chain of the vertex `(v₀, τ)` -/

theorem izo_subsingleton_stdSimplex_zero (n : ℕ) :
    Subsingleton ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).obj
      (Opposite.op (SimplexCategory.mk n))) :=
  ⟨fun a b => (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 0)
      (m := Opposite.op (SimplexCategory.mk n))).injective (Work.KunnethEZ.hom_zero_unique _ _)⟩

theorem izo_ssetVertex_zero_eq_yoneda :
    ssetVertex 0 = SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) :=
  (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 0)
      (m := Opposite.op (SimplexCategory.mk 0))).injective (Work.KunnethEZ.hom_zero_unique _ _)

theorem izo_vertIncl_snd_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (n : ℕ) (w : (sSing (Work.StemsB.fibre p b)) _⦋n⦌) :
    ((vertIncl p b 0).app (Opposite.op (SimplexCategory.mk n)) w).2 = w := by
  change ((SemiCartesianMonoidalCategory.snd (SSet.stdSimplex.obj (SimplexCategory.mk 0))
      (sSing (Work.StemsB.fibre p b))).app (Opposite.op (SimplexCategory.mk n)))
      ((vertIncl p b 0).app (Opposite.op (SimplexCategory.mk n)) w) = w
  have h := congrArg (fun (g : sSing (Work.StemsB.fibre p b) ⟶
      sSing (Work.StemsB.fibre p b)) =>
      (g.app (Opposite.op (SimplexCategory.mk n))) w) (vertIncl_snd p b 0)
  simp only [CategoryTheory.NatTrans.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.id_apply, CategoryTheory.NatTrans.id_app] at h
  exact h

theorem izo_ezGen_zero_eq_vertIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (q : ℕ)
    (τ : sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    Work.Cohomology.Crux33.ezGen 0 q
        (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (sSing (Work.StemsB.fibre p b)) (stdIdSimplex 0) τ
      = (sCCMap (vertIncl p b 0)).f (0 + q)
          (((sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((sSing (Work.StemsB.fibre p b)).map
              (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
                (Work.KunnethEZ.zSh q).2)) τ)).hom 1) := by
  rw [Work.KunnethEZ.ezGen_zero_single, Work.KunnethEZ.genP]
  rw [izo_sCCMap_apply_gen]
  refine congrArg (fun t => (((SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⊗
      sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) t).hom 1) ?_
  refine Prod.ext ?_ ?_
  · haveI := izo_subsingleton_stdSimplex_zero (0 + q)
    exact Subsingleton.elim _ _
  · exact (izo_vertIncl_snd_apply p b (0 + q) _).symm

/-! ## The Eilenberg–Zilber lift at a vertex is `phiAlong` -/

theorem izo_ezSimplex_vert_eq_phiAlong {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B) :
    vertIncl p (sigmaVert σ) 0 ≫
        ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl
      = phiAlong p σ := by
  apply pullback.hom_ext
  · calc (vertIncl p (sigmaVert σ) 0 ≫
          ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)
          ≫ pullback.fst σ (sSingP p)
        = vertIncl p (sigmaVert σ) 0 ≫
            (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl
              ≫ pullback.fst σ (sSingP p)) := Category.assoc _ _ _
      _ = vertIncl p (sigmaVert σ) 0 ≫ SemiCartesianMonoidalCategory.fst _ _ := by
            rw [ezSimplex_fst]
      _ = SSet.const (ssetVertex 0) := vertIncl_fst _ _ _
      _ = phiAlongFst p σ := by rw [izo_ssetVertex_zero_eq_yoneda]; rfl
      _ = phiAlong p σ ≫ pullback.fst σ (sSingP p) := (phiAlong_fst p σ).symm
  · calc (vertIncl p (sigmaVert σ) 0 ≫
          ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)
          ≫ pullback.snd σ (sSingP p)
        = vertIncl p (sigmaVert σ) 0 ≫
            (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl
              ≫ pullback.snd σ (sSingP p)) := Category.assoc _ _ _
      _ = vertIncl p (sigmaVert σ) 0 ≫ liftFam p hfib 0 (sigmaVert σ) σ rfl := by
            rw [ezSimplex_snd]
      _ = sSingP (Work.StemsB.fibreIncl p (sigmaVert σ)) :=
            liftFam_vert p hfib 0 (sigmaVert σ) σ rfl
      _ = phiAlong p σ ≫ pullback.snd σ (sSingP p) := (phiAlong_snd p σ).symm

/-! ## The key elementwise computation at `P = 0`, fibre `F_{σ(v₀)}` -/

/-- The definitional unfolding of `iotaTLift` at `P = 0`. -/
theorem izo_iotaTLift_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) (τ : sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    iotaTLift p hfib 0 b σ h q τ
      = (sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 b σ h)).f (0+q)
          (Work.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
            (sSing (Work.StemsB.fibre p b)) (stdIdSimplex 0) τ) := rfl

/-- **The vertex composite at degree `0 + q`.** -/
theorem izo_apply_gen_deg {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (q : ℕ) (τ : sSing (Work.StemsB.fibre p (sigmaVert σ)) _⦋q⦌) :
    ((pieceAlongZeroIso p σ).hom.f (0+q))
        ((iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl q)
          (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1))
      = (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((sSing (Work.StemsB.fibre p (sigmaVert σ))).map
            (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
              (Work.KunnethEZ.zSh q).2)) τ)).hom 1) := by
  set g0 : (sCC (sSing (Work.StemsB.fibre p (sigmaVert σ)))).X (0+q) :=
    (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      ((sSing (Work.StemsB.fibre p (sigmaVert σ))).map
        (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
          (Work.KunnethEZ.zSh q).2)) τ)).hom 1) with hg0
  set gg : (sCC (sSing (Work.StemsB.fibre p (sigmaVert σ)))).X q :=
    (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) τ).hom 1) with hgg
  have h1 : ((pieceAlongZeroIso p σ).hom.f (0+q))
        ((iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl q) gg)
      = (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
          (iotaTLift p hfib 0 (sigmaVert σ) σ rfl q τ) :=
    izo_pieceAlongZeroIso_apply p hfib (sigmaVert σ) σ rfl q τ
  have h2 : (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
        (iotaTLift p hfib 0 (sigmaVert σ) σ rfl q τ)
      = (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
          ((sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q)
            (Work.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
              (sSing (Work.StemsB.fibre p (sigmaVert σ))) (stdIdSimplex 0) τ)) :=
    congrArg (fun y => (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q) y)
      (izo_iotaTLift_eq p hfib (sigmaVert σ) σ rfl q τ)
  have h3 : (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
        ((sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q)
          (Work.Cohomology.Crux33.ezGen 0 q (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
            (sSing (Work.StemsB.fibre p (sigmaVert σ))) (stdIdSimplex 0) τ))
      = (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
          ((sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q)
            ((sCCMap (vertIncl p (sigmaVert σ) 0)).f (0+q) g0)) :=
    congrArg (fun y => (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
        ((sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q) y))
      (izo_ezGen_zero_eq_vertIncl p (sigmaVert σ) q τ)
  have h4 : (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
          ((sCCMap (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q)
            ((sCCMap (vertIncl p (sigmaVert σ) 0)).f (0+q) g0))
      = (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
          ((sCCMap (vertIncl p (sigmaVert σ) 0 ≫
            ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q) g0) :=
    congrArg (fun y => (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q) y)
      (izo_sCCMap_apply_comp (vertIncl p (sigmaVert σ) 0)
        (ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl) (0+q) g0)
  have h5 : (sCCMap ((pullAlongVertexIsoIso p σ).hom)).f (0+q)
          ((sCCMap (vertIncl p (sigmaVert σ) 0 ≫
            ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)).f (0+q) g0)
      = (sCCMap ((vertIncl p (sigmaVert σ) 0 ≫
            ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl) ≫
          (pullAlongVertexIsoIso p σ).hom)).f (0+q) g0 :=
    izo_sCCMap_apply_comp
      (vertIncl p (sigmaVert σ) 0 ≫
        ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl)
      ((pullAlongVertexIsoIso p σ).hom) (0+q) g0
  have h6 : (sCCMap ((vertIncl p (sigmaVert σ) 0 ≫
            ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl) ≫
          (pullAlongVertexIsoIso p σ).hom)).f (0+q) g0
      = (sCCMap (𝟙 (sSing (Work.StemsB.fibre p (sigmaVert σ))))).f (0+q) g0 :=
    congrArg (fun g => (sCCMap g).f (0+q) g0)
      (show (vertIncl p (sigmaVert σ) 0 ≫
            ezSimplex p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl) ≫
            (pullAlongVertexIsoIso p σ).hom
          = 𝟙 (sSing (Work.StemsB.fibre p (sigmaVert σ))) from by
        haveI : IsIso (phiAlong p σ) := Work.SSS.phiAlong_isIso p σ
        rw [show (pullAlongVertexIsoIso p σ).hom = CategoryTheory.inv (phiAlong p σ) from rfl,
          izo_ezSimplex_vert_eq_phiAlong p hfib σ,
          CategoryTheory.IsIso.hom_inv_id])
  have h7 : (sCCMap (𝟙 (sSing (Work.StemsB.fibre p (sigmaVert σ))))).f (0+q) g0 = g0 := by
    rw [izo_sCCMap_id]
    simp
  rw [h1, h2, h3, h4, h5, h6, h7]


/-- **The vertex composite sends `ι_σ τ` to `τ`.** -/
theorem izo_apply_gen {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (q : ℕ) (τ : sSing (Work.StemsB.fibre p (sigmaVert σ)) _⦋q⦌) :
    ((pieceAlongZeroIso p σ).hom.f q)
        (castElem (pieceAlong (sSingP p) σ) (Nat.zero_add q)
          ((iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl q)
            (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) τ).hom 1)))
      = (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) := by
  have h3 : castElem (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (sigmaVert σ)))) (Nat.zero_add q)
      (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((sSing (Work.StemsB.fibre p (sigmaVert σ))).map
          (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
            (Work.KunnethEZ.zSh q).2)) τ)).hom 1)
      = (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) :=
    (izo_castElem_ιChainComplex (Nat.zero_add q)
        ((sSing (Work.StemsB.fibre p (sigmaVert σ))).map
          (Quiver.Hom.op (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh q).1
            (Work.KunnethEZ.zSh q).2)) τ)).trans
      (congrArg (fun y => (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) y).hom 1))
        (izo_castSimp_zSh_bHom (Y := sSing (Work.StemsB.fibre p (sigmaVert σ))) q τ))
  rw [← izo_castElem_map (pieceAlongZeroIso p σ).hom (Nat.zero_add q)
    ((iotaF p (liftFam p hfib) (liftFam_proj p hfib) 0 (sigmaVert σ) σ rfl q)
      (((sSing (Work.StemsB.fibre p (sigmaVert σ))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1))]
  rw [izo_apply_gen_deg p hfib σ q τ]
  exact h3

/-! ## The statement -/

theorem iotaStatement_zero_c_one {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (q : ℕ) (τ : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (Opposite.op (SimplexCategory.mk q)))
    (hτ : (Work.SSS.fibreCC p b).d q ((ComplexShape.down ℕ).next q)
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0)
    (hcyc : (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (0+q)
        ((ComplexShape.down ℕ).next (0+q))
        ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h q)
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0) :
    (HomologicalComplex.homologyMap
        (CategoryTheory.eqToIso (congrArg (Work.SSS.fibreCC p) h)).hom q)
      ((Work.SSS.serreE1PieceIso p hfib 0 q σ).hom
        (HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ) (0+q)
          (HomologicalComplex.cyclesMk (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ)
            ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0 b σ h q)
              (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) τ).hom 1))
            ((ComplexShape.down ℕ).next (0+q)) rfl hcyc)))
    = (1 : ℤ) • HomologicalComplex.homologyπ (Work.SSS.fibreCC p b) q
        (HomologicalComplex.cyclesMk (Work.SSS.fibreCC p b)
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)
          ((ComplexShape.down ℕ).next q) rfl hτ) := by
  rw [← izo_sCCMap_fibreTrans p b σ h]
  subst h
  have hE : sCCMap (Work.SSS.SZero.fibreTrans p (Work.SSS.sigmaVert σ) σ rfl)
      = 𝟙 (Work.SSS.fibreCC p (Work.SSS.sigmaVert σ)) := by
    rw [Work.SSS.SZero.fibreTrans]
    simp only [CategoryTheory.eqToHom_refl, Work.SSS.sCCMap, CategoryTheory.Functor.map_id]
  rw [hE]
  simp only [HomologicalComplex.homologyMap_id, CategoryTheory.id_apply]
  rw [one_smul]
  rw [izo_serreE1PieceIso_zero_eq p hfib (Work.SSS.sigmaVert σ) σ rfl q]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.comp_apply]
  exact izo_homology_apply (Work.SSS.pieceAlongZeroIso p σ).hom (Nat.zero_add q)
    ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) 0
        (Work.SSS.sigmaVert σ) σ rfl q)
      (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1))
    hcyc
    (((Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) τ).hom 1)
    hτ
    (izo_apply_gen p hfib σ q τ)

end

end Work.SSS
