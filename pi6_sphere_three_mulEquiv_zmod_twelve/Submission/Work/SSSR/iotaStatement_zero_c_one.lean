import Mathlib
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.SZero.Defs
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.KunnethEZ.EZGenX
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-! ## Elementary transports of chain complexes along degree equalities -/

theorem izo_eqMpr_iso {A : ℕ → ModuleCat R} {B : ModuleCat R} {m n : ℕ} (h : m = n)
    (e : A n ≅ B) : Eq.mpr (congrArg (fun i => A i ≅ B) h) e = eqToIso (congrArg A h) ≪≫ e := by
  subst h
  simp

theorem izo_castElem_map {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (x : K.X i) : castElem L h ((φ.f i) x) = (φ.f j) (castElem K h x) := by
  subst h
  simp [castElem]

/-- Transport of an element of the cycles of a chain complex along an equality of degrees. -/
def izoCastCycles (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j) (x : K.cycles i) :
    K.cycles j :=
  (eqToHom (congrArg (fun m => K.cycles m) h)).hom x

theorem izo_homologyMap_homologyπ {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) z)
      = (L.homologyπ i) (HomologicalComplex.cyclesMap φ i z) :=
  congrArg (fun (f : K.cycles i ⟶ L.homology i) => f z)
    (HomologicalComplex.homologyπ_naturality φ i)

theorem izo_eqToIso_homologyπ {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    (z : K.cycles i) :
    (eqToIso (congrArg (fun m => K.homology m) h)).hom ((K.homologyπ i) z)
      = (K.homologyπ j) (izoCastCycles K h z) := by
  subst h
  simp [izoCastCycles]

theorem izo_iCycles_cyclesMk {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

theorem izo_d_map_eq_zero {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (x : K.X i) (hx : K.d i j x = 0) : L.d i j ((φ.f i) x) = 0 := by
  have h := congrArg (fun (g : K.X i ⟶ L.X j) => g x) (HomologicalComplex.Hom.comm φ i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hx, map_zero] at h
  exact h

theorem izo_d_castElem {K : ChainComplex (ModuleCat R) ℕ} {i i' j : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.d i' ((ComplexShape.down ℕ).next i') (castElem K h x) = 0 := by
  subst h
  rw [← hj] at hx
  simpa [castElem] using hx

theorem izo_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ}
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

theorem izo_castCycles_cyclesMk {K : ChainComplex (ModuleCat R) ℕ} {i i' j j' : ℕ} (h : i = i')
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
theorem izo_homology_apply {K Z : ChainComplex (ModuleCat R) ℕ} (F : K ⟶ Z) {i j : ℕ} (h : i = j)
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

/-! ## The unfolding of `serreE1PieceIso` at `0` -/

theorem izo_serreE1PieceIso_zero_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) :
    serreE1PieceIso p hfib 0 q σ =
      eqToIso (congrArg (fun i => (pieceAlong R (sSingP p) σ).homology i)
          (Nat.zero_add q)) ≪≫
        HomologicalComplex.homologyMapIso (pieceAlongZeroIso p σ) q := by
  rw [serreE1PieceIso.eq_1]
  exact izo_eqMpr_iso (A := fun i => (pieceAlong R (sSingP p) σ).homology i)
    (B := (Work.SSSR.Cohomology.singularChains R
      (TopCat.of (Work.SSSR.StemsB.fibre p (sigmaVert σ)))).homology q)
    (m := 0 + q) (n := q) (Nat.zero_add q)
    (HomologicalComplex.homologyMapIso (pieceAlongZeroIso p σ) q)

theorem izo_cokerIso_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ sSing B) :
    pieceπOf (R := R) (sSingP p) σ ≫ (pieceAlongZeroCokerIso p σ).hom = 𝟙 _ := by
  haveI : IsIso (cokernel.π (sCCMap R (bdryAlong (sSingP p) σ).ι)) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (cokernel.π _) (cokernel.condition _))
      (cokernelIsCokernel _)
      (sCCMap_ι_eq_zero_of_eq_bot (bdryAlong_eq_bot_of_zero (sSingP p) σ))
  rw [show pieceAlongZeroCokerIso p σ
      = (asIso (cokernel.π (sCCMap R (bdryAlong (sSingP p) σ).ι))).symm from rfl]
  rw [show pieceπOf (sSingP p) σ
      = (asIso (cokernel.π (sCCMap R (bdryAlong (sSingP p) σ).ι))).hom from rfl]
  rw [← Iso.trans_hom, Iso.self_symm_id, Iso.refl_hom]

/-! ## `sCCMap R` on a generator and its functoriality -/

theorem izo_sCCMap_apply_gen {X Y : SSet.{0}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (sCCMap R f).f n ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1)
      = (Y.ιChainComplex (R := ModuleCat.of R R)
          (f.app (Opposite.op (SimplexCategory.mk n)) x)).hom 1 := by
  have h := congrArg (fun (g : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X n) =>
    g.hom (1 : R)) (SSet.ι_chainComplexMap_f (f := f) (R := ModuleCat.of R R) (x := x))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

theorem izo_sCCMap_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sCCMap R (f ≫ g) = sCCMap R f ≫ sCCMap R g := by
  simp only [sCCMap, CategoryTheory.Functor.map_comp]

/-! ## The `(0,q)`-shuffle is the degree identification -/

theorem izo_pB_zSh (q : ℕ) (i : Fin (0 + q + 1)) :
    Work.SSSR.Cohomology.Crux33.pB (Work.SSSR.KunnethEZ.zSh q).1 i = i.val := by
  rw [Work.SSSR.KunnethEZ.zSh]
  rw [Work.SSSR.Cohomology.Crux33.pB]
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

theorem izo_eqToHom_comp_bHom (q : ℕ) :
    eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q).symm) ≫
      Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1 (Work.SSSR.KunnethEZ.zSh q).2
      = 𝟙 ⦋q⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  refine Fin.ext ?_
  show ((ConcreteCategory.hom (((eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q).symm)) :
      (⦋q⦌ ⟶ ⦋0+q⦌)) ≫
      Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1 (Work.SSSR.KunnethEZ.zSh q).2)) i).val
    = (((𝟙 ⦋q⦌ : ⦋q⦌ ⟶ ⦋q⦌) i)).val
  rw [Work.SSSR.KunnethEZ.comp_val]
  rw [Work.SSSR.Cohomology.Crux33.bHom_val (Work.SSSR.KunnethEZ.zSh q).1 (Work.SSSR.KunnethEZ.zSh q).2]
  rw [izo_pB_zSh q]
  rw [izo_eqToHom_mk_val (Nat.zero_add q).symm i]
  rfl

theorem izo_castSimp_eq_map {Y : SSet.{0}} {m n : ℕ} (h : m = n) (x : Y _⦋m⦌) :
    Work.SSSR.SZero.castSimp h x
      = Y.map (Quiver.Hom.op (eqToHom (congrArg SimplexCategory.mk h.symm))) x := by
  subst h
  simp [Work.SSSR.SZero.castSimp]

theorem izo_castSimp_zSh_bHom {Y : SSet.{0}} (q : ℕ) (τ : Y _⦋q⦌) :
    Work.SSSR.SZero.castSimp (Nat.zero_add q)
      (Y.map (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
        (Work.SSSR.KunnethEZ.zSh q).2)) τ) = τ := by
  rw [izo_castSimp_eq_map]
  rw [← Work.SSSR.KunnethEZ.map_op_comp]
  rw [izo_eqToHom_comp_bHom q]
  simp

theorem izo_castElem_ιChainComplex {X : SSet.{0}} {m n : ℕ} (h : m = n) (y : X _⦋m⦌) :
    castElem (X.chainComplex (ModuleCat.of R R)) h
        ((X.ιChainComplex (R := ModuleCat.of R R) y).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of R R) (Work.SSSR.SZero.castSimp h y)).hom 1 := by
  subst h
  simp [castElem, Work.SSSR.SZero.castSimp]

/-! ## The Eilenberg–Zilber chain of the vertex `(v₀, τ)` -/

theorem izo_subsingleton_stdSimplex_zero (n : ℕ) :
    Subsingleton ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).obj
      (Opposite.op (SimplexCategory.mk n))) :=
  ⟨fun a b => (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 0)
      (m := Opposite.op (SimplexCategory.mk n))).injective (Work.SSSR.KunnethEZ.hom_zero_unique _ _)⟩

theorem izo_ssetVertex_zero_eq_yoneda :
    ssetVertex 0 = SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) :=
  (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk 0)
      (m := Opposite.op (SimplexCategory.mk 0))).injective (Work.SSSR.KunnethEZ.hom_zero_unique _ _)

theorem izo_vertIncl_snd_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (n : ℕ) (w : (sSing (Work.SSSR.StemsB.fibre p b)) _⦋n⦌) :
    ((vertIncl p b 0).app (Opposite.op (SimplexCategory.mk n)) w).2 = w := by
  change ((SemiCartesianMonoidalCategory.snd (SSet.stdSimplex.obj (SimplexCategory.mk 0))
      (sSing (Work.SSSR.StemsB.fibre p b))).app (Opposite.op (SimplexCategory.mk n)))
      ((vertIncl p b 0).app (Opposite.op (SimplexCategory.mk n)) w) = w
  have h := congrArg (fun (g : sSing (Work.SSSR.StemsB.fibre p b) ⟶
      sSing (Work.SSSR.StemsB.fibre p b)) =>
      (g.app (Opposite.op (SimplexCategory.mk n))) w) (vertIncl_snd p b 0)
  simp only [CategoryTheory.NatTrans.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.id_apply, CategoryTheory.NatTrans.id_app] at h
  exact h

theorem izo_ezGen_zero_eq_vertIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (q : ℕ)
    (τ : sSing (Work.SSSR.StemsB.fibre p b) _⦋q⦌) :
    Work.SSSR.Cohomology.Crux33.ezGen 0 q
        (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex 0) τ
      = (sCCMap R (vertIncl p b 0)).f (0 + q)
          (((sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R)
            ((sSing (Work.SSSR.StemsB.fibre p b)).map
              (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
                (Work.SSSR.KunnethEZ.zSh q).2)) τ)).hom 1) := by
  rw [Work.SSSR.KunnethEZ.ezGen_zero_single, Work.SSSR.KunnethEZ.genP]
  rw [izo_sCCMap_apply_gen]
  refine congrArg (fun t => (((SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⊗
      sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R) t).hom 1) ?_
  refine Prod.ext ?_ ?_
  · haveI := izo_subsingleton_stdSimplex_zero (0 + q)
    exact Subsingleton.elim _ _
  · exact (izo_vertIncl_snd_apply p b (0 + q) _).symm

end

end Work.SSSR
