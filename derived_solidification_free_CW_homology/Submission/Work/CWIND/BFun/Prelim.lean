import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.BFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

open scoped Simplicial

/-!
# CWIND/T1: auxiliary lemmas for the comparison map `b : C_sing(X) ⟶ A(X)`

Auxiliary lemmas used in `Submission/Work/CWIND/BFun/exists_bNat.lean`: the compatibility of the
canonical points `thePoint` and generators `theGen` with the simplicial structure maps, and
elementary lemmas about sums of morphisms in `ModuleCat ℤ`.
-/

/-! ## Elementary lemmas about points of the compact-open mapping space -/

/-- The canonical point of `X^{Δⁿ}` attached to a singular simplex, as a section of the light
condensed set `X^{Δⁿ}` at the point `PUnit`. -/
noncomputable def thePointSec (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    (topCatToLightCondSet.obj (Work.CWIND.singSpace X n)).obj.obj (Opposite.op (↧PUnit)) :=
  ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥(Work.CWIND.singSpace X n))
    (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) x)

lemma thePoint_eq_sec (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    Work.CWIND.thePoint X n x = thePointSec X n x := rfl

/-- The compatibility of the canonical point with the cosimplicial structure of the simplex: the
simplicial structure map of `n ↦ X^{Δⁿ}` sends the point corresponding to `x` to the point
corresponding to the simplex map applied to `x`. -/
lemma toSSetObjEquiv_simp (X : TopCat.{0}) {a b : SimplexCategory} (φ : a ⟶ b)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op b)) :
    TopCat.toSSetObjEquiv X (Opposite.op a) ((TopCat.toSSet.obj X).map φ.op x)
      = (TopCat.toSSetObjEquiv X (Opposite.op b) x).comp (SimplexCategory.toTop₀.map φ).hom := by
  ext z
  simp only [ContinuousMap.comp_apply, SimplexCategory.toTop₀_map, ConcreteCategory.hom_ofHom,
    ContinuousMap.coe_mk]
  rw [TopCat.toSSetObjEquiv_naturality_apply]

/-- Postcomposition with a continuous map commutes with the constant maps out of a subsingleton. -/
lemma const'_comp {P : Type*} [TopologicalSpace P] [Subsingleton P] {Z Y : TopCat}
    (f : Z ⟶ Y) (z : Z) :
    f.hom.comp (ContinuousMap.const' (X := P) z) = ContinuousMap.const' (X := P) (f.hom z) := by
  ext p
  simp

/-- The compatibility of the canonical point with the simplicial structure maps. -/
lemma thePointSec_naturality (X : TopCat.{0}) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    (topCatToLightCondSet.map (Work.CWIND.singSpaceMap X φ)).hom.app (Opposite.op (↧PUnit))
        (thePointSec X n x)
      = thePointSec X m ((TopCat.toSSet.obj X).map φ.op x) := by
  show (Work.CWIND.singSpaceMap X φ).hom.comp
      (ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥(Work.CWIND.singSpace X n))
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)) x))
    = ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥(Work.CWIND.singSpace X m))
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌)) ((TopCat.toSSet.obj X).map φ.op x))
  rw [const'_comp]
  rw [show (Work.CWIND.singSpaceMap X φ).hom ((TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)) x)
      = (TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌)) ((TopCat.toSSet.obj X).map φ.op x) from
    (toSSetObjEquiv_simp X φ x).symm]

lemma thePoint_simp (X : TopCat.{0}) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    LightCondSet.underlying.map (topCatToLightCondSet.map (Work.CWIND.singSpaceMap X φ))
        (Work.CWIND.thePoint X n x) = Work.CWIND.thePoint X m ((TopCat.toSSet.obj X).map φ.op x) := by
  rw [thePoint_eq_sec (X := X) (n := n) (x := x),
    thePoint_eq_sec (X := X) (n := m) (x := (TopCat.toSSet.obj X).map φ.op x)]
  show (topCatToLightCondSet.map (Work.CWIND.singSpaceMap X φ)).hom.app (Opposite.op (↧PUnit))
        (thePointSec X n x) = thePointSec X m ((TopCat.toSSet.obj X).map φ.op x)
  exact thePointSec_naturality X φ x

/-- The compatibility of the canonical point with postcomposition of maps of spaces. -/
lemma thePointSec_naturality_space (X Y : TopCat.{0}) (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    (topCatToLightCondSet.map (Work.CWIND.singSpacePostcomp f n)).hom.app (Opposite.op (↧PUnit))
        (thePointSec X n x)
      = thePointSec Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x) := by
  show (Work.CWIND.singSpacePostcomp f n).hom.comp
      (ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥(Work.CWIND.singSpace X n))
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)) x))
    = ContinuousMap.const' (X := ↥(LightProfinite.of PUnit.{1})) (Y := ↥(Work.CWIND.singSpace Y n))
        ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋n⦌)) ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x))
  rw [const'_comp]
  rw [show (Work.CWIND.singSpacePostcomp f n).hom ((TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)) x)
      = (TopCat.toSSetObjEquiv Y (Opposite.op ⦋n⦌)) ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x)
      from rfl]

lemma thePoint_simp_space (X Y : TopCat.{0}) (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    LightCondSet.underlying.map (topCatToLightCondSet.map (Work.CWIND.singSpacePostcomp f n))
        (Work.CWIND.thePoint X n x) = Work.CWIND.thePoint Y n
          ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x) := by
  rw [thePoint_eq_sec (X := X) (n := n) (x := x),
    thePoint_eq_sec (X := Y) (n := n) (x := (TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x)]
  show (topCatToLightCondSet.map (Work.CWIND.singSpacePostcomp f n)).hom.app (Opposite.op (↧PUnit))
        (thePointSec X n x) = thePointSec Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x)
  exact thePointSec_naturality_space X Y f n x

/-! ## Elementary lemmas about sums in `ModuleCat ℤ` -/

/-- The underlying object functor (evaluation at `PUnit`) is additive. -/
instance instAdditiveUnderlying : (LightCondensed.underlying (ModuleCat ℤ)).Additive where
  map_add := by
    intro X Y f g
    rw [LightCondensed.underlying_map, LightCondensed.underlying_map, LightCondensed.underlying_map]
    rfl

lemma ModuleCat.hom_sum {M N : ModuleCat ℤ} {ι : Type*} (s : Finset ι) (F : ι → (M ⟶ N)) :
    (∑ i ∈ s, F i).hom = ∑ i ∈ s, (F i).hom := by
  classical
  refine Finset.induction (motive := fun s => (∑ i ∈ s, F i).hom = ∑ i ∈ s, (F i).hom) ?_ ?_ s
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change (F a).hom + (∑ x ∈ s, F x).hom = (F a).hom + ∑ x ∈ s, (F x).hom
    rw [ih]

lemma ModuleCat.hom_sum_apply {M N : ModuleCat ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → (M ⟶ N)) (z : M) :
    (∑ i ∈ s, F i).hom z = ∑ i ∈ s, (F i).hom z := by
  rw [ModuleCat.hom_sum]
  exact LinearMap.sum_apply s (fun i => (F i).hom) z

/-- The "generator" `1 ↦ z` map, seen as a morphism in `ModuleCat ℤ`. -/
lemma ofHom_toSpanSingleton_comp {M N : ModuleCat ℤ} (z : M) (f : M ⟶ N) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M z) ≫ f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ N (f z)) := by
  conv_lhs => rw [← ModuleCat.ofHom_hom f]
  rw [← ModuleCat.ofHom_comp]
  congr 1
  ext x
  simp [LinearMap.toSpanSingleton_apply]

/-! ## The transpose of `bLevel` -/

/-- The transpose of the levelwise comparison map `bLevel X n` under the adjunction
`discrete ⊣ underlying`: the module map sending the generator at a singular simplex `x` to the
element `theGen X n x` of `ℤ[X^{Δⁿ}]`. -/
noncomputable def genMap (X : TopCat.{0}) (n : ℕ) :
    (∐ (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌) => ModuleCat.of ℤ ℤ)) ⟶
      (LightCondensed.underlying (ModuleCat ℤ)).obj (freeLightCondAbOfTop (Work.CWIND.singSpace X n)) :=
  Sigma.desc (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (Work.CWIND.theGen X n x)))

lemma homEquiv_bLevel (X : TopCat.{0}) (n : ℕ) :
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _ (Work.CWIND.bLevel X n) =
      genMap X n := by
  rw [Work.CWIND.bLevel]
  exact Equiv.apply_symm_apply _ _

/-- The value of `genMap` on the generator at a simplex. -/
lemma genMap_ι (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌) => ModuleCat.of ℤ ℤ) x ≫
        genMap X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (Work.CWIND.theGen X n x)) :=
  Sigma.ι_comp_desc _ x

/-- The transpose of a composite `bLevel X n ≫ g`. -/
lemma homEquiv_bLevel_comp_right (X : TopCat.{0}) (n : ℕ) {W : LightCondAb}
    (g : (Work.CWIND.Achain X).X n ⟶ W) :
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ W
        (Work.CWIND.bLevel X n ≫ g)
      = genMap X n ≫ (LightCondensed.underlying (ModuleCat ℤ)).map g := by
  set_option backward.isDefEq.respectTransparency false in
  rw [Adjunction.homEquiv_naturality_right, homEquiv_bLevel]

/-- The transpose of the composite with the differential of the singular chain complex. -/
lemma homEquiv_Csrc_d_comp (X : TopCat.{0}) (n : ℕ) :
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _
        ((Work.CWIND.Csrc X).d (n+1) n ≫ Work.CWIND.bLevel X n)
      = ((Submission.Blueprint.singC).obj X).d (n+1) n ≫ genMap X n := by
  rw [show (Work.CWIND.Csrc X).d (n+1) n = (LightCondensed.discrete (ModuleCat ℤ)).map
      (((Submission.Blueprint.singC).obj X).d (n+1) n) from rfl]
  refine (Adjunction.homEquiv_naturality_left (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ))
    (f := (((Submission.Blueprint.singC).obj X).d (n+1) n)) (g := Work.CWIND.bLevel X n)).trans ?_
  exact congrArg (fun k => (((Submission.Blueprint.singC).obj X).d (n+1) n) ≫ k)
    (homEquiv_bLevel X n)

/-! ## Compatibility of the canonical generators -/

/-- Naturality of the unit of `free ⊣ forget` at the level of elements. -/
lemma unit_naturality_element {S T : LightCondSet} (g : S ⟶ T)
    (s : LightCondSet.underlying.obj S) :
    (LightCondensed.underlying (ModuleCat ℤ)).map ((LightCondensed.free ℤ).map g)
        (LightCondSet.underlying.map ((LightCondensed.freeForgetAdjunction ℤ).unit.app S) s)
      = LightCondSet.underlying.map ((LightCondensed.freeForgetAdjunction ℤ).unit.app T)
          (LightCondSet.underlying.map g s) := by
  rw [LightCondensed.underlying_map, LightCondensed.underlying_map, LightCondensed.underlying_map]
  have h := congrArg (fun (k : S ⟶ (LightCondensed.forget ℤ).obj ((LightCondensed.free ℤ).obj T)) =>
    LightCondSet.underlying.map k) ((LightCondensed.freeForgetAdjunction ℤ).unit.naturality g)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at h
  exact (congrArg (fun k => k s) h).symm

/-- The compatibility of the canonical generators with the simplicial structure maps. -/
lemma theGen_simp (X : TopCat.{0}) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    (LightCondensed.underlying (ModuleCat ℤ)).map
        (freeLightCondAbOfTopFunctor.map (Work.CWIND.singSpaceMap X φ)) (Work.CWIND.theGen X n x)
      = Work.CWIND.theGen X m ((TopCat.toSSet.obj X).map φ.op x) := by
  rw [Work.CWIND.theGen, Work.CWIND.theGen]
  rw [show freeLightCondAbOfTopFunctor.map (Work.CWIND.singSpaceMap X φ)
      = (LightCondensed.free ℤ).map (topCatToLightCondSet.map (Work.CWIND.singSpaceMap X φ)) from rfl]
  rw [unit_naturality_element]
  rw [thePoint_simp X φ x]

/-- The compatibility of the canonical generators with maps of spaces. -/
lemma theGen_simp_space (X Y : TopCat.{0}) (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    (LightCondensed.underlying (ModuleCat ℤ)).map
        (freeLightCondAbOfTopFunctor.map (Work.CWIND.singSpacePostcomp f n)) (Work.CWIND.theGen X n x)
      = Work.CWIND.theGen Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x) := by
  rw [Work.CWIND.theGen, Work.CWIND.theGen]
  rw [show freeLightCondAbOfTopFunctor.map (Work.CWIND.singSpacePostcomp f n)
      = (LightCondensed.free ℤ).map
          (topCatToLightCondSet.map (Work.CWIND.singSpacePostcomp f n)) from rfl]
  rw [unit_naturality_element]
  rw [thePoint_simp_space X Y f n x]


section
set_option backward.isDefEq.respectTransparency false

theorem genMap_comm (X : TopCat.{0}) (n : ℕ) :
    genMap X (n+1) ≫ (LightCondensed.underlying (ModuleCat ℤ)).map ((Achain X).d (n+1) n)
      = ((Submission.Blueprint.singC).obj X).d (n+1) n ≫ genMap X n := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := (ModuleCat.of ℤ ℤ))
  intro x
  have hd : (LightCondensed.underlying (ModuleCat ℤ)).map ((Achain X).d (n+1) n)
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
          (LightCondensed.underlying (ModuleCat ℤ)).map ((Work.CWIND.Y X).δ i) := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD,
      Functor.map_sum]
    simp only [Functor.map_zsmul]
  have hL : (TopCat.toSSet.obj X).ιChainComplex x ≫ genMap X (n+1) ≫
        (LightCondensed.underlying (ModuleCat ℤ)).map ((Achain X).d (n+1) n)
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
          (Work.CWIND.theGen X n ((ConcreteCategory.hom
            (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x))) := by
    rw [congrArg (fun k => (TopCat.toSSet.obj X).ιChainComplex x ≫ genMap X (n+1) ≫ k) hd]
    rw [← Category.assoc, Preadditive.comp_sum]
    simp only [Preadditive.comp_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    refine congrArg (fun k => (-1 : ℤ) ^ (i : ℕ) • k) ?_
    calc ((TopCat.toSSet.obj X).ιChainComplex x ≫ genMap X (n+1)) ≫
          (LightCondensed.underlying (ModuleCat ℤ)).map ((Work.CWIND.Y X).δ i)
        = (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
              (Work.CWIND.theGen X (n+1) x))) ≫
            (LightCondensed.underlying (ModuleCat ℤ)).map ((Work.CWIND.Y X).δ i) :=
          congrArg (fun k => k ≫
            (LightCondensed.underlying (ModuleCat ℤ)).map ((Work.CWIND.Y X).δ i))
            (genMap_ι X (n+1) x)
      _ = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
            ((LightCondensed.underlying (ModuleCat ℤ)).map ((Work.CWIND.Y X).δ i)
              (Work.CWIND.theGen X (n+1) x))) :=
          ofHom_toSpanSingleton_comp _ _
      _ = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
            (Work.CWIND.theGen X n ((ConcreteCategory.hom
              (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x))) :=
          congrArg (fun z => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ z))
            (theGen_simp X (SimplexCategory.δ i) x)
  have hR : (TopCat.toSSet.obj X).ιChainComplex x ≫
        ((Submission.Blueprint.singC).obj X).d (n+1) n ≫ genMap X n
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
          (Work.CWIND.theGen X n ((ConcreteCategory.hom
            (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x))) := by
    have h1 : (TopCat.toSSet.obj X).ιChainComplex x ≫
          ((Submission.Blueprint.singC).obj X).d (n+1) n
        = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
            (TopCat.toSSet.obj X).ιChainComplex ((ConcreteCategory.hom
              (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x) :=
      SSet.ιChainComplex_d (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) x
    calc (TopCat.toSSet.obj X).ιChainComplex x ≫
          ((Submission.Blueprint.singC).obj X).d (n+1) n ≫ genMap X n
        = ((TopCat.toSSet.obj X).ιChainComplex x ≫
            ((Submission.Blueprint.singC).obj X).d (n+1) n) ≫ genMap X n := by
          rw [Category.assoc]
      _ = (∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
            (TopCat.toSSet.obj X).ιChainComplex ((ConcreteCategory.hom
              (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x)) ≫ genMap X n := by rw [h1]
      _ = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
            ((TopCat.toSSet.obj X).ιChainComplex ((ConcreteCategory.hom
              (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x) ≫ genMap X n) := by
          rw [Preadditive.sum_comp]; simp only [Preadditive.zsmul_comp]
      _ = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
          (Work.CWIND.theGen X n ((ConcreteCategory.hom
            (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun k => (-1 : ℤ) ^ (i : ℕ) • k)
            (genMap_ι X n ((ConcreteCategory.hom (SimplicialObject.δ (TopCat.toSSet.obj X) i)) x))
  exact hL.trans hR.symm

lemma homEquiv_discrete_map_comp_bLevel (X : TopCat.{0}) (n : ℕ) {A : ModuleCat ℤ}
    (u : A ⟶ ((Submission.Blueprint.singC).obj X).X n) :
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _
        ((LightCondensed.discrete (ModuleCat ℤ)).map u ≫ Work.CWIND.bLevel X n)
      = u ≫ genMap X n := by
  refine (Adjunction.homEquiv_naturality_left (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ))
    (f := u) (g := Work.CWIND.bLevel X n)).trans ?_
  exact congrArg (fun k => u ≫ k) (homEquiv_bLevel X n)

theorem bLevel_comm (X : TopCat.{0}) (n : ℕ) :
    Work.CWIND.bLevel X (n+1) ≫ (Work.CWIND.Achain X).d (n+1) n =
      (Work.CWIND.Csrc X).d (n+1) n ≫ Work.CWIND.bLevel X n := by
  apply (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _ |>.injective
  exact (homEquiv_bLevel_comp_right X (n+1) ((Work.CWIND.Achain X).d (n+1) n)).trans
    ((genMap_comm X n).trans (homEquiv_Csrc_d_comp X n).symm)

theorem bLevel_naturality (X Y : TopCat.{0}) (f : X ⟶ Y) (n : ℕ) :
    (LightCondensed.discrete (ModuleCat ℤ)).map (((Submission.Blueprint.singC).map f).f n) ≫
        Work.CWIND.bLevel Y n
      = Work.CWIND.bLevel X n ≫ (Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌) := by
  apply (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv _ _ |>.injective
  have htrans1 := homEquiv_discrete_map_comp_bLevel Y n (((Submission.Blueprint.singC).map f).f n)
  have htrans2 := homEquiv_bLevel_comp_right X n ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌))
  have key : (((Submission.Blueprint.singC).map f).f n) ≫ genMap Y n
      = genMap X n ≫ (LightCondensed.underlying (ModuleCat ℤ)).map
          ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌)) := by
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := (ModuleCat.of ℤ ℤ))
    intro x
    have hL : (TopCat.toSSet.obj X).ιChainComplex x ≫
          (((Submission.Blueprint.singC).map f).f n) ≫ genMap Y n
        = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
            (Work.CWIND.theGen Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x))) := by
      have h1 : (TopCat.toSSet.obj X).ιChainComplex x ≫
            (((Submission.Blueprint.singC).map f).f n)
          = (TopCat.toSSet.obj Y).ιChainComplex
              ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x) :=
        SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
          (f := TopCat.toSSet.map f) (R := ModuleCat.of ℤ ℤ) x
      calc (TopCat.toSSet.obj X).ιChainComplex x ≫
            (((Submission.Blueprint.singC).map f).f n) ≫ genMap Y n
          = ((TopCat.toSSet.obj X).ιChainComplex x ≫
              (((Submission.Blueprint.singC).map f).f n)) ≫ genMap Y n := by
            rw [Category.assoc]
        _ = (TopCat.toSSet.obj Y).ιChainComplex
              ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x) ≫ genMap Y n := by rw [h1]
        _ = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
            (Work.CWIND.theGen Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x))) :=
            genMap_ι Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x)
    have hR : (TopCat.toSSet.obj X).ιChainComplex x ≫ genMap X n ≫
          (LightCondensed.underlying (ModuleCat ℤ)).map
            ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌))
        = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
            (Work.CWIND.theGen Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x))) := by
      calc (TopCat.toSSet.obj X).ιChainComplex x ≫ genMap X n ≫
            (LightCondensed.underlying (ModuleCat ℤ)).map
              ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌))
          = ((TopCat.toSSet.obj X).ιChainComplex x ≫ genMap X n) ≫
              (LightCondensed.underlying (ModuleCat ℤ)).map
                ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌)) := by
            rw [Category.assoc]
        _ = (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (Work.CWIND.theGen X n x))) ≫
              (LightCondensed.underlying (ModuleCat ℤ)).map
                ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌)) :=
            congrArg (fun k => k ≫ (LightCondensed.underlying (ModuleCat ℤ)).map
                ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌))) (genMap_ι X n x)
        _ = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
              ((LightCondensed.underlying (ModuleCat ℤ)).map
                ((Work.CWIND.YFunctor.map f).app (Opposite.op ⦋n⦌)) (Work.CWIND.theGen X n x))) :=
            ofHom_toSpanSingleton_comp _ _
        _ = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
            (Work.CWIND.theGen Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) x))) :=
            congrArg (fun z => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ z))
              (theGen_simp_space X Y f n x)
    exact hL.trans hR.symm
  exact htrans1.trans (key.trans htrans2.symm)

end

end Work.CWIND.BFun
