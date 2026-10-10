import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Submission.Work.SSGRoute.local_detect_h_pgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

namespace RDSI

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- The unit `ℤ → ℤ` of a group change, as an isomorphism of representations. -/
def unitResIso' {H G : Type} [Group H] [Group G] (f : H →* G) :
    Rep.res f (unitRep G) ≅ unitRep H where
  hom := trivResInv f Coeff
  inv := unitRes f
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

/-- **Change of group along a group isomorphism on `Ext`**, as an additive equivalence. -/
noncomputable def extResEquiv' {G₁ G₂ : Type} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (X Y : Rep.{0} Coeff G₂) (n : ℕ) :
    Abelian.Ext X Y n ≃+ Abelian.Ext (Rep.res e.toMonoidHom X) (Rep.res e.toMonoidHom Y) n := by
  haveI : (Rep.resFunctor (k := Coeff) e.toMonoidHom).IsEquivalence := by
    have h : (e.symm).symm.toMonoidHom = e.toMonoidHom := by rw [MulEquiv.symm_symm]
    rw [← h]
    exact resFunctor_isEquivalence e.symm
  exact AddEquiv.ofBijective ((Rep.resFunctor e.toMonoidHom).mapExtAddHom X Y n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects _ X Y n)

@[simp] lemma extResEquiv'_apply {G₁ G₂ : Type} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (X Y : Rep.{0} Coeff G₂) (n : ℕ) (x : Abelian.Ext X Y n) :
    extResEquiv' e X Y n x = extRes e.toMonoidHom x := rfl

/-- The `H¹`-restriction along a group isomorphism is injective. -/
theorem extHMap_self_ne_zero {G H : Type} [Group G] [Group H] (e : H ≃* G)
    {B : Rep.{0} Coeff G} {n : ℕ} (y : extH B n) (hy : y ≠ 0) :
    extHMap e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom B)) y ≠ 0 := by
  intro h0
  have h0u : (Abelian.Ext.mk₀ (unitRes e.toMonoidHom)).comp (extRes e.toMonoidHom y)
      (zero_add n) = 0 := by
    have h := h0
    simp only [SSGRoute.PTExt.extHMap, Abelian.Ext.comp_mk₀_id] at h
    exact h
  have hZ : (Abelian.Ext.mk₀ (unitResIso' e.toMonoidHom).hom).comp
      ((Abelian.Ext.mk₀ (unitRes e.toMonoidHom)).comp (extRes e.toMonoidHom y)
        (zero_add n)) (zero_add n) = extRes e.toMonoidHom y := by
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
    rw [show Abelian.Ext.mk₀ (unitRes e.toMonoidHom)
        = Abelian.Ext.mk₀ ((unitResIso' e.toMonoidHom).inv) from rfl]
    rw [Abelian.Ext.mk₀_comp_mk₀, (unitResIso' e.toMonoidHom).hom_inv_id,
      Abelian.Ext.mk₀_id_comp]
  have h1 : extRes e.toMonoidHom y = 0 := by
    rw [← hZ, h0u, Abelian.Ext.comp_zero]
  refine hy ?_
  apply (extResEquiv' e (unitRep G) B n).injective
  rw [map_zero, extResEquiv'_apply]
  exact h1

/-- **Two level maps which are equal give the same level pairing**, after transporting the
coefficient map and the `H¹`-class along the (propositional) equality of the two levels. -/
theorem levelPair_eqOfEq {G H' : Type} [Group G] [Group H']
    (φ φ' : H' →* G) (hcomp : φ' = φ)
    {M A : Rep.{0} Coeff G} {B' : Rep.{0} Coeff H'} (ι : Rep.res φ A ⟶ B')
    (ι' : Rep.res φ' A ⟶ B')
    (hι : ι = eqToHom (congrArg (fun t => Rep.res t A) hcomp.symm) ≫ ι')
    {s : ℕ} (x : Abelian.Ext M A 1) (h : extH (Rep.res φ M) s) :
    levelPair φ' ι' x
        (h.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t M) hcomp.symm)))
          (add_zero s))
      = levelPair φ ι x h := by
  cases hcomp
  simp only [CategoryTheory.eqToHom_refl, Category.id_comp, Abelian.Ext.comp_mk₀_id] at hι ⊢
  rw [hι]

/-- **The coefficient map of a level transported along an equality of the level maps** is the
coefficient map of the transported level, given pointwise agreement. -/
theorem coeffMap_eqOfEq {G H' : Type} [Group G] [Group H']
    (φ φ' : H' →* G) (hcomp : φ' = φ)
    {A : Rep.{0} Coeff G} {B' : Rep.{0} Coeff H'} (ι : Rep.res φ A ⟶ B')
    (ι' : Rep.res φ' A ⟶ B')
    (H : ∀ v : A.V, (Rep.Hom.hom ι') v = (Rep.Hom.hom ι) v) :
    ι = eqToHom (congrArg (fun t => Rep.res t A) hcomp.symm) ≫ ι' := by
  cases hcomp
  simp only [CategoryTheory.eqToHom_refl, Category.id_comp]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact (H v).symm

/-- A nonzero `H¹`-class stays nonzero after transporting its coefficient module along an
equality. -/
theorem comp_eqToHom_ne_zero {G : Type} [Group G] {X Y : Rep.{0} Coeff G} (h : X = Y)
    {n : ℕ} (a : extH X n) (ha : a ≠ 0) :
    a.comp (Abelian.Ext.mk₀ (eqToHom h)) (add_zero n) ≠ 0 := by
  intro h0
  refine ha ?_
  have hback : (a.comp (Abelian.Ext.mk₀ (eqToHom h)) (add_zero n)).comp
      (Abelian.Ext.mk₀ (eqToHom h.symm)) (add_zero n) = a := by
    rw [Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀]
    have : eqToHom h ≫ eqToHom h.symm = 𝟙 _ := by
      rw [CategoryTheory.eqToHom_trans]
      rw [show h.trans h.symm = rfl from Subsingleton.elim _ _,
        CategoryTheory.eqToHom_refl]
    rw [this, Abelian.Ext.comp_mk₀_id]
    all_goals try omega
  rw [← hback, h0, Abelian.Ext.zero_comp]

end RDSI

theorem rightDetect_sylowLevelStabIncl (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K)) (hP : IsPGroup p P)
    (hPD : P ≤ SSGRoute.PTExt.decompK (k := k) w)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
    (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w) ⟶
      NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp' : p ∣ Nat.card (MulAction.stabilizer
      (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w')) :
    SSGRoute.PTExt.RightDetect
      (A := Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
        (SSGRoute.PTExt.localUnitsK (k := k) w))
      (B := Rep.res ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w'))
      (f.subgroupComap (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype))
      (Rep.resMap ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype ι)
      (Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)) := by
  classical
  haveI hgalL : IsGalois ↥(IntermediateField.fixedField P) L :=
    IsGalois.tower_top_of_isGalois k (IntermediateField.fixedField P) L
  -- ## The two group isomorphisms (base change `k → k' = K^P`)
  let eK : SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w ≃*
      P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype :=
    Work.SSGRoute.stabInclEquivK k K w P hPD
  let eL : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' ≃*
      (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f :=
    Work.SSGRoute.stabInclEquivL k K L P w hPD w' hw' f hf
  -- ## The `k'`-world level data
  obtain ⟨f', hf'⟩ := Work.SSGRoute.decompK_restrict_exists
      ↥(IntermediateField.fixedField P) K L w w' hw'
  obtain ⟨ι', hι'⟩ := Work.SSGRoute.localUnitsMap_exists
      ↥(IntermediateField.fixedField P) K L w w' hw' f' hf'
  -- ## The two level maps agree
  have hcomp : eK.toMonoidHom.comp f' =
      (f.subgroupComap (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype)).comp
        eL.toMonoidHom := by
    have hcast2 : ∀ σ : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w',
        ((eL σ : (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f) :
          MulAction.stabilizer (L ≃ₐ[k] L) w')
          = AlgEquiv.restrictScalars k (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L) := fun σ => by
      rw [show ((eL σ : (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f) :
          MulAction.stabilizer (L ≃ₐ[k] L) w') = Work.SSGRoute.stabIncl (k := k)
          (M := ↥(IntermediateField.fixedField P)) (E := L) w' σ from
        Work.SSGRoute.stabInclEquivL_apply k K L P w hPD w' hw' f hf σ]
      rfl
    refine MonoidHom.ext fun σ => Subtype.ext (Subtype.ext (AlgEquiv.ext fun x => ?_))
    simp only [MonoidHom.comp_apply]
    change (AlgEquiv.restrictScalars k ((f' σ :
        SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w) :
        K ≃ₐ[↥(IntermediateField.fixedField P)] K)) x
      = ((f (eL σ) : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K) x
    rw [hf' σ, hf (eL σ), hcast2 σ]
    apply (algebraMap K L).injective
    rw [show (algebraMap K L) ((AlgEquiv.restrictScalars k ((SSGRoute.PTExt.galRes
        ↥(IntermediateField.fixedField P) K L)
        (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L))) x)
        = (algebraMap K L) (((σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)).restrictNormal K x) from rfl,
      show (algebraMap K L) ((SSGRoute.PTExt.galRes k K L
        (AlgEquiv.restrictScalars k (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L))) x)
        = (algebraMap K L) (((AlgEquiv.restrictScalars k
          (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)).restrictNormal K x)) from rfl]
    rw [AlgEquiv.restrictNormal_commutes (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L) K x,
        AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars k
          (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)) K x]
    rfl
  -- ## Right detection in the `k'`-world
  have hD : IsPGroup p (SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w) :=
    (Work.SSGRoute.SylowIn.isPGroup_fixedField (P := P) hP).to_subgroup _
  haveI hfin : Finite (Rep.res (SSGRoute.PTExt.decompK
      (k := ↥(IntermediateField.fixedField P)) w).subtype
      (Rep.res (AlgEquiv.restrictScalarsHom (R := k)
        (S := ↥(IntermediateField.fixedField P)) (A := K)) M)) := inferInstance
  have hM' : ∀ n : Rep.res (SSGRoute.PTExt.decompK
      (k := ↥(IntermediateField.fixedField P)) w).subtype
      (Rep.res (AlgEquiv.restrictScalarsHom (R := k)
        (S := ↥(IntermediateField.fixedField P)) (A := K)) M), p • n = 0 := fun n => hM n
  have hdet : SSGRoute.PTExt.RightDetect f' ι'
      (Rep.res (SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w).subtype
        (Rep.res (AlgEquiv.restrictScalarsHom (R := k)
          (S := ↥(IntermediateField.fixedField P)) (A := K)) M)) :=
    Work.SSGRoute.local_detect_h_pgroup p ↥(IntermediateField.fixedField P) K w hD _
      hM' L w' hw' f' hf' ι' hι' hp'
  -- ## The transport
  intro h hne
  -- abbreviations for the `k`-world at the subgroup `S`
  let M_S := Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
  let A_S := Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
      (SSGRoute.PTExt.localUnitsK (k := k) w)
  let φ₀ := f.subgroupComap (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype)
  let B := Rep.res ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype
      (NK.HassePrinciple.localUnitsRep k L w')
  let ι_S := Rep.resMap ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype ι
  let B' := NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w'
  -- the `H¹`-class at the `eL`-level
  let h₁ := extHMap eL.toMonoidHom (𝟙 (Rep.res eL.toMonoidHom (Rep.res φ₀ M_S))) h
  have h₁ne : h₁ ≠ 0 := RDSI.extHMap_self_ne_zero eL h hne
  -- the transported `H¹`-class at the `eK ∘ f'`-level
  let h₂ := h₁.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t M_S) hcomp.symm)))
    (add_zero 1)
  have h₂ne : h₂ ≠ 0 :=
    RDSI.comp_eqToHom_ne_zero (congrArg (fun t => Rep.res t M_S) hcomp.symm) h₁ h₁ne
  obtain ⟨y', hy'⟩ := hdet h₂ h₂ne
  -- the class at the `k`-world `S`-level
  set y : Abelian.Ext M_S A_S 1 := (RDSI.extResEquiv' eK M_S A_S 1).symm y' with hydef
  have hy : extRes eK.toMonoidHom y = y' := by
    rw [hydef, ← RDSI.extResEquiv'_apply]
    exact AddEquiv.apply_symm_apply _ _
  refine ⟨y, ?_⟩
  -- ## The identification of the coefficient maps
  have hιM : (Rep.resMap eL.toMonoidHom ι_S)
      = eqToHom (congrArg (fun t => Rep.res t A_S) hcomp.symm) ≫ ι' := by
    refine RDSI.coeffMap_eqOfEq (A := A_S) (B' := B') (φ := φ₀.comp eL.toMonoidHom)
      (φ' := eK.toMonoidHom.comp f') hcomp (ι := Rep.resMap eL.toMonoidHom ι_S) (ι' := ι') ?_
    intro v
    change (Rep.Hom.hom ι') v = (Rep.Hom.hom ι) v
    calc (Rep.Hom.hom ι') v
        = (Rep.Hom.hom ι') (Additive.ofMul (Additive.toMul v)) := rfl
      _ = Additive.ofMul ((NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw') (Additive.toMul v)) :=
            hι' (Additive.toMul v)
      _ = (Rep.Hom.hom ι) (Additive.ofMul (Additive.toMul v)) := (hι (Additive.toMul v)).symm
      _ = (Rep.Hom.hom ι) v := rfl
  -- ## The final chain of pairings
  have hchain : levelPair f' ι' y' h₂
      = extHMap eL.toMonoidHom (𝟙 (Rep.res eL.toMonoidHom B))
          (levelPair φ₀ ι_S y h) := by
    calc levelPair f' ι' y' h₂
        = levelPair f' ι' (extRes eK.toMonoidHom y) h₂ := by rw [hy]
      _ = levelPair (eK.toMonoidHom.comp f') ι' y h₂ := by
            simp only [SSGRoute.PTExt.levelPair]
            rw [← Work.SSGRoute.SylowDesc.extRes_comp_aux]
      _ = levelPair (φ₀.comp eL.toMonoidHom) (Rep.resMap eL.toMonoidHom ι_S) y h₁ :=
            RDSI.levelPair_eqOfEq (M := M_S) (A := A_S) (B' := B')
              (φ₀.comp eL.toMonoidHom) (eK.toMonoidHom.comp f') hcomp
              (Rep.resMap eL.toMonoidHom ι_S) ι' hιM y h₁
      _ = extHMap eL.toMonoidHom (𝟙 (Rep.res eL.toMonoidHom B)) (levelPair φ₀ ι_S y h) :=
            (Work.SSGRoute.SylowIn.levelPair_restrict (M := M_S) (A := A_S) (B := B)
              (B' := Rep.res eL.toMonoidHom B) φ₀ eL.toMonoidHom ι_S
              (𝟙 (Rep.res eL.toMonoidHom B)) (Rep.resMap eL.toMonoidHom ι_S) y h rfl).symm
  rw [hchain] at hy'
  exact fun h0 => hy' (by rw [h0, E6Util.extHMap_zero])

end Work.SSGRoute
