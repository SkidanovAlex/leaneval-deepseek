import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Category.ModuleCat.Basic
import Submission.NK.BrauerHasse.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option maxHeartbeats 1600000

set_option autoImplicit false

universe u

namespace NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The finite levels of a closed subgroup -/

/-- The finite level of the profinite group `U ≤ Gal(K'/K)` corresponding to a finite Galois
intermediate field `L`: the finite quotient `U / (U ∩ Gal(K'/L))`. -/
abbrev LevelGroup (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') : Type u :=
  ↥U ⧸ L.fixingSubgroup.subgroupOf U

/-- The level `H²(U / (U ∩ Gal(K'/L)), Z/p)`. -/
noncomputable abbrev LevelH2 (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : ModuleCat (Coeff.{u} p) :=
  H2 p (LevelGroup U L)

section levelMap

variable (p : ℕ) {U V : Subgroup Gal(K'/K)}

omit [IsSepClosure K K'] in
lemma fixingSubgroup_subgroupOf_le {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') (U : Subgroup Gal(K'/K)) :
    L'.fixingSubgroup.subgroupOf U ≤ L.fixingSubgroup.subgroupOf U :=
  fun _ hx => IntermediateField.fixingSubgroup_le h hx

/-- The quotient map `U/(U ∩ Gal(K'/L')) →* U/(U ∩ Gal(K'/L))` for `L ≤ L'`. -/
noncomputable def levelQuotHom {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    LevelGroup U L' →* LevelGroup U L :=
  QuotientGroup.map (L'.fixingSubgroup.subgroupOf U) (L.fixingSubgroup.subgroupOf U)
    (MonoidHom.id ↥U) (by simpa using fixingSubgroup_subgroupOf_le h U)

lemma levelQuotHom_comp {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂)
    (h₂ : L₂ ≤ L₃) :
    (levelQuotHom (U := U) h₁).comp (levelQuotHom (U := U) h₂) =
      levelQuotHom (U := U) (h₁.trans h₂) := by
  simp only [levelQuotHom]
  rw [QuotientGroup.map_comp_map (N := L₃.fixingSubgroup.subgroupOf U)
      (M := L₂.fixingSubgroup.subgroupOf U) (O := L₁.fixingSubgroup.subgroupOf U)
      (f := MonoidHom.id ↥U) (g := MonoidHom.id ↥U)]
  simp

/-- **Inflation between levels**: for `L ≤ L'` the level cohomologies are connected by the
inflation map of the quotient `U/(U ∩ Gal(K'/L')) ↠ U/(U ∩ Gal(K'/L))`. -/
noncomputable def levelMap {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    LevelH2 p U L ⟶ LevelH2 p U L' :=
  H2.map (levelQuotHom (U := U) h)

lemma levelMap_comp {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂)
    (h₂ : L₂ ≤ L₃) :
    levelMap p (U := U) h₁ ≫ levelMap p (U := U) h₂ =
      levelMap p (U := U) (h₁.trans h₂) := by
  simp only [levelMap]
  rw [← H2.map_comp, levelQuotHom_comp]

@[simp]
lemma levelMap_apply {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : LevelH2 p U L) :
    (levelMap p (U := U) h) x = (H2.map (levelQuotHom (U := U) h)).hom x := rfl

/-- The quotient map `V/(V ∩ Gal(K'/L)) →* U/(U ∩ Gal(K'/L))` induced by an inclusion of closed
subgroups `V ≤ U`; it induces the *restriction* map on profinite cohomology. -/
noncomputable def levelInclHom {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') : LevelGroup V L →* LevelGroup U L :=
  QuotientGroup.map (L.fixingSubgroup.subgroupOf V) (L.fixingSubgroup.subgroupOf U)
    (Subgroup.inclusion h) (fun x hx => by simpa using hx)

end levelMap

/-! ## The colimit -/

section colimit

variable (p : ℕ) (U : Subgroup Gal(K'/K))

/-- The generating relation of the filtered colimit: an element of a finite level and its
inflation to a larger level are identified. -/
def colimitGen : (Σ L : FiniteGaloisIntermediateField K K', LevelH2 p U L) →
    (Σ L : FiniteGaloisIntermediateField K K', LevelH2 p U L) → Prop :=
  fun x y => ∃ (h : x.1 ≤ y.1), y.2 = (levelMap p (U := U) h) x.2

/-- **The profinite cohomology `H²(U, Z/p)`** of a closed subgroup `U ≤ Gal(K'/K)`: the filtered
colimit of the cohomologies of the finite quotients `U/(U ∩ Gal(K'/L))` along the inflation
maps. -/
noncomputable def H2Profinite : Type u := Quot (Relation.EqvGen (colimitGen p U))

variable {p U V}

/-- The structure map from a finite level into `H²(U, Z/p)`. -/
noncomputable def H2Profinite.ofLevel (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) : H2Profinite p U :=
  Quot.mk _ ⟨L, a⟩

/-- **Every element of `H²(U, Z/p)` comes from a finite level.** -/
lemma H2Profinite.ofLevel_surjective (x : H2Profinite p U) :
    ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      H2Profinite.ofLevel L a = x := by
  induction x using Quot.ind with
  | _ y => exact ⟨y.1, y.2, rfl⟩

/-- An element of a smaller level and its inflation to a larger level define the same class. -/
lemma H2Profinite.ofLevel_levelMap {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (a : LevelH2 p U L) :
    H2Profinite.ofLevel L' ((levelMap p (U := U) h) a) = H2Profinite.ofLevel L a :=
  (Quot.sound (Relation.EqvGen.rel _ _ ⟨h, rfl⟩)).symm

/-- **The universal property of `H²(U, Z/p)`**: a compatible family of maps on the levels
descends to the colimit. -/
noncomputable def H2Profinite.lift {β : Sort*} (f : ∀ L : FiniteGaloisIntermediateField K K',
    LevelH2 p U L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L),
      f L' ((levelMap p (U := U) h) a) = f L a) :
    H2Profinite p U → β :=
  Quot.lift (fun x => f x.1 x.2) (by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact (hf x.1 y.1 hxy.1 x.2).symm.trans (congrArg (f y.1) hxy.2).symm
    | refl x => rfl
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)

@[simp]
lemma H2Profinite.lift_ofLevel {β : Sort*} (f : ∀ L : FiniteGaloisIntermediateField K K',
    LevelH2 p U L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L),
      f L' ((levelMap p (U := U) h) a) = f L a)
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    H2Profinite.lift f hf (H2Profinite.ofLevel L a) = f L a := rfl

/-- Two maps out of `H²(U, Z/p)` agreeing on all levels are equal. -/
lemma H2Profinite.lift_unique {β : Sort*} (f : ∀ L : FiniteGaloisIntermediateField K K',
    LevelH2 p U L → β)
    (hf : ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L),
      f L' ((levelMap p (U := U) h) a) = f L a)
    (g : H2Profinite p U → β) (hg : ∀ L a, g (H2Profinite.ofLevel L a) = f L a) :
    g = H2Profinite.lift f hf := by
  funext x
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [H2Profinite.lift_ofLevel, hg]

end colimit

/-! ## Local cohomology at a place and the localisation map -/

section localisation

variable (p : ℕ)

/-- The **decomposition group** of a place `A` of `K'`, as a subgroup of `Gal(K'/K)`: the
stabiliser of `A` under the action of `Gal(K'/K)` on places (valuation subrings). -/
abbrev stabSubgroup (A : ValuationSubring K') : Subgroup Gal(K'/K) :=
  MulAction.stabilizer Gal(K'/K) A

/-- The local finite level at a place: `(U ∩ D_A) / ((U ∩ D_A) ∩ Gal(K'/L))`. -/
abbrev LocalLevelGroup (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : Type u :=
  ↥(U ⊓ stabSubgroup A) ⧸ L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A)

/-- The local level `H²((U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L)), Z/p)`. -/
noncomputable abbrev LocalLevelH2 (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : ModuleCat (Coeff.{u} p) :=
  H2 p (LocalLevelGroup U A L)

/-- The inclusion-induced quotient map `(U ∩ D_A)/((U∩D_A) ∩ Gal(K'/L)) →* U/(U ∩ Gal(K'/L))`. -/
noncomputable def localInclHom (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : LocalLevelGroup U A L →* LevelGroup U L :=
  QuotientGroup.map (L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
    (L.fixingSubgroup.subgroupOf U) (Subgroup.inclusion inf_le_left)
    (fun x hx => by simpa using hx)

/-- **The level-wise localisation map** `H²(U/(U ∩ Gal(K'/L))) → H²((U ∩ D_A)/(...))`. -/
noncomputable def locLevel (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    LevelH2 p U L ⟶ LocalLevelH2 p U A L :=
  H2.map (localInclHom U A L)

/-- The inclusion-induced quotient map for `L ≤ L'` on the local levels. -/
noncomputable def localLevelQuotHom (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    LocalLevelGroup U A L' →* LocalLevelGroup U A L :=
  QuotientGroup.map (L'.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
    (L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A)) (MonoidHom.id ↥(U ⊓ stabSubgroup A))
    (by simpa using fixingSubgroup_subgroupOf_le h (U ⊓ stabSubgroup A))

/-- **Inflation between levels, locally at a place.** -/
noncomputable def localLevelMap (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    LocalLevelH2 p U A L ⟶ LocalLevelH2 p U A L' :=
  H2.map (localLevelQuotHom U A h)

/-- **The local cohomology at a place**: the colimit of the local level cohomologies. -/
noncomputable def LocalH2 (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') : Type u :=
  Quot (Relation.EqvGen (fun x y : Σ L : FiniteGaloisIntermediateField K K', LocalLevelH2 p U A L =>
    ∃ (h : x.1 ≤ y.1), y.2 = (localLevelMap p U A h) x.2))

/-- The structure map from a local level into `LocalH2`. -/
noncomputable def LocalH2.ofLevel (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L) :
    LocalH2 p U A :=
  Quot.mk _ ⟨L, a⟩

lemma LocalH2.ofLevel_levelMap (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (a : LocalLevelH2 p U A L) :
    LocalH2.ofLevel p U A L' ((localLevelMap p U A h) a) = LocalH2.ofLevel p U A L a :=
  (Quot.sound (Relation.EqvGen.rel _ _ ⟨h, rfl⟩)).symm

/-- Naturality of the inclusion of the local level groups in the global level group. -/
lemma localInclHom_comp (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    (levelQuotHom (U := U) h).comp (localInclHom U A L') =
      (localInclHom U A L).comp (localLevelQuotHom U A h) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => simp [levelQuotHom, localInclHom, localLevelQuotHom]

/-- **The compatibility of the level-wise localisation maps with inflation**, i.e. the commuting
square expressing that the localisation is a map of filtered systems. -/
lemma levelMap_locLevel (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    levelMap p (U := U) h ≫ locLevel p U A L' = locLevel p U A L ≫ localLevelMap p U A h := by
  simp only [levelMap, locLevel, localLevelMap]
  rw [← H2.map_comp, ← H2.map_comp, localInclHom_comp U A h]

/-- Elementwise form of `levelMap_locLevel`. -/
lemma levelMap_locLevel_apply (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (a : LevelH2 p U L) :
    (locLevel p U A L') ((levelMap p (U := U) h) a) =
      (localLevelMap p U A h) ((locLevel p U A L) a) := by
  simp only [levelMap, locLevel, localLevelMap]
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    ← H2.map_comp, ← H2.map_comp, localInclHom_comp U A h]

/-- The places of `K'` over a finite prime of `K`, i.e. the valuation subrings of `K'` whose
restriction to `K` is not everything. -/
def OverFinitePrime (K : Type u) (K' : Type u) [Field K] [Field K'] [Algebra K K'] :
    Type u :=
  {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤}

/-- The product of the local cohomologies at all places over the finite primes of `K`. -/
def LocalProduct (p : ℕ) (K : Type u) (K' : Type u) [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (U : Subgroup Gal(K'/K)) : Type u :=
  ∀ A : OverFinitePrime K K', LocalH2 p U A.1

/-- The level-wise description of the localisation map, as a family of maps on the levels. -/
noncomputable def locFamily (U : Subgroup Gal(K'/K)) :
    ∀ L : FiniteGaloisIntermediateField K K',
      LevelH2 p U L → LocalProduct p K K' U :=
  fun L a A => LocalH2.ofLevel p U A.1 L ((locLevel p U A.1 L) a)

/-- The compatibility of `locFamily` with the inflation maps. -/
lemma locFamily_compat (U : Subgroup Gal(K'/K))
    (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p U L) :
    locFamily (p := p) (K := K) (K' := K') U L' ((levelMap p (U := U) h) a) =
      locFamily (p := p) (K := K) (K' := K') U L a := by
  funext A
  exact (congrArg (fun y => LocalH2.ofLevel p U A.1 L' y)
          (levelMap_locLevel_apply (p := p) (U := U) (A := A.1) (h := h) a)).trans
    (LocalH2.ofLevel_levelMap (p := p) (U := U) (A := A.1) (h := h)
      ((locLevel p U A.1 L) a))

/-- **The localisation map**: from the global cohomology `H²(U, Z/p)` to the product of the local
cohomologies at all places of `K'` over a finite prime of `K`. -/
noncomputable def H2Profinite.loc (U : Subgroup Gal(K'/K)) :
    H2Profinite p U → LocalProduct p K K' U :=
  Quot.lift (fun x : Σ L : FiniteGaloisIntermediateField K K', LevelH2 p U L =>
      locFamily (p := p) (K := K) (K' := K') U x.1 x.2)
    (by
      intro x y hxy
      induction hxy with
      | rel x y hxy =>
          exact (locFamily_compat (p := p) (K := K) (K' := K') U x.1 y.1 hxy.1 x.2).symm.trans
            (congrArg (locFamily (p := p) (K := K) (K' := K') U y.1) hxy.2).symm
      | refl x => rfl
      | symm x y hxy ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)

noncomputable instance instZeroH2Profinite (p : ℕ) (U : Subgroup Gal(K'/K)) : Zero (H2Profinite p U) :=
  ⟨Quot.mk _ ⟨⊥, 0⟩⟩

noncomputable instance instZeroLocalH2 (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    Zero (LocalH2 p U A) :=
  ⟨Quot.mk _ ⟨⊥, 0⟩⟩

/-- **The computation rule for the localisation map**: the localisation of a class represented at
a finite level `L` is the class of its level-wise localisation at `L`. -/
lemma H2Profinite.loc_ofLevel_apply (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) (A : OverFinitePrime K K') :
    H2Profinite.loc p U (H2Profinite.ofLevel L a) A =
      LocalH2.ofLevel p U A.1 L ((locLevel p U A.1 L) a) := rfl

/-- The distinguished zero of the colimit is localised to the distinguished zero of the local
colimit. -/
lemma H2Profinite.loc_zero (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K') :
    H2Profinite.loc p U (0 : H2Profinite p U) A = 0 := by
  show H2Profinite.loc p U (H2Profinite.ofLevel ⊥ (0 : LevelH2 p U ⊥)) A = 0
  rw [H2Profinite.loc_ofLevel_apply, map_zero]
  rfl



end localisation

end NK.BrauerHasse
