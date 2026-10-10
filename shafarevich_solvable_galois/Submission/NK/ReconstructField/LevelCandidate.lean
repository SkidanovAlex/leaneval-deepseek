import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# From the weak Neukirch–Uchida theorem to candidate isomorphisms of finite levels

This file makes precise the first step of the §12.2 / §5 route: the *weak* Neukirch–Uchida theorem
(Uchida's theorem; nu2d §6, Theorem `thm:uchida isomorphism`) applied to a matched pair of finite
levels `L ⊆ K₁'`, `levelMap ϕ L ⊆ K₂'` produces an isomorphism

`τ : ↥L ≃+* ↥(levelMap ϕ L)`

of the two levels.  The matched pair has isomorphic absolute Galois groups: the isomorphism is
`NK.ReconstructField.levelGalEquiv`, the restriction of `ϕ` to
`Gal(K₁'/L) ≅ Gal(K₂'/(levelMap ϕ L))` (Mathlib's Galois correspondence together with `ϕ` and the
identity `(levelMap ϕ L).fixingSubgroup = L.fixingSubgroup.map ϕ`).

The named input of the chapter is `NK.ReconstructField.LevelIsoInput ϕ hϕ` — for every finite level
`L ⊆ K₁'` the levels `L` and `levelMap ϕ L` are isomorphic as fields.  This is *σ-free*: it asserts
no global isomorphism of the separable closures, and no compatibility between the level
isomorphisms.  It is a consequence of the weak Neukirch–Uchida theorem
(`NK.ReconstructField.levelIsoInput_of_isWeakUchida`).

The candidate produced here is *any* isomorphism of the levels: the rest of the chapter pins it down
by the arithmetic correspondence of the places.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The isomorphism of Galois groups induced by `ϕ` at a finite level.**

For a finite intermediate field `L ⊆ K₁'`, the Galois group `Gal(K₁'/L)` is isomorphic to
`Gal(K₂'/(levelMap ϕ L))` by the Galois correspondence of `Mathlib.FieldTheory.Galois.Infinite`
together with the identification `(levelMap ϕ L).fixingSubgroup = L.fixingSubgroup.map ϕ`. -/
noncomputable def levelGalEquiv (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    Gal(K₁'/↥L) ≃* Gal(K₂'/↥(levelMap ϕ L)) :=
  ((IntermediateField.fixingSubgroupEquiv L).symm.trans
    (Subgroup.equivMapOfInjective L.fixingSubgroup (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂))
      ϕ.injective)).trans
    ((MulEquiv.subgroupCongr (fixingSubgroup_levelMap hϕ L).symm).trans
      (IntermediateField.fixingSubgroupEquiv (levelMap ϕ L)))

/-- **The level-wise weak Neukirch–Uchida input (σ-free).**

For every finite level `L ⊆ K₁'`, the number fields `L` and `levelMap ϕ L` are isomorphic.  This is
the conclusion of the weak Neukirch–Uchida theorem applied to the matched pair `(L, levelMap ϕ L)`,
whose absolute Galois groups are isomorphic by `levelGalEquiv`.

The input asserts *neither* the existence of an isomorphism `K₂' ≃+* K₁'` of the separable closures
*nor* any compatibility of the level isomorphisms with each other: it is a family of isomorphisms of
finite levels only, and the compactness argument of the chapter is what packages it into a global
`σ`. -/
def LevelIsoInput (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (_hϕ : IsHomeomorph ϕ) : Prop :=
  ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L],
    Nonempty (↥L ≃+* ↥(levelMap ϕ L))

/-- A chosen candidate level isomorphism, produced from the level-wise weak input. -/
noncomputable def levelIsoOf (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (hL : LevelIsoInput ϕ hϕ) (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    ↥L ≃+* ↥(levelMap ϕ L) :=
  (hL L).some

end NK.ReconstructField

/-! ## The derivation of the level-wise input from the weak Neukirch–Uchida theorem

`NK.UchidaKummer.IsWeakUchida` is stated for number fields in the bottom universe (its binders are
`(K₁ K₂ : Type)`), so the derivation below is stated in that case; this is the case in which the
target theorem is stated when all four fields live in `Type`. -/

namespace NK.ReconstructField

open NK.Reconstruct

variable {k₁ k₂ k₁' k₂' : Type} [Field k₁] [Field k₂] [Field k₁'] [Field k₂']
  [NumberField k₁] [NumberField k₂] [Algebra k₁ k₁'] [Algebra k₂ k₂']
  [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']

/-- **The weak Neukirch–Uchida theorem implies the level-wise input.** -/
theorem levelIsoInput_of_isWeakUchida {ℓ : ℕ} (hW : NK.UchidaKummer.IsWeakUchida ℓ)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) : LevelIsoInput ϕ hϕ :=
  fun L _ =>
    @hW ↥L ↥(levelMap ϕ L) _ _ _ (numberField_levelMap hϕ L) k₁' _ _
      (isSepClosure_level L) k₂' _ _
      (isSepClosure_level (levelMap ϕ L)) ⟨levelGalEquiv ϕ hϕ L⟩

end NK.ReconstructField
