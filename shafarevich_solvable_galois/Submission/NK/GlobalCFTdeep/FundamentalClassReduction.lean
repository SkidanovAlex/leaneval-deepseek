import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.CohomologicalFieldAxiom
import Submission.NK.GlobalCFTdeep.natCard_groupCohomology_two_le_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Reducing Hasse's fundamental class to its irreducible content

`SecondInequality.HasseFundamentalClass` bundles two classical statements about
`H²(Gal(L/K), C_L)`: that its order is `[L:K]`, and that it contains an element of that order (the
fundamental class).  In this chapter

* `NK.GlobalCFTdeep.natCard_groupCohomology_two_le_card` proves **Milne, *CFT*, Theorem 5.1(c)**:
  `H²(Gal(L/K), C_L)` is *finite* and `|H²(Gal(L/K), C_L)| ≤ [L:K]` — unconditionally;
* consequently the *order* field follows from the *existence* of an element of order `[L:K]`, and
  `HasseFundamentalClass` is equivalent to the single statement

    `H²(Gal(L/K), C_L)` contains an element of order `[L:K]`    (`FundamentalClassElement`),

  which is the irreducible arithmetic content — `H²(Gal(L/K),C_L) ≅ Br(L/K) ≅ (1/[L:K])ℤ/ℤ`
  (Hasse's theorem on the Brauer group of a number field, i.e. local class field theory plus
  Shapiro for `𝕀_L` and the Hasse principle `Σ_v inv_v = 0`; the local half is the
  `HassePrinciple` chapter's `HBNUnits`, unconditional in this workspace).

## Main results

* `NK.GlobalCFTdeep.FundamentalClassElement` and
  `NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement`;
* `NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement` — the class-formation
  axioms from that single input;
* `NK.GlobalCFTdeep.galoisReciprocity_of_fundamentalClassElement`,
  `NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **The fundamental class exists**: for every finite Galois extension of number fields,
`H²(Gal(L/K), C_L)` contains an element of order `[L:K]`.

This is the irreducible Brauer-group content of Hasse's fundamental class: given it, the *order*
field of `SecondInequality.HasseFundamentalClass` follows from Milne's Theorem 5.1(c) (proved in
this chapter), and the class-formation axioms and the reciprocity isomorphisms follow from
`cohomologicalFieldAxiom_of_fundamentalClass`. -/
structure FundamentalClassElement : Prop where
  /-- the fundamental class: an element of `H²(Gal(L/K), C_L)` of order `[L:K]`. -/
  exists_fundamental : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    ∃ α : groupCohomology (IdeleClassGroup.rep K L) 2, addOrderOf α = Nat.card (L ≃ₐ[K] L)

/-- **Hasse's fundamental class from the existence of a fundamental class**: the order of
`H²(Gal(L/K), C_L)` is `[L:K]` because `|H²| ≤ [L:K]` (Milne's Theorem 5.1(c), proved in this
chapter) and an element of order `[L:K]` forces `|H²| ≥ [L:K]`. -/
theorem hasseFundamentalClass_of_fundamentalClassElement (h : FundamentalClassElement) :
    SecondInequality.HasseFundamentalClass :=
  ⟨fun {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] => by
    obtain ⟨hfin, hle⟩ := natCard_groupCohomology_two_le_card (K := K) (L := L)
    obtain ⟨α, hα⟩ := h.exists_fundamental (K := K) (L := L)
    haveI := hfin
    refine le_antisymm hle ?_
    have hcard : Nat.card ↥(AddSubgroup.zmultiples α) = Nat.card (L ≃ₐ[K] L) := by
      rw [Nat.card_zmultiples]; exact hα
    rw [← hcard]
    exact Nat.card_le_card_of_injective _ (AddSubgroup.subtype_injective _),
   h.exists_fundamental⟩

/-- **The class-formation axioms from the existence of a fundamental class** — the single input
left on this route. -/
theorem cohomologicalFieldAxiom_of_fundamentalClassElement (h : FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : CohomologicalFieldAxiom K L :=
  cohomologicalFieldAxiom_of_fundamentalClass (hasseFundamentalClass_of_fundamentalClassElement h)

/-- **Artin's reciprocity law for solvable extensions from the existence of a fundamental
class.** -/
noncomputable def galoisReciprocity_of_fundamentalClassElement (h : FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)] :
    GaloisReciprocity K L :=
  galoisReciprocity_of_fundamentalClass (hasseFundamentalClass_of_fundamentalClassElement h)

/-- **Artin's reciprocity law for abelian extensions from the existence of a fundamental
class.** -/
noncomputable def artinReciprocity_of_fundamentalClassElement (h : FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    ArtinReciprocity K L :=
  artinReciprocity_of_fundamentalClass (hasseFundamentalClass_of_fundamentalClassElement h)

end NK.GlobalCFTdeep
