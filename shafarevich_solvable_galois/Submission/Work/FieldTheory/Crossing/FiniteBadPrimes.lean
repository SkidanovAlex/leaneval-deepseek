/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finiteness of the set of intermediate fields, and of the "bad" primes

* `finite_intermediateFields_of_isGalois`: a finite Galois extension `L/F` has only finitely many
  intermediate fields.  The injection `F' ↦ (F'.restrict h).fixingSubgroup` into `Gal(L/F)` is
  injective (if two restricted subfields have the same fixing subgroup they are equal, by
  `IsGalois.fixedField_fixingSubgroup`), and `Gal(L/F)` is finite because
  `IsGalois.card_aut_eq_finrank` computes its cardinality as `[L : F] > 0`.
* `finite_bad_primes`: only finitely many primes `p` have `CycloField p ⊓ L ≠ ⊥`, because
  `p ↦ CycloField p ⊓ L` is injective on the bad primes (if `CycloField p ⊓ L = CycloField q ⊓ L`
  for `p ≠ q`, that field is contained in `CycloField p ⊓ CycloField q = ⊥`, a contradiction).

Both are stated over a generic base field where elaboration is clean; the `ℚ`-specialised
`finite_bad_primes` is obtained by passing the instances explicitly.

## Main declarations

* `finite_intermediateFields_of_isGalois`
* `finite_bad_primes`

-/
import Mathlib
import Submission.Work.FieldTheory.Crossing.Defs
import Submission.Work.FieldTheory.Crossing.Disjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Classical
open scoped Nat

noncomputable section

set_option linter.style.haveILetI false

/-- A finite Galois extension has only finitely many intermediate fields. -/
theorem finite_intermediateFields_of_isGalois {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] :
    Finite {F' : IntermediateField F Ω // F' ≤ L} := by
  haveI : Finite Gal(↥L/F) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank F ↥L]
    exact (Module.finrank_pos (R := F) (M := ↥L)).ne'
  refine Finite.of_injective
    (fun F' : {F' : IntermediateField F Ω // F' ≤ L} =>
      (F'.1.restrict F'.2).fixingSubgroup) ?_
  intro F₁ F₂ h
  have h1 : F₁.1.restrict F₁.2 = F₂.1.restrict F₂.2 := by
    have h2 := congrArg IntermediateField.fixedField h
    rwa [IsGalois.fixedField_fixingSubgroup, IsGalois.fixedField_fixingSubgroup] at h2
  apply Subtype.ext
  refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hxL : x ∈ L := F₁.2 hx
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ F₁.1.restrict F₁.2 :=
      (IntermediateField.mem_restrict F₁.2 _).mpr hx
    rw [h1] at hx'
    exact (IntermediateField.mem_restrict F₂.2 _).mp hx'
  · have hxL : x ∈ L := F₂.2 hx
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ F₂.1.restrict F₂.2 :=
      (IntermediateField.mem_restrict F₂.2 _).mpr hx
    rw [← h1] at hx'
    exact (IntermediateField.mem_restrict F₁.2 _).mp hx'

/-- **Only finitely many primes are "bad" for a finite Galois `L`**, i.e. satisfy
`CycloField p ⊓ L ≠ ⊥`. -/
theorem finite_bad_primes (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hfd : FiniteDimensional ℚ L) (hG : IsGalois ℚ L) :
    ({p : ℕ | Nat.Prime p ∧ CycloField p ⊓ L ≠ ⊥} : Set ℕ).Finite := by
  have hfin : Finite {F' : IntermediateField ℚ (AlgebraicClosure ℚ) // F' ≤ L} :=
    @finite_intermediateFields_of_isGalois ℚ (AlgebraicClosure ℚ) _ _ _ L hfd hG
  refine Finite.of_injective
    (fun p : {p : ℕ | Nat.Prime p ∧ CycloField p ⊓ L ≠ ⊥} =>
      (⟨CycloField p.1 ⊓ L, inf_le_right⟩ :
        {F' : IntermediateField ℚ (AlgebraicClosure ℚ) // F' ≤ L})) ?_
  intro p q hpq
  haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩
  haveI : NeZero q.1 := ⟨q.2.1.ne_zero⟩
  apply Subtype.ext
  by_contra hne
  have heq : CycloField p.1 ⊓ L = CycloField q.1 ⊓ L := congrArg Subtype.val hpq
  have hle : CycloField p.1 ⊓ L ≤ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
    have h3 : CycloField p.1 ⊓ L ≤ CycloField p.1 ⊓ CycloField q.1 :=
      le_inf inf_le_left (heq ▸ inf_le_left)
    rwa [cycloField_inf_eq_bot p.2.1 q.2.1 hne] at h3
  exact p.2.2 (le_bot_iff.mp hle)


/-- `exists_disjoint_cyclic`-style instance-friendly form of `finite_bad_primes`. -/
theorem finite_bad_primes_of_instances (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [hfd : FiniteDimensional ℚ L] [hG : IsGalois ℚ L] :
    ({p : ℕ | Nat.Prime p ∧ CycloField p ⊓ L ≠ ⊥} : Set ℕ).Finite :=
  finite_bad_primes L hfd hG

end

end Work.FieldTheory.Crossing
