import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The base `↥K` for the "over `K`" applications of the class-field-theory library

Step 4 of Theorem 15 (and, more generally, any *descent* step of the induction) applies the
class-field-theory inputs over the base field `K` rather than over `ℚ`: the class `y` with the
prescribed local targets lives in `H¹(k_S|K, E(n,τ))`, and the corresponding local conditions are
those of the places of `K`.  In the language of `SSGRoute.coker_obstruction` this means

  `k := ↥K`,   `K := ⊥ : IntermediateField ↥K ℚ̄`,   `N := N_m` (seen over `↥K`),

with `Ω := ℚ̄` and the *trivial* `Gal(⊥/↥K)`-module `E(n,τ)` (the action of `G_K` on the graded
piece is trivial, since `E(n,τ)` only carries a `(K ≃ₐ[ℚ] K)`-action).

None of this is automatic in Mathlib: the `ℚ`-algebra structure on `↥K` creates a diamond with the
structures on `ℚ̄` (`DESIGN.md` warns that `restrictNormalHom` conditions must not be unfolded), so
the instances `IsAlgClosure ↥K ℚ̄`, `NumberField ↥K`, `IsGalois ↥K ℚ̄` and the promotion of an
`IntermediateField ℚ ℚ̄` to an `IntermediateField ↥K ℚ̄` all have to be produced by hand.

This module contains the *base layer* of that plumbing.

## What is here

* `isAlgClosure_qbar_over_K` — `ℚ̄` is an algebraic closure of `↥K` (from
  `Algebra.IsAlgebraic.tower_top` for intermediate fields, which is an instance in
  `Mathlib/FieldTheory/IntermediateField/Algebraic.lean`);
* `isGalois_qbar_over_K` — `ℚ̄/↥K` is Galois;
* `numberField_K` — `↥K` is a number field;
* `overK` — an `IntermediateField ℚ ℚ̄` containing `K`, regarded as an `IntermediateField ↥K ℚ̄`;
* `overK_coe` — its underlying set is unchanged.

## What the descent still needs (next layers, not formalised here)

* `FiniteDimensional ↥K (overK K N hKN)` and `IsGalois ↥K (overK K N hKN)` for
  `N : IntermediateField ℚ ℚ̄` with `[FiniteDimensional ℚ N] [IsGalois ℚ N]` and `K ≤ N` —
  **done**: `Work.SSGRoute.overK_finiteDimensional_and_isGalois`
  (`Submission/Work/SSGRoute/overK_finiteDimensional_and_isGalois.lean`);
* the comparison `IsRamifiedIn ↥K (overK K N hKN) A → IsRamifiedIn ℚ N A` and
  `IsFinPlace ↥K A ↔ IsFinPlace ℚ A` (the latter is
  `Work.SSGRoute.local_transport_isFinPlace`, already proved);
* **the `↥K`-version of the finite set `S`** — also **done**:
  `Work.SSGRoute.ramifiedPlaces_finite_over_K`
  (`Submission/Work/SSGRoute/ramifiedPlaces_finite_over_K.lean`).  Detail:  `IsConjPlace ↥K A B` (conjugacy by an element of
  `G_K`) is *stronger* than `IsConjPlace ℚ A B`, and `IsConjPlace ↥K A B → IsConjPlace ℚ A B`, but
  not conversely; so the finite set of `Work.SSGRoute.ramifiedPlaces_finite` (one place per
  `ℚ`-conjugacy class) does not by itself satisfy `hSram` over the base `↥K`.  One needs the same
  finiteness statement for the `G_K`-classes, i.e. a `↥K`-version of `ramifiedPlaces_finite`
  (finitely many `G_K`-classes of places ramified in `N/↥K` or above `p`).  Note that
  `hSdisj` over `↥K` *does* follow from `hSdisj` over `ℚ` (via `IsConjPlace ↥K A B →
  IsConjPlace ℚ A B`), so only `hSfin`/`hSram` need the new finiteness statement;
* the identification of the relevant cohomology: for the *trivial* middle field `K := ⊥` over `↥K`
  the group `(⊥ ≃ₐ[↥K] ⊥)` is trivial, so the maps `πN` and `π₂` demanded by
  `SSGRoute.coker_obstruction` are the unique homomorphisms into the trivial group, and
  `hπN`/`hπ₂` are `res`-conditions that hold by `Subsingleton.elim`;
* the module structure on `E(n,τ)` over the trivial group `(⊥ ≃ₐ[↥K] ⊥)`: the action is trivial,
  so `DistribMulAction`/`SMulCommClass` are the subsingleton instances.

Only after these are available can `SSGRoute.coker_obstruction` be instantiated over `K` to produce
the class `y` of Step 4 of Schmidt–Wingberg (pp. 30–31).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open _root_.SSGRoute

/-- `ℚ̄` is an algebraic closure of the number field `↥K`. -/
theorem isAlgClosure_qbar_over_K (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] :
    IsAlgClosure ↥K SSGRoute.QBar := by
  haveI : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  rw [isAlgClosure_iff]
  refine ⟨inferInstance, ?_⟩
  haveI : Algebra.IsAlgebraic ℚ SSGRoute.QBar := IsAlgClosure.isAlgebraic
  exact inferInstance

/-- `ℚ̄/↥K` is Galois. -/
theorem isGalois_qbar_over_K (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] :
    IsGalois ↥K SSGRoute.QBar := by
  haveI : IsAlgClosure ↥K SSGRoute.QBar := isAlgClosure_qbar_over_K K
  infer_instance

/-- `↥K` is a number field. -/
theorem numberField_K (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] :
    NumberField ↥K :=
  NumberField.of_module_finite ℚ ↥K

/-- An intermediate field `N` of `ℚ̄/ℚ` containing `K`, regarded as an intermediate field of
`ℚ̄/↥K`.

This is the same object as `Subfield.extendScalars` (`Mathlib/FieldTheory/IntermediateField/Basic.lean`,
`section ExtendScalars`) applied to the subfields `K.toSubfield ≤ N.toSubfield` of `ℚ̄`; its API
(`coe_extendScalars`, `mem_extendScalars`, `extendScalars_le_iff`, ...) may be useful when proving
statements about it. -/
noncomputable def overK (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ℚ SSGRoute.QBar) (hKN : K ≤ N) :
    IntermediateField ↥K SSGRoute.QBar where
  carrier := (N : Set SSGRoute.QBar)
  mul_mem' := N.mul_mem'
  one_mem' := N.one_mem'
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  inv_mem' := N.inv_mem'
  algebraMap_mem' := fun r => hKN (Subtype.coe_prop r)

/-- `overK` does not change the underlying set. -/
theorem overK_coe (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ℚ SSGRoute.QBar) (hKN : K ≤ N) :
    ((overK K N hKN : IntermediateField ↥K SSGRoute.QBar) : Set SSGRoute.QBar)
      = (N : Set SSGRoute.QBar) :=
  rfl

end Work.SSGRoute
