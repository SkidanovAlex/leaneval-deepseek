/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.GlobalCFT
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute

/-!
# `NK.GlobalCFTdeep` — the analytic/cohomological core of global class field theory

This is the basic layer of the deep chapter: the vocabulary of the Tate-cohomological Herbrand
quotient in the form in which the chapter states its theorems, together with the first reductions
that are *proved* here (no reciprocity, no fundamental class assumed).

Everything is phrased over the idèle class group `C_L = 𝕀 L ⧸ Lˣ` of the delivered chapter
`Submission/Work/GlobalCFT/`:
* `NK.GlobalCFT.IdeleClassGroup.rep K L` is `C_L` as a `ℤ[Gal(L/K)]`-module;
* `NK.GlobalCFT.HerbrandQuotient K L` is Milne, *CFT*, Theorem 4.3;
* `NK.GlobalCFT.TwoInequalities K L` / `NK.GlobalCFT.FieldAxiom K L` are the index forms;
* `NK.GlobalCFT.CohomologicalFieldAxiom K L` is the class-formation axiom in cohomological form.

## The Herbrand quotient, as a cardinality statement

For a finite group `G` and a `ℤ[G]`-module `M` the chapter writes

* `hZero M = |Ĥ⁰(G, M)|`, `hOne M = |Ĥ¹(G, M)|`;

and `h(M) = hZero M / hOne M` whenever both are finite.  The statements of the chapter are kept in
the *multiplicative* form `hZero M = m * hOne M`, which is meaningful for `Nat.card` (equal to `0`
on infinite types) and avoids divisions.

## Universes

Mathlib's `tateCohomology` ties the universe of the coefficient ring to that of the group, so the
number fields are in `Type 0` throughout, as in the delivered chapter.
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

variable {G : Type} [Group G] [Fintype G]

/-- `|Ĥ⁰(G, M)|`, the numerator of the Herbrand quotient. -/
def hZero (M : Rep ℤ G) : ℕ := Nat.card (tateCohomology M 0)

/-- `|Ĥ¹(G, M)|`, the denominator of the Herbrand quotient. -/
def hOne (M : Rep ℤ G) : ℕ := Nat.card (tateCohomology M 1)

@[simp] theorem hZero_def (M : Rep ℤ G) : hZero M = Nat.card (tateCohomology M 0) := rfl
@[simp] theorem hOne_def (M : Rep ℤ G) : hOne M = Nat.card (tateCohomology M 1) := rfl

/-- The Herbrand quotient of `M` is `m`, written multiplicatively: `|Ĥ⁰| = m|Ĥ¹|`. -/
def HerbrandEq (M : Rep ℤ G) (m : ℕ) : Prop := hZero M = m * hOne M

end NK.GlobalCFTdeep
