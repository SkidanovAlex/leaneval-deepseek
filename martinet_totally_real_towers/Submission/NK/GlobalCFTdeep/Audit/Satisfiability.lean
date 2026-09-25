/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.CoCore.Reciprocity
import Submission.NK.GlobalCFTdeep.Audit.cohomologicalFieldAxiom_self
import Submission.NK.GlobalCFTdeep.Audit.herbrandQuotient_self
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_eq_hOne_of_finite

/-!
# Satisfiability audits

The chapter's theorems are conditional on named classical inputs; this file records the
*satisfiability checks* that show the statements involved are not vacuous and that the ladder
produces the right objects in the degenerate case.  See `README.md` §4 for the discussion.

* `cohomologicalFieldAxiom_self` (`Audit/cohomologicalFieldAxiom_self.lean`) proves
  `NK.GlobalCFT.CohomologicalFieldAxiom K K`: the class-formation axioms are inhabited, for every
  number field `K`.  (At `L = K` the Galois group is trivial, so every subgroup is `⊥`, the
  positive-degree cohomology of the trivial group vanishes, and the fundamental class is `0` of
  order `1`.)
* consequently the chapter's reciprocity construction produces an actual isomorphism at the
  trivial extension: `artinReciprocity_self`, `galoisReciprocity_self`;
* the Herbrand input is satisfiable at a finite module
  (`Herbrand.hZero_eq_hOne_of_finite`: Herbrand's lemma) and the multiplicativity identity of
  `Herbrand/natCard_tateCohomology_mul_of_shortExact.lean` is available for the assembly.

### The `p = 2` and `p = 3` cases

`Nat.Prime 2` and `Nat.Prime 3` are checked below; a quadratic (resp. cyclic cubic) extension
`L/K` satisfies `IsCyclic (L ≃ₐ[K] L)` and `Nat.card (L ≃ₐ[K] L) = 2` (resp. `3`), so
`cohomologicalFieldAxiom_of_isCyclic_prime_card` applies to those levels.  The chapter does not
claim the two inputs at those levels: they are Milne's Theorem 4.3 and Takagi's second inequality,
i.e. the classical theorems named in `README.md` §3.

### The `L = K` case is *not* the only satisfiable instance of the Herbrand input

`NK.GlobalCFT.HerbrandQuotient K K` is provable (`Audit/herbrandQuotient_self.lean`, used as
`herbrandQuotient_self'` below): at the
trivial extension the norm is the identity, both `Ĥ⁰` and `Ĥ¹` are trivial, and `[K:K] = 1`.  What
the input `CyclicHerbrandQuotient` adds is precisely the non-trivial content.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- The class-formation axioms at the trivial extension (restatement for the reading order). -/
theorem cohomologicalFieldAxiom_self' (K : Type) [Field K] [NumberField K] :
    CohomologicalFieldAxiom K K :=
  NK.GlobalCFTdeep.Audit.cohomologicalFieldAxiom_self K

/-- **The reciprocity isomorphism at the trivial extension**: the ladder of `CoCore/Reciprocity.lean`
produces an actual `ArtinReciprocity K K`, i.e. a group isomorphism
`C_K ⧸ N_{K/K}C_K ≃* (K ≃ₐ[K] K)` — a check that the construction is well-typed and not vacuous. -/
def artinReciprocity_self (K : Type) [Field K] [NumberField K] : ArtinReciprocity K K :=
  artinReciprocity_of_cohomologicalFieldAxiom (cohomologicalFieldAxiom_self' K)

/-- **The Herbrand input at the trivial extension** (`Audit/herbrandQuotient_self.lean`):
`NK.GlobalCFT.HerbrandQuotient K K` holds, so the `HerbrandQuotient` structure is inhabited. -/
theorem herbrandQuotient_self' (K : Type) [Field K] [NumberField K] :
    HerbrandQuotient K K :=
  NK.GlobalCFTdeep.Audit.herbrandQuotient_self K

/-- `2` is prime, as required for the quadratic case of the cyclic prime-degree theorem. -/
example : (2 : ℕ).Prime := Nat.prime_two

/-- `3` is prime, as required for the cyclic cubic case of the cyclic prime-degree theorem. -/
example : (3 : ℕ).Prime := Nat.prime_three

end NK.GlobalCFTdeep
