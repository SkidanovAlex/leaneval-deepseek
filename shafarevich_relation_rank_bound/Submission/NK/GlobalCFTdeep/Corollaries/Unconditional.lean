/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.CyclicHerbrandQuotient
import Submission.NK.GlobalCFTdeep.Corollaries.HasseNorm

/-!
# The boundary theorems with `CyclicHerbrandQuotient` discharged

`NK.GlobalCFTdeep.cyclicHerbrandQuotient` proves Milne's Theorem 4.3 — `h(Gal(L/K), C_L) = [L:K]`
for every finite cyclic extension — so every result of this chapter that used `CyclicHerbrandQuotient`
as an input now depends only on the *second* inequality (and on Milne's reduction 5.3–5.4, or on
Takagi's existence theorem, where those are genuinely used).

This file records the resulting unconditional-in-`CyclicHerbrandQuotient` forms of the boundary
theorems.
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

/-- **The Hasse norm theorem from the second inequality alone.**  The index form of the Hasse norm
theorem now follows from the (proved) Herbrand-quotient computation together with the second
inequality; the remaining hypothesis is the licensed local–global principle
`NK.GlobalCFTdeep.HasseNormPrinciple`. -/
theorem hasseNormTheorem_of_secondInequality (h2 : SecondInequality) (h : HasseNormPrinciple) :
    NK.HassePrinciple.HasseNormTheorem.{0} :=
  hasseNormTheorem_of_inputs cyclicHerbrandQuotient h2 h

/-- **The index of the norm subgroup is the degree, from the second inequality alone.**  For a
cyclic extension `L/K` (indeed any commutative `Gal(L/K)`), `[C_K : N_{L/K}C_L] = [L : K]`. -/
theorem index_eq_of_secondInequality {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] (h2 : SecondInequality) :
    (Idele.normClassSubgroup K L).index = Module.finrank K L :=
  index_eq_finrank_of_secondInequality (cyclicHerbrandQuotient.herbrand (K := K) (L := L)) h2

/-- **The field axiom from the second inequality alone.** -/
theorem fieldAxiom_of_secondInequality' {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] (h2 : SecondInequality) :
    FieldAxiom K L :=
  fieldAxiom_of_secondInequality (cyclicHerbrandQuotient.herbrand (K := K) (L := L)) h2

/-- **The class-formation axioms from the second inequality and Milne's reduction 5.3–5.4.** -/
theorem cohomologicalFieldAxiom_of_secondInequality {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hred : CyclicPrimeReduction) (h2 : SecondInequality) :
    CohomologicalFieldAxiom K L :=
  cohomologicalFieldAxiom_of_inputs hred
    (fun {_ _} _ _ _ _ _ _ _ _ _ => cyclicHerbrandQuotient.herbrand) h2

end NK.GlobalCFTdeep
