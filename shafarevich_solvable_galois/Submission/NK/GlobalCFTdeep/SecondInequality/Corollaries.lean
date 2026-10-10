import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Corollaries.Unconditional
import Submission.NK.GlobalCFTdeep.SecondInequality.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The boundary theorems with the second inequality discharged

`secondInequality_of_heckeRegularity` proves the second inequality
`[C_K : N_{L/K}C_L] ≤ [L : K]` for every finite Galois extension of number fields from the single
named analytic input `HeckeRegularity` (Hecke's theorem).  Together with the first inequality
(Milne's Theorem 4.3, proved unconditionally in `Herbrand/CyclicHerbrandQuotient.lean`) this
determines the index of the norm subgroup for cyclic extensions:

  `[C_K : N_{L/K}C_L] = [L : K]`.

This file records the resulting forms of the boundary theorems, in which the chapter's former
input `SecondInequality` is gone.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- **Milne's Theorem 4.3 reassembled**: from Hecke's regularity input the universal cyclic
Herbrand-quotient computation and the second inequality both hold, so the index of the norm
subgroup is the degree for every finite cyclic extension of number fields. -/
theorem index_eq_of_heckeRegularity (hH : HeckeRegularity) {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    (Idele.normClassSubgroup K L).index = Module.finrank K L :=
  NK.GlobalCFTdeep.index_eq_of_secondInequality (secondInequality_of_heckeRegularity hH)

/-- **The field axiom of the class formation for cyclic extensions**, from Hecke's regularity. -/
theorem fieldAxiom_of_heckeRegularity (hH : HeckeRegularity) {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    FieldAxiom K L :=
  NK.GlobalCFTdeep.fieldAxiom_of_secondInequality' (secondInequality_of_heckeRegularity hH)

/-- **Hasse's norm theorem from Hecke's regularity alone**: the index form of
`NK.HassePrinciple.HasseNormTheorem` now follows from the analytic input together with the
licensed local–global principle `HasseNormPrinciple`. -/
theorem hasseNormTheorem_of_heckeRegularity (hH : HeckeRegularity)
    (h : NK.GlobalCFTdeep.HasseNormPrinciple) :
    NK.HassePrinciple.HasseNormTheorem.{0} :=
  NK.GlobalCFTdeep.hasseNormTheorem_of_secondInequality (secondInequality_of_heckeRegularity hH) h

/-- **The class-formation axioms at every cyclic level of prime degree**, from Hecke's regularity
and the (proved) Herbrand-quotient computation — no further input. -/
theorem cyclicPrimeAxioms_of_heckeRegularity (hH : HeckeRegularity) :
    NK.GlobalCFTdeep.CyclicPrimeAxioms :=
  NK.GlobalCFTdeep.cyclicPrimeAxioms_of_herbrandAndSecondInequality
    (fun {_ _} _ _ _ _ _ _ _ _ _ => NK.GlobalCFTdeep.cyclicHerbrandQuotient.herbrand)
    (secondInequality_of_heckeRegularity hH)

/-- **The class-formation axioms for every finite Galois extension of number fields**, from Hecke's
regularity and Milne's reduction 5.3–5.4. -/
theorem cohomologicalFieldAxiom_of_heckeRegularity (hH : HeckeRegularity)
    (hred : NK.GlobalCFTdeep.CyclicPrimeReduction) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    CohomologicalFieldAxiom K L :=
  NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_secondInequality hred
    (secondInequality_of_heckeRegularity hH)

end NK.GlobalCFTdeep.SecondInequality
