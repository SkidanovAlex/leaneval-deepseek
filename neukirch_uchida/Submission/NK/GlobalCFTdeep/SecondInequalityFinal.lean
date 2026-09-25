/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.secondInequality_unconditional
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFTdeep.CoCore.FundamentalClass

/-!
# The second inequality, unconditionally: consequences and cross-checks

`NK.GlobalCFTdeep.secondInequality_unconditional` proves the second inequality

  `[C_K : N_{L/K} C_L] ≤ [L : K]`

for **every** finite Galois extension of number fields, with no analytic input at all (the cyclic
prime-degree case `SecondInequality.secondInequality_of_isCyclic_prime`, the cyclic/solvable case
`index_le_finrank_of_isSolvable`, and the Sylow/`p`-primary reduction of Milne 5.3 on top of the
finiteness of the norm index `normClassSubgroup_index_ne_zero`).  This file records the
consequences, which are now unconditional as well, and cross-checks them against the analytic route
(`SecondInequality/secondInequality_of_heckeRegularity`, whose `HeckeRegularity` input is thereby
*removed from the critical path*).

## Main results

* `NK.GlobalCFTdeep.cyclicPrimeAxioms` — the class-formation axioms at cyclic prime-degree levels
  (Milne 5.2), unconditionally;
* `NK.GlobalCFTdeep.hasseNormTheorem_of_second_inequality` — Hasse's norm theorem, re-derived
  from the second inequality (cross-check of `HasseNormTheorem.hasseNormTheorem`);
* `NK.GlobalCFTdeep.cyclicHasseInput_of_second_inequality` — the same for the licensed cyclic
  input of the `HassePrinciple` chapter.
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

/-- **The class-formation axioms at cyclic levels of prime degree** (Milne, *CFT*, Lemma 5.2),
unconditionally: for cyclic `L/K` of prime degree, `H¹(H, C_L) = 0`, `|H²(H, C_L)| = |H|` for every
`H ≤ Gal(L/K)`, and a fundamental class of order `[L:K]`. -/
theorem cyclicPrimeAxioms : CyclicPrimeAxioms :=
  cyclicPrimeAxioms_of_herbrandAndSecondInequality
    (fun {_ _} _ _ _ _ _ _ _ _ _ => cyclicHerbrandQuotient.herbrand)
    secondInequality_unconditional

/-- **Hasse's norm theorem, re-derived from the second inequality** (the route of
`Corollaries/HasseNorm.lean` with both its inputs discharged: the second inequality is now a
theorem, and the local–global principle is `HasseNormTheorem.hasseNormPrinciple`). -/
theorem hasseNormTheorem_of_second_inequality : NK.HassePrinciple.HasseNormTheorem.{0} :=
  hasseNormTheorem_of_inputs cyclicHerbrandQuotient secondInequality_unconditional
    hasseNormPrinciple

/-- **The licensed cyclic input of the `HassePrinciple` chapter, re-derived from the second
inequality.** -/
theorem cyclicHasseInput_of_second_inequality : NK.HassePrinciple.CyclicHasseInput :=
  cyclicHasseInput_of_inputs cyclicHerbrandQuotient secondInequality_unconditional hasseNormPrinciple

end NK.GlobalCFTdeep
