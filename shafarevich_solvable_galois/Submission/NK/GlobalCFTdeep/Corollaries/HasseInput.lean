/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Corollaries.HasseNorm
import Submission.NK.HassePrinciple.CyclicBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The licensed cyclic input of the Hasse principle, produced by this chapter

`Submission/Work/HassePrinciple/CyclicBase.lean` defines the licensed input

  `NK.HassePrinciple.CyclicHasseInput = (HasseNormTheorem, ∀ cyclic L/K, HerbrandQuotient K L)`

from which that chapter derives the Hasse–Brauer–Noether transport.  This file *produces* it from
the chapter's two inputs `CyclicHerbrandQuotient` (Milne, *CFT*, Theorem 4.3) and
`SecondInequality` (Takagi's second inequality) together with the licensed local–global principle
`HasseNormPrinciple` — with the index form of the Hasse norm theorem **proved**, not assumed.
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

/-- **The licensed cyclic input of the Hasse principle**, from this chapter's inputs. -/
theorem cyclicHasseInput_of_inputs (hH : CyclicHerbrandQuotient) (h2 : SecondInequality)
    (h : HasseNormPrinciple) : NK.HassePrinciple.CyclicHasseInput where
  hasse_norm := hasseNormTheorem_of_inputs hH h2 h
  herbrand := by
    intro K L _ _ _ _ _ _ _ hcyc
    haveI := hcyc
    exact herbrandQuotient_of_cyclicHerbrandQuotient hH

end NK.GlobalCFTdeep
