/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The licensed cyclic input of the Hasse principle

Umbrella development: `Submission/Work/HassePrinciple/` (README §4, §12.3 items (a), (b)).

This module collects the **licensed number-theoretic input** of the chapter — the pair of
classical statements *about cyclic extensions of number fields and their norm groups* from which
the whole Hasse–Brauer–Noether transport is derived:

* `NK.HassePrinciple.CyclicHasseInput.hasse_norm` — the Hasse norm theorem for cyclic extensions
  of number fields, with its index form (the reciprocity isomorphism),
  `NK.HassePrinciple.HasseNormTheorem` (`Norm.lean`);
* `NK.HassePrinciple.CyclicHasseInput.herbrand` — the Herbrand quotient of the idèle class group
  for cyclic extensions, `h(Gal(L/K), C_L) = [L : K]` (Milne, *CFT*, Thm 4.3; on disk as
  `NK.GlobalCFT.HerbrandQuotient`).

Nothing else about norm groups of cyclic extensions is needed: the reduction of the Hasse principle
to these two statements is the classical one, and the steps of it that are formalised in this
chapter are recorded in the README §12.3.
-/

import Submission.NK.HassePrinciple.Norm
import Submission.NK.GlobalCFT.GlobalCFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The licensed cyclic input**: the Hasse norm theorem for cyclic extensions of number fields
(in the index form of the reciprocity isomorphism and in the norm form), together with the Herbrand
quotient of the idèle class group for cyclic extensions.

Both fields are statements about *cyclic* extensions of number fields and their norm groups; they
are the two classical inputs of the Hasse–Brauer–Noether theorem, and this chapter derives the
Hasse principle from them. -/
structure CyclicHasseInput : Prop where
  /-- **The Hasse norm theorem for cyclic extensions of number fields** (`Norm.lean`): the index
  formula `[C_K : N_{L/K} C_L] = [L : K]` and the local–global principle for norms
  `Kˣ ∩ N 𝕀_L = N Lˣ`. -/
  hasse_norm : HasseNormTheorem.{0}
  /-- **The Herbrand quotient of the idèle class group for cyclic extensions**:
  `h(Gal(L/K), C_L) = [L : K]` (Milne, *CFT*, Thm 4.3). -/
  herbrand : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L], IsCyclic (L ≃ₐ[K] L) → HerbrandQuotient K L

end NK.HassePrinciple
