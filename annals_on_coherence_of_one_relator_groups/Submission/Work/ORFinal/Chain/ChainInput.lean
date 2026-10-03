/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The dimension-shifting chain of JL Lemma 5.2, as an input of the T7 assembly

`Work.ORFinal.Chain.chainOfJL52` (T6) proves the dimension-shifting equivalence of JL Lemma 5.2 in
the `Work.ORFP2.augIdeal` form, for every `K`-algebra `S` with structure map `φ : K[G] →ₐ[K] S`;
`Work.ORFinal.Chain.chainHyp_of_augIdeal` transfers it to the `Work.ORLyndon.augIdeal` form, which
is the one consumed by `Work.ORLyndon.magnus_torTwoVanishes`.

This file collects the two forms into the named inputs of `Submission/Work/ORFinal/ChainDefs.lean`:

* `Work.ORFinal.chainInputFP2 : Work.ORFinal.ChainInputFP2`
* `Work.ORFinal.chainInput : Work.ORFinal.ChainInput` — the input of the T7 assembly
  `Work.ORFinal.T7.realTorInput_of_chainInput`.
-/
import Submission.Work.ORFinal.Chain.chainOfJL52
import Submission.Work.ORFinal.Chain.chainHyp_of_augIdeal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ORFinal

/-- **JL Lemma 5.2's dimension-shifting chain as a theorem**, in the `Work.ORFP2.augIdeal` form:
`Work.ORFinal.Chain.chainOfJL52` (T6), packaged as `Work.ORFinal.ChainInputFP2`. -/
theorem chainInputFP2 : ChainInputFP2 := by
  intro K _ G _ S _ _ φ
  unfold ChainHypFP2
  letI := Work.ORFlatness.diagRightModule K G S φ ↥(Work.ORFP2.augIdeal K G)
  intro M
  exact Work.ORFinal.Chain.chainOfJL52 K G S φ rfl M

/-- **JL Lemma 5.2's dimension-shifting chain as a theorem**, in the `Work.ORLyndon.augIdeal` form
consumed by `Work.ORLyndon.magnus_torTwoVanishes` — the remaining input of the T7 assembly. -/
theorem chainInput : ChainInput :=
  fun K _ G _ S _ _ φ =>
    Work.ORFinal.Chain.chainHyp_of_augIdeal K G S φ (chainInputFP2 K G S φ)

end Work.ORFinal
