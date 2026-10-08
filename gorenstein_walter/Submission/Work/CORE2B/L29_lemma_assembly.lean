import Submission.Work.CORE2B.Deliverable
import Submission.Work.CORE2B.L29_contra_proved

/-!
# AREA CORE2B — the contract `Lemma29Prop`

The colleague who proved `L29_contra_proved : Work.CORE2B.L29_contra` (Bender 1981, Lemma 2.9 in
its printed form, `L29Hyp` only) also derived the disjunction
`L29_two_core_or_layer_of_contra_proved : L29_two_core_or_layer` from it and from
`Deliverable.l29_two_core_or_layer_of_contra`.  Feeding that into `lemma29_of_leaves` gives the
contract statement.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

/-- **Bender Lemma 2.9 = the contract `Work.GW2.Lemma29Prop`**, complete: the only input is the
toolkit. -/
theorem lemma29 (T : Work.GW2.LocalToolkit) : Work.GW2.Lemma29Prop :=
  lemma29_of_leaves T (L29_two_core_or_layer_of_contra_proved T)

end Work.CORE2B
