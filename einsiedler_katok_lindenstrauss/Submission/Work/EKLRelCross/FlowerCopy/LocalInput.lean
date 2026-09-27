import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.W.W_flower_local

/-!
# `Work.EKLRelCross.FlowerCopy.LocalInput`

`Work.EKLRelCross.LocalFlowerInput U` from the local flower `W.W_flower_local`.

The files in this directory are copies of `flower.lean`, `exists_shrink_nhds.lean`,
`atom_flower_local.lean`, `flower_plaqueAlgebra_bdd.lean` and `W/W_flower_local.lean` in which the
three declarations `isCompact_entryBox`, `isClosed_Ucl`, `isCompact_Ucl` are renamed
(`isCompact_entryBoxC`, `isClosed_UclC`, `isCompact_UclC`).  Those three names are also declared in
`Submission.Work.EKLRelCross.LeafMeasDefs`, and Lean refuses to import two modules declaring the
same constant; the renaming makes the two branches of the C5 development importable together.
-/

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.EKLRelCross

/-- **The local flower input** (Pisa 6.7 + 6.9–6.15). -/
theorem localFlowerInput_of (h2 : Work.EKLContract.P_X3) {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U) : LocalFlowerInput U := by
  intro x₀ hfree R hR
  exact Work.EKLRelCross.W.W_flower_local h2 hU x₀ hfree R hR

end Work.EKLRelCross
