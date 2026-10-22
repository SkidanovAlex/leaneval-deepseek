import Mathlib
import Submission.Work.CWTOP.Closed

/-!
# `CWClosed` holds for the empty space

A class `G` of spaces satisfying the closure axioms `CWClosed` contains the empty space
(`CWClosed.empty`) and is invariant under homotopy equivalence (`CWClosed.of_homotopyEquiv`).
Since an empty space `X` is homeomorphic to `PEmpty`, `G X` follows.

Note that `[IsEmpty X]` for a bundled space `X : TopCat` is an emptiness hypothesis on the
underlying type, so the (vacuous) Hausdorffness instances required by
`CWClosed.of_homotopyEquiv` are found by instance search.
-/

open CategoryTheory

namespace Work.CWTOP

theorem g_of_isEmpty (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G)
    (X : TopCat.{0}) [IsEmpty X] : G X := by
  refine hG.of_homotopyEquiv (X := X) (Y := TopCat.of PEmpty) ?_ hG.empty
  refine Homeomorph.toHomotopyEquiv
    { toFun := fun x => isEmptyElim x
      invFun := fun y => isEmptyElim y
      left_inv := fun x => isEmptyElim x
      right_inv := fun y => isEmptyElim y
      continuous_toFun := continuous_iff_continuousAt.2 fun x => isEmptyElim x
      continuous_invFun := continuous_iff_continuousAt.2 fun y => isEmptyElim y }

end Work.CWTOP
