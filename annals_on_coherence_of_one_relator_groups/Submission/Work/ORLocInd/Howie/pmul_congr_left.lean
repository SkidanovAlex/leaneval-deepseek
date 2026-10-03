import Mathlib
import Submission.Work.ORLocInd.Howie.Basic

namespace Work.ORLocInd.Howie

open Quiver

/-- If `A` reduces to `A'`, then multiplying on the right by a fixed path `B` is insensitive to
this reduction: both `A.comp B` and `A'.comp B` reduce to the same reduced form. -/
theorem pmul_congr_left {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {a b c : V} (A A' : Quiver.Path a b) (h : A.ReducesTo A') (B : Quiver.Path b c) :
    Work.ORLocInd.Howie.pmul A B = Work.ORLocInd.Howie.pmul A' B := by
  rw [pmul, pmul]
  exact red_eq_of_reducesTo_isReduced
    ((Quiver.Path.ReducesTo.comp_right h B).trans (comp_reducesTo_pmul A' B))
    (pmul_isReduced A' B)

end Work.ORLocInd.Howie
