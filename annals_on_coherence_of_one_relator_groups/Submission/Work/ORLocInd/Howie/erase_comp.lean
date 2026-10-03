import Mathlib
import Submission.Work.ORLocInd.Howie.Span

universe u

namespace Work.ORLocInd.Howie

theorem erase_comp {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {u w x : Work.ORLocInd.Howie.SpanVertex D}
    (p : Quiver.Path u w) (q : Quiver.Path w x) :
    Work.ORLocInd.Howie.erase D u (p.comp q) =
      (Work.ORLocInd.Howie.erase D u p).comp (Work.ORLocInd.Howie.erase D w q) := by
  induction q with
  | nil => simp [Work.ORLocInd.Howie.erase_nil]
  | cons q e ih =>
    rw [Quiver.Path.comp_cons, Work.ORLocInd.Howie.erase_cons, Work.ORLocInd.Howie.erase_cons,
      ih, Quiver.Path.comp_cons]

end Work.ORLocInd.Howie
