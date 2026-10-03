import Mathlib
import Submission.Work.ORLocInd.Howie.Span
import Submission.Work.ORLocInd.Howie.erase_pmul

universe u

namespace Work.ORLocInd.Howie

/-- Erasure of paths of the span commutes with taking powers of a closed path.

This is the `compPower` analogue of `erase_path_comp`
(`Submission.Work.ORLocInd.Howie.erase_pmul`) and follows from it by induction on the exponent. -/
theorem erase_compPower {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {u : Work.ORLocInd.Howie.SpanVertex D}
    (p : Quiver.Path u u) (m : ℕ) :
    Work.ORLocInd.Howie.erase D u (Quiver.Path.compPower p m) =
      Quiver.Path.compPower (Work.ORLocInd.Howie.erase D u p) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Quiver.Path.compPower_succ, Quiver.Path.compPower_succ,
        Work.ORLocInd.Howie.erase_path_comp, ih]

end Work.ORLocInd.Howie
