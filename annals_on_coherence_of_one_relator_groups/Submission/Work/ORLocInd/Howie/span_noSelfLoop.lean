import Mathlib
import Submission.Work.ORLocInd.Howie.Span

universe u

namespace Work.ORLocInd.Howie

/-- If a quiver has no self-loop which is fixed by the reversal, then no arrow of `Quiver.Total V`
is equal to its own total reverse.  Indeed, if `totalReverse e = e` then (looking at the left
endpoints) the endpoints of `e` coincide, and the underlying arrow of `e` is then a self-loop whose
reverse is itself. -/
theorem totalReverse_ne_self {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hV : ∀ (v : V) (e : v ⟶ v), Quiver.reverse e ≠ e) (e : Quiver.Total V) :
    Quiver.totalReverse e ≠ e := by
  intro h
  obtain ⟨a, b, g⟩ := e
  have hleft : b = a := by simpa using congrArg Quiver.Total.left h
  subst b
  exact hV a g (by simpa using h)

/-- The graph spanned by a datum has no self-inverse loop: the arrows of the span are arrows of the
ambient graph (together with their reverses), and the ambient presentation has no self-loop which
is its own reverse. -/
theorem span_noSelfLoop {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) (u : Work.ORLocInd.Howie.SpanVertex D)
    (f : u ⟶ u) : Quiver.reverse f ≠ f := by
  intro h
  exact totalReverse_ne_self P.noSelfLoop f.1 (congrArg (fun x => x.1) h)

end Work.ORLocInd.Howie
