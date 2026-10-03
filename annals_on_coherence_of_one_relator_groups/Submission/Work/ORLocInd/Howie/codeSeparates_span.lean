import Mathlib
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.exists_spanDatum

universe u

namespace Work.ORLocInd.Howie

/-- `CodeSeparates` is inherited by the sub-presentation spanned by a datum: the arrows of the
span are (subtypes of) arrows of the ambient graph and `spanEdgeOf D f = P.edgeOf f.hom.1`.  This
is what lets Howie's Case 2 be applied to the span inside `datum_vanishes_spanned`. -/
theorem codeSeparates_span {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] {P : Work.ORLocInd.Howie.Presentation V} (hsep : P.CodeSeparates)
    {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n) :
    (Work.ORLocInd.Howie.spanPresentation D).CodeSeparates := by
  rw [Work.ORLocInd.Howie.Presentation.CodeSeparates] at hsep ⊢
  intro e f h
  rcases hsep e.hom.1 f.hom.1 h with h1 | h1
  · exact Or.inl (Work.ORLocInd.Howie.spanTotal_ext h1)
  · refine Or.inr (Work.ORLocInd.Howie.spanTotal_ext ?_)
    rw [show (Quiver.totalReverse f).hom.1 = Quiver.totalReverse f.hom.1 from rfl]
    exact h1

end Work.ORLocInd.Howie
