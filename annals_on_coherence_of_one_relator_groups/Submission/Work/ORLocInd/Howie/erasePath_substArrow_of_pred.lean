import Mathlib
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.TietzeSupport

namespace Work.ORLocInd.Howie

theorem erasePath_substArrow_of_pred {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {P : Work.ORLocInd.Howie.Presentation V} (D : Work.ORLocInd.Howie.TietzeData P)
    {e : Quiver.Total V} (h : D.K.pred e) :
    Work.ORLocInd.Howie.DelV.erasePath D.K e.left (D.substArrow e) = Quiver.Hom.toPath e.hom := by
  -- An arrow kept by the transformation never carries the code of the deleted arrow pair, hence it
  -- is neither `g` nor `g⁻¹`; the substitution fixes it and erasure returns the single arrow.
  have hcode : P.edgeOf e ≠ P.edgeOf D.f := (D.hK e).mp h
  have he : e ≠ D.g := fun hg => hcode (by rw [hg, D.code])
  have he' : e ≠ Quiver.totalReverse D.g := fun hg =>
    hcode (by rw [hg, P.edgeOf_reverse D.g, D.code])
  rw [D.substArrow_of_ne he he']
  rfl

end Work.ORLocInd.Howie
