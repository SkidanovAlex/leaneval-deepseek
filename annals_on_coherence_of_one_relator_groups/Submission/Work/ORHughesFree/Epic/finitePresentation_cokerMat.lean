import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory

namespace Work.ORHughesFree.Epic

universe u

theorem finitePresentation_cokerMat {R : Type u} [Ring R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    Module.FinitePresentation R (Work.ORHughesFree.Epic.cokerMat A) := by
  refine Module.finitePresentation_of_free_of_surjective
    (Submodule.mkQ (LinearMap.range (rowMulLin A)))
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range _

end Work.ORHughesFree.Epic
