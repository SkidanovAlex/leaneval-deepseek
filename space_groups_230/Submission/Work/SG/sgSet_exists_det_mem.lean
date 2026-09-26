import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.AffCoord
import Submission.Work.SG.matOf_affCoord

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- Every matrix `A` of an integral point group `P` is the linear part of an element of the
lattice-normalised space group `sgSet P τ`: the map `x ↦ A x + τ A` lies in `sgSet P τ` and has
linear determinant `A.det`. -/
theorem sgSet_exists_det_mem {P : Set IMat} (hP : IsIntPointGroup P) {τ : IMat → Fin 3 → ℝ}
    {A : IMat} (hA : A ∈ P) : ∃ g ∈ sgSet P τ, (g.linear.det : ℝ) = (A.det : ℝ) := by
  refine ⟨affOfInt A (hP.2.2.2 A hA) (τ A + intVec 0), affOfInt_mem_sgSet hP hA 0, ?_⟩
  rw [← matOf_aux_det]
  show ((matOf (affOfMat (matR A) (isUnit_matR_det (hP.2.2.2 A hA)) (τ A + intVec 0))).det : ℝ)
      = (A.det : ℝ)
  rw [matOf_aux_affOfMat, matR_eq_mapCast]
  exact (Int.cast_det A).symm

end Work.SG
