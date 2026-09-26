import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.matOf_affCoord

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- The determinant of an integer matrix, cast to `ℝ`, is the determinant of its real image. -/
theorem matR_det (A : IMat) : (matR A).det = (A.det : ℝ) := by
  rw [matR_eq_mapCast, ← Int.cast_det]

/-- The linear part of an element of a lattice-normalised space group `sgSet P τ` has the
determinant of one of the matrices of `P`. -/
theorem sgSet_det_of_mem {P : Set IMat} {τ : IMat → Fin 3 → ℝ} {g : AffineGroup 3}
    (hg : g ∈ sgSet P τ) : ∃ A ∈ P, (g.linear.det : ℝ) = (A.det : ℝ) := by
  obtain ⟨A, hA, n, hgx⟩ := hg
  refine ⟨A, hA, ?_⟩
  have huniq := matOf_aux_unique g (matR A) (τ A + intVec n) (fun x => by
    rw [hgx x, ← matR_eq_mapCast A, add_assoc])
  rw [← matOf_aux_det g, huniq.1, matR_det]

end Work.SG
