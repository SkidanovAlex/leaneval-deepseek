import Mathlib
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Scale

/-- The squared norm of a real number embedded in `ℂ` is its square. -/
lemma norm_sq_ofReal (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]; ring

theorem frob_map_ofReal_sq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (Work.TMC7Core.frob (A.map (fun x => (x : ℂ)))) ^ 2
      = A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 := by
  rw [Work.TMC7Core.frob_sq]
  simp only [Matrix.map_apply]
  rw [norm_sq_ofReal, norm_sq_ofReal, norm_sq_ofReal, norm_sq_ofReal]

end Work.TMC7Core.Scale
