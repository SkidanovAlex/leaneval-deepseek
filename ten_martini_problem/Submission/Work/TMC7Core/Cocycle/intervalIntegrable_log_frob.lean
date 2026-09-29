import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

/-!
# Interval integrability of `x ↦ log ‖A_n(x)‖_F`

`A_n = iterC α lam E n` is continuous in `x` (`continuous_iterC`), and for every `n`, `x`
the determinant of `A_n(x)` is `1` (`det_iterC`); a determinant-one `2×2` matrix has
Frobenius norm at least `√2` (`frob_sqrt_two_le_of_det_one`). Hence
`x ↦ frob (iterC α lam E n x)` is continuous and everywhere positive, so its logarithm is
continuous on the compact interval `[0,1]` and therefore interval integrable.
-/

open MeasureTheory
open Work.TMC7Core

namespace Work.TMC7Core.Cocycle

theorem intervalIntegrable_log_frob (α lam : ℝ) (E : ℂ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α lam E n x))) volume (0 : ℝ) 1 := by
  -- Continuity of the Frobenius norm as a function of the matrix.
  have hfrob : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) := by
    have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A)
        = fun A => Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) :=
      rfl
    rw [h]
    have e : ∀ i j : Fin 2, Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) :=
      fun i j => (continuous_apply j).comp (continuous_apply i)
    refine Real.continuous_sqrt.comp ?_
    exact ((((e 0 0).norm.pow 2).add ((e 0 1).norm.pow 2)).add ((e 1 0).norm.pow 2)).add
      ((e 1 1).norm.pow 2)
  -- `x ↦ frob (iterC α lam E n x)` is continuous and everywhere positive.
  apply Continuous.intervalIntegrable
  refine Continuous.log (hfrob.comp (continuous_iterC α lam E n)) ?_
  intro x
  have hle : Real.sqrt 2 ≤ frob (iterC α lam E n x) :=
    frob_sqrt_two_le_of_det_one (det_iterC α lam E n x)
  have hlt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact ne_of_gt (lt_of_lt_of_le hlt hle)

end Work.TMC7Core.Cocycle
