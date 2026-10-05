import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

theorem laurentPoly_exp (N : ℕ) (a : ℤ → ℂ) (t : ℝ) :
    laurentPoly N a (Complex.exp (t * I)) = trigPoly N a t := by
  unfold laurentPoly trigPoly
  refine Finset.sum_congr rfl ?_
  intro n _
  congr 1
  rw [← Complex.exp_int_mul (t * I) n]
  congr 1
  ring

end Work.RPB1a
