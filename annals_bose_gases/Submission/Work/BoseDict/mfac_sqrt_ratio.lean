import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseB4.Cre_ann_adjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseDict

open Work.BoseB4

/-- `√((d+1)!) = √(d!) · √(d+1)`, from `(d+1)! = d! · (d+1)`. -/
private lemma sqrt_factorial_succ (d : ℕ) :
    Real.sqrt (((d + 1).factorial : ℝ))
      = Real.sqrt ((d.factorial : ℝ)) * Real.sqrt ((d : ℝ) + 1) := by
  rw [← Real.sqrt_mul (x := (d.factorial : ℝ)) (by positivity) ((d : ℝ) + 1)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- Division bookkeeping in a field: `x·y/(b·f) = (y/b)·x/f`. -/
private lemma div_mul_div_eq (x y b f : ℝ) : x * y / (b * f) = (y / b) * x / f := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem mfac_sqrt_ratio {m d : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    Work.BoseB4.mfac (α + Work.BoseB4.e m l) / Real.sqrt (((d + 1).factorial : ℝ))
      = (Work.BoseB4.mfac α / Real.sqrt ((d.factorial : ℝ))) * ((α l : ℝ) + 1)
          / Real.sqrt ((d : ℝ) + 1) := by
  rw [mfac_add_e l α, sqrt_factorial_succ d, div_mul_div_eq]

end Work.BoseDict
