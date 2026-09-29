import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Defs

namespace Work.TMC7Core.Solutions

open Work.TMC7Core

/-- `iterC` is invariant under integer translations of the base point (period `1`). -/
theorem iterC_periodic_int (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) (m : ℤ) :
    iterC α lam E n (x + (m : ℝ)) = iterC α lam E n x := by
  have h : Function.Periodic (fun y : ℝ => iterC α lam E n y) (1 : ℝ) :=
    fun y => iterC_periodic α lam E n y
  simpa using (h.zsmul m) x

theorem iterC_qpow (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (k : ℕ) (x : ℝ) :
    Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (q * k) x
      = (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x) ^ k := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt this
  have hα : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
    field_simp
  induction k with
  | zero => simp [iterC_zero]
  | succ k ih =>
    rw [Nat.mul_succ, iterC_add, hα,
      iterC_periodic_int ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (q * k) x p, ih, pow_succ]

end Work.TMC7Core.Solutions
