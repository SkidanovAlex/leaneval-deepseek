import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Solutions

open Work.TMC7Core

/-- **One step of the transfer cocycle on the solution vector.**
If `u` is a formal solution of the almost Mathieu difference equation at energy `E`
(`amoAct α lam θ u = E · u`), then the transfer matrix `tmC lam E (θ + k α)` maps the
vector `(u k, u (k-1))` to `(u (k+1), u k)`.  This is the recurrence
`u (k+1) = (E - 2λ cos 2π(θ + kα)) u k - u (k-1)` read as a matrix–vector product. -/
lemma tmC_mulVec_step (α lam θ : ℝ) (E : ℂ) (u : ℤ → ℂ)
    (hu : ∀ n : ℤ, amoAct α lam θ u n = E * u n) (k : ℕ) :
    (tmC lam E (θ + (k : ℝ) * α)).mulVec ![u (k : ℤ), u ((k : ℤ) - 1)] =
      ![u ((k : ℤ) + 1), u (k : ℤ)] := by
  have hv : (amoPot α lam θ (k:ℤ) : ℂ) =
      2 * (lam : ℂ) * Complex.cos (2 * (Real.pi : ℂ) * ((θ : ℂ) + ((k:ℤ) : ℂ) * (α : ℂ))) := by
    rw [amoPot]; push_cast; ring
  have hrec := hu (k:ℤ)
  rw [amoAct, hv] at hrec
  funext i
  fin_cases i <;> simp [Matrix.mulVec, tmC]
  rw [eq_comm]
  linear_combination hrec

/-- The transfer cocycle applied to the initial vector `(u 0, u (-1))` of a formal solution
returns `(u n, u (n-1))`. -/
theorem iterC_mulVec_solution (α lam θ E : ℝ) (u : ℤ → ℂ) (hu : ∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n) (n : ℕ) : (iterC α lam (E : ℂ) n θ).mulVec ![u 0, u (-1)] = ![u (n : ℤ), u ((n : ℤ) - 1)] := by
  induction n with
  | zero => simp [iterC]
  | succ n ih =>
    rw [iterC_succ, ← Matrix.mulVec_mulVec, ih]
    rw [tmC_mulVec_step α lam θ (E : ℂ) u hu n]
    simp [Nat.cast_add, Nat.cast_one]

end Work.TMC7Core.Solutions
