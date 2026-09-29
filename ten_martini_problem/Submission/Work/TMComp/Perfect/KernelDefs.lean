import Mathlib
import Submission.Work.TMComp.PerfectDefs

/-!
# Component C2 (`P_Perfect`): auxiliary vocabulary for `kernel_dim_le_one`

This module introduces the two elementary notions used in the proof that the almost
Mathieu operator has at most one-dimensional `ℓ²` eigenspaces at a given real energy.

* `IsRecSol c x` -- `x` solves the second order recurrence `x (n+1) = c n * x n - x (n-1)`
  (this is the eigenvalue equation `H x = E x` written as a recursion, with
  `c n = E - v n`).
* `wronsk c`/`wronsk x y n` -- the Wronskian `x n * y (n+1) - x (n+1) * y n` of two
  solutions; it is constant along the recurrence, which is what forces two `ℓ²` solutions
  to be proportional.
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Perfect

/-- `x` satisfies the Jacobi recursion with coefficient sequence `c`:
`x (n+1) = c n * x n - x (n-1)`, i.e. `x (n+1) + x (n-1) = c n * x n`. -/
def IsRecSol (c : ℤ → ℂ) (x : ℤ → ℂ) : Prop := ∀ n : ℤ, x (n + 1) = c n * x n - x (n - 1)

/-- The Wronskian of two sequences: `x n * y (n+1) - x (n+1) * y n`. -/
def wronsk (x y : ℤ → ℂ) (n : ℤ) : ℂ := x n * y (n + 1) - x (n + 1) * y n

theorem IsRecSol.apply {c x : ℤ → ℂ} (h : IsRecSol c x) (n : ℤ) :
    x (n + 1) = c n * x n - x (n - 1) := h n

/-- Rearranged form of the recursion: `x (n+1) + x (n-1) = c n * x n`. -/
theorem IsRecSol.add_shift {c x : ℤ → ℂ} (h : IsRecSol c x) (n : ℤ) :
    x (n + 1) + x (n - 1) = c n * x n := by
  rw [h n]; ring

end Work.TMComp.Perfect
