/-
# The Dirichlet determinant is the continuant (`AJ §9`)

`dirMat α lam θ E n` is the restriction of `H - E` to `n` consecutive sites with zero
boundary conditions, and `pd α lam θ E` is the continuant of `E - H`:
`pd 0 = 0`, `pd 1 = 1`, `pd (k+2) = (E - v_k) * pd (k+1) - pd k` with `v_k = amoPot α lam θ k`.

This file proves `dirMat_det`:  `det (dirMat α lam θ E n) = (-1)^n * pd α lam θ E (n+1)`,
i.e. `pd (n+1) = P_n(θ) = det (E - H)|_{[0,n-1]}` in the notation of AJ §9.

The argument is the classical tridiagonal (continuant) recurrence: expanding the determinant
of `triDiag d (n+2)` along its last row gives
`D_{n+2} = d (n+1) * D_{n+1} - D_n`, which is exactly the recurrence defining `pd`, so the
identity follows by two-step induction.  The determinant recurrence and its supporting
matrix identities live in `Submission.Work.TMC16Core.Basic.triDiag`.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.triDiag

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-- `det (dirMat α lam θ E n) = (-1)^n * P_n(θ)` where `P_n` is the continuant `pd (n+1)` of
`E - H` on `n` consecutive sites with Dirichlet boundary conditions. -/
theorem dirMat_det (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) :
    (Work.TMC16Core.dirMat α lam θ E n).det = (-1) ^ n * Work.TMC16Core.pd α lam θ E (n + 1) := by
  have h : ∀ n : ℕ,
      (triDiag (fun k : ℕ => ((amoPot α lam θ (k : ℤ) : ℝ) : ℂ) - E) n).det =
        (-1) ^ n * pd α lam θ E (n + 1) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [pd]
    | one =>
      simp only [Matrix.det_fin_one]
      rw [triDiag]
      simp [pd]
    | more m ih1 ih2 =>
      rw [triDiag_det_recur, ih1, ih2]
      have hpd : pd α lam θ E (m + 3) =
          (E - ((amoPot α lam θ ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ)) * pd α lam θ E (m + 2)
            - pd α lam θ E (m + 1) := by
        rw [show m + 3 = (m + 1) + 2 by ring]
        rfl
      rw [hpd]
      have hs1 : (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by
        rw [pow_add]; ring
      have hs2 : (-1 : ℂ) ^ (m + 1) = -(-1 : ℂ) ^ m := by
        rw [pow_succ]; ring
      rw [hs1, hs2]
      ring
  rw [dirMat_eq_triDiag]
  exact h n

end Work.TMC16Core.Basic
