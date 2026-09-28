import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ball_prod_window_r2_arith

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

/-- `2 ^ (2 * m) = (2 ^ m) ^ 2`, used to match the window quantities `2 ^ {2 k_j}`. -/
lemma two_pow_two_mul (m : ℕ) : (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 := by
  rw [Nat.mul_comm 2 m, pow_mul]

/-- The window estimate for `rk L = 2`.  Both ball-count bounds `hsmall2` (at `X`) and `hsmallY`
(at `Y`) are multiplied together, and the arithmetic core `ball_prod_window_r2_arith` (with
`a = lam L 1`, `b = lam L 2`, `p = 2 ^ {k 0}`, `q = 2 ^ {k 1}`) clears the `2 ^ {k_j}`
denominators using `hk2 : 2 ^ {k j} ≤ 2 * lam L (j+1)`. -/
theorem ball_prod_window_r2 (n : ℕ) (hn : 2 ≤ n)
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hsmall2 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X →
      (ballCount L X : ℝ) ≤ Ksmall * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1))
    (hsmallY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ Ksmall * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)))
    (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrL : rk L = 2) (k : Fin 2 → ℕ)
    (hk2 : ∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1))
    (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X ≤ Y) (hlX : lam L 1 ≤ X) (hlY : lam L 2 ≤ Y) :
    (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
      Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
        + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
        + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))) := by
  have hrk : 2 ≤ rk L := by omega
  have hlam1 : 0 < lam L 1 := lam_pos L le_rfl (le_trans (by norm_num) hrk)
  have hlam2 : 0 < lam L 2 := lam_pos L (by norm_num) hrk
  -- the two ball-count bounds
  have hXb : (ballCount L X : ℝ) ≤
      Ksmall * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) := hsmall2 L X hrL hX
  have hYb : (ballCount L Y : ℝ) ≤ Ksmall * Y ^ 2 / (lam L 1 * lam L 2) := by
    have h := hsmallY L Y hY hrk hlY
    rw [hrL] at h
    simpa using h
  have hbndnn : (0 : ℝ) ≤
      Ksmall * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) :=
    le_trans (Nat.cast_nonneg _) hXb
  refine (mul_le_mul hXb hYb (Nat.cast_nonneg _) hbndnn).trans ?_
  -- match `2 ^ {2 k_j} = (2 ^ {k_j}) ^ 2` and apply the arithmetic core
  rw [two_pow_two_mul (k 0), two_pow_two_mul (k 1)]
  exact ball_prod_window_r2_arith (lam L 1) (lam L 2) Ksmall X Y
    ((2 : ℝ) ^ (k 0)) ((2 : ℝ) ^ (k 1)) hKsmall hlam1 hlam2 (by positivity)
    (by simpa using hk2 ⟨0, by norm_num⟩) (by positivity)
    (by simpa using hk2 ⟨1, by norm_num⟩) hX hY

end Work.HP
