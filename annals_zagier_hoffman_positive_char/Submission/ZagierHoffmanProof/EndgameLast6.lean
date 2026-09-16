import Submission.ZagierHoffmanProof.EndgameLast5

/-!
# SESSION 363 — the last case `w = 2q-2`: item (i), `N·D = D₂·P·(P - 2Λ)`

`PLAN.md` §«SESSION 362» §7 item 1.  From `num = D₂·Λ²` (`Λ = L^q = X^q - C(θ^q)`,
`L = X - Cθ`) and the integral σ-recursion `σ num = W^w·(num + N·D)` (`W = σ L = X - C(θ^q)`,
`σ` = the coefficientwise `q`-th power) one cancels `W^{2q-2}` and gets

  `D₂·W² = D₂·Λ² + N·D`,   i.e.   **`N·D = D₂·(W² - Λ²) = D₂·P·(P - 2Λ)`**

with `P = X^q - X` (the elementary identity `W² - Λ² = (W-Λ)(W+Λ) = (-P)·(-(P-2Λ))`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★★ **`σ num = D₂·W^{2q}`** for `num = D₂·L^{2q}` with `D₂` Frobenius-fixed. -/
theorem polyTwist_num_eq {num D2 : Polynomial (Ambient F)} (hD2 : ∀ n, D2.coeff n ∈ ambF F)
    (hnum : num = D2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ (2 * Nat.card F)) :
    polyTwist (q := Nat.card F) 1 num
      = D2 * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (2 * Nat.card F) := by
  rw [hnum, polyTwist_mul, polyTwist_pow, polyTwist_one_fixed F D2 hD2,
    polyTwist_X_sub_C_theta]

/-- ★★★★★ **Item (i)** (`PLAN.md` §«SESSION 362» §7.1): `N·D = D₂·P·(P - 2Λ)`. -/
theorem ND_eq {w : ℕ} {num N D D2 : Polynomial (Ambient F)}
    (hw : w = 2 * Nat.card F - 2)
    (hrec : polyTwist (q := Nat.card F) 1 num
      = (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * (num + N * D))
    (hD2 : ∀ n, D2.coeff n ∈ ambF F)
    (hnum : num = D2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ (2 * Nat.card F)) :
    N * D = D2 * ((Polynomial.X ^ Nat.card F - Polynomial.X)
        * ((Polynomial.X ^ Nat.card F - Polynomial.X)
          - 2 * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)))) := by
  set W : Polynomial (Ambient F) := Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) with hWs
  have hW0 : W ≠ 0 := by rw [hWs]; exact Polynomial.X_sub_C_ne_zero _
  have hσnum : polyTwist (q := Nat.card F) 1 num = D2 * W ^ (2 * Nat.card F) := by
    rw [polyTwist_num_eq F hD2 hnum, hWs]
  have hmain : D2 * W ^ (2 * Nat.card F) = W ^ w * (num + N * D) := hσnum.symm.trans hrec
  rw [hw] at hmain
  rw [show W ^ (2 * Nat.card F) = W ^ (2 * Nat.card F - 2) * W ^ 2 from by
    rw [← pow_add]; congr 1
    have := two_le_ambCard F; omega] at hmain
  have hcancel : D2 * W ^ 2 = num + N * D := by
    have hmul : W ^ (2 * Nat.card F - 2) * (D2 * W ^ 2)
        = W ^ (2 * Nat.card F - 2) * (num + N * D) := by
      have h1 : W ^ (2 * Nat.card F - 2) * (D2 * W ^ 2)
          = D2 * (W ^ (2 * Nat.card F - 2) * W ^ 2) := by ring
      rw [h1, hmain]
    exact mul_left_cancel₀ (pow_ne_zero _ hW0) hmul
  have hnumΛ : num = D2 * (Polynomial.X ^ Nat.card F
      - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ 2 := by
    rw [hnum, show 2 * Nat.card F = Nat.card F * 2 from by ring, pow_mul,
      X_sub_C_pow_card F (ambTheta F)]
  have hkey : N * D = D2 * (W ^ 2 - (Polynomial.X ^ Nat.card F
      - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ 2) := by
    rw [show N * D = D2 * W ^ 2 - num from by rw [hcancel]; ring, hnumΛ, mul_sub]
  rw [hkey, hWs]
  exact congrArg (fun x => D2 * x) (by
    ring : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ 2
        - (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ 2
      = (Polynomial.X ^ Nat.card F - Polynomial.X)
        * ((Polynomial.X ^ Nat.card F - Polynomial.X)
          - 2 * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))))

end ZagierHoffmanPositiveChar
