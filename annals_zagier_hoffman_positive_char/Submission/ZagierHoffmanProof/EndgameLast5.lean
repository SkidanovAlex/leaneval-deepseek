import Submission.ZagierHoffmanProof.EndgameLast4

/-!
# SESSION 362 — the last case `w = 2q-2`: the arithmetic and `V = D₂·L²`

`PLAN.md` §«SESSION 362».  With `w = 2q-2` one has `w ≡ -2` and `w² - C(w,2) ≡ 1 (mod p)`, so the
two reads `D_one_eq`, `D_zero_eq` give `D_1 = -2X·D_2` and `D_0 = X²·D_2`, hence `V = D_2·L²` and
`num = D_2·Λ²` (`Λ = L^q = X^q - C(θ^q)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma cast_two_card_sub_two : ((2 * Nat.card F - 2 : ℕ) : Ambient F) = -2 := by
  have hq1 : 1 ≤ Nat.card F := by have := two_le_ambCard F; omega
  rw [show 2 * Nat.card F - 2 = 2 * (Nat.card F - 1) from by omega, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub hq1, natCast_card_eq_zero_ambient]
  ring

lemma cast_choose_two_two_card_sub_two (hq : 3 ≤ Nat.card F) :
    (((2 * Nat.card F - 2).choose 2 : ℕ) : Ambient F) = 3 := by
  have hq1 : 1 ≤ Nat.card F := by omega
  have h2 : 1 ≤ 2 * (Nat.card F - 1) := by omega
  rw [show 2 * Nat.card F - 2 = 2 * (Nat.card F - 1) from by omega, Nat.choose_two_right,
    show 2 * (Nat.card F - 1) * (2 * (Nat.card F - 1) - 1) / 2
        = (Nat.card F - 1) * (2 * (Nat.card F - 1) - 1) from by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)],
    Nat.cast_mul, Nat.cast_sub h2, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hq1,
    natCast_card_eq_zero_ambient]
  ring

/-- ★★★★ **The three-term read gives `V = D_2·(X - Cθ)²`.** -/
theorem V_eq_D2_mul_sq {w : ℕ} {V D0 D1 D2 : Polynomial (Ambient F)}
    (hV : V = D0 + D1 * Polynomial.C (ambTheta F) + D2 * Polynomial.C ((ambTheta F) ^ 2))
    (h1 : D1 = Polynomial.C ((w : ℕ) : Ambient F) * (Polynomial.X * D2))
    (h0 : D0 = Polynomial.C ((w : ℕ) : Ambient F) * (Polynomial.X * D1)
      - Polynomial.C (((w.choose 2 : ℕ) : Ambient F)) * (Polynomial.X ^ 2 * D2))
    (hw : ((w : ℕ) : Ambient F) = -2) (hc : (((w.choose 2 : ℕ)) : Ambient F) = 3) :
    V = D2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ 2 := by
  have h0' : D0 = Polynomial.X ^ 2 * D2 := by
    rw [h1] at h0
    have hstep : Polynomial.C ((w : ℕ) : Ambient F)
          * (Polynomial.X * (Polynomial.C ((w : ℕ) : Ambient F) * (Polynomial.X * D2)))
        - Polynomial.C (((w.choose 2 : ℕ) : Ambient F)) * (Polynomial.X ^ 2 * D2)
        = (Polynomial.C ((w : ℕ) : Ambient F) * Polynomial.C ((w : ℕ) : Ambient F)
            - Polynomial.C (((w.choose 2 : ℕ) : Ambient F))) * (Polynomial.X ^ 2 * D2) := by
      ring
    have hunit : Polynomial.C ((w : ℕ) : Ambient F) * Polynomial.C ((w : ℕ) : Ambient F)
        - Polynomial.C (((w.choose 2 : ℕ) : Ambient F)) = 1 := by
      rw [← Polynomial.C_mul, ← Polynomial.C_sub, hw, hc]
      norm_num
    rw [h0, hstep, hunit, one_mul]
  rw [hV, h1, h0', hw, Polynomial.C_pow]
  simp only [Polynomial.C_neg, map_ofNat]
  ring

/-- ★★★★ **`num = D_2·Λ²`** with `Λ = L^q = X^q - C(θ^q)`. -/
theorem num_eq_D2_mul_theta {w : ℕ} {V num D1 D2 : Polynomial (Ambient F)}
    (hprod : num = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V)
    (hVsq : V = D2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ 2)
    (hw : w = 2 * Nat.card F - 2) :
    num = D2 * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ 2 := by
  have hLq : ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F : Polynomial (Ambient F))
      = Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :=
    X_sub_C_pow_card F (ambTheta F)
  rw [hprod, hVsq, ← hLq]
  have hw2 : w + 2 = 2 * Nat.card F := by
    have h2 := two_le_ambCard F
    rw [hw]; omega
  rw [show (Polynomial.X - Polynomial.C (ambTheta F)) ^ w
        * (D2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ 2)
      = D2 * (Polynomial.X - Polynomial.C (ambTheta F)) ^ (w + 2) from by ring,
    hw2, ← pow_mul, Nat.mul_comm]

end ZagierHoffmanPositiveChar
