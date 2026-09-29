import Mathlib
import Submission.Work.Recursion.defs

/-!
# The transform estimate of the recursion inequality

`Est1 n` is the first half of the cost recursion of Corollary 5.5 (paper §5.3): after cancelling
the constant `C` of `CmOf C m = C * (m * size m + 1)`, the transform term
`12 * (T/r) * (C * (3 r p * size (3 r p) + 1))` of `mainCost` is at most
`(1 - 1/(2d)) * n * size n`.

Everything is elementary real arithmetic: the hypotheses `Est1Hyp n` provide the estimates on
the concrete functions `bpar, ppar, kTpar, Tpar, rpar` (their arithmetic content is established
elsewhere, in `Work.Recursion.params`), and the present lemma only has to combine them.
-/

set_option autoImplicit false

namespace Work.Recursion

open HvdH

noncomputable section

/-- `d = 1729`, concretely. -/
private lemma rD_eq : rD = 1729 := by norm_num [rD, HvdH.D]

/-- `p = 6b`. -/
private lemma rP_eq (n : ℕ) : rP n = 6 * rB n := by
  simp only [rP, rB, HvdH.ppar]
  push_cast
  ring

/-- The constant `1 - 1/(2d)` is nonnegative. -/
private lemma one_sub_nonneg : (0 : ℝ) ≤ 1 - 1 / (2 * rD) := by
  rw [rD_eq]; norm_num

/-- Pure real arithmetic behind `Est1`: the estimates
`T·b ≤ 8n`, `p = 6b`, `size (3rp) ≤ A`, `b ≥ 1`, `r ≥ 1`, `log₂ n ≤ size n` and the key
inequality `1728A + 96 ≤ (1 - 1/(2d)) log₂ n` combine to give the claim. -/
private lemma arith_est1 (n T R P B s A L S : ℝ)
    (hn : 0 ≤ n) (hT : 0 ≤ T) (hR1 : 1 ≤ R) (hB1 : 1 ≤ B)
    (hTb : T * B ≤ 8 * n) (hP : P = 6 * B) (hs : s ≤ A) (hA : 0 ≤ A)
    (hLS : L ≤ S) (hkey : 1728 * A + 96 ≤ (1 - 1 / (2 * rD)) * L) :
    12 * (T / R) * ((3 * R * P) * s + 1) ≤ (1 - 1 / (2 * rD)) * (n * S) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hPnn : 0 ≤ P := by linarith
  have h3RP : 0 ≤ 3 * R * P := by nlinarith
  have h12 : 0 ≤ 12 * (T / R) := by positivity
  -- replace `size (3rp)` by its bound `A`
  have h1 : (3 * R * P) * s + 1 ≤ (3 * R * P) * A + 1 := by
    have := mul_le_mul_of_nonneg_left hs h3RP
    linarith
  have h2 : 12 * (T / R) * ((3 * R * P) * s + 1) ≤ 12 * (T / R) * ((3 * R * P) * A + 1) :=
    mul_le_mul_of_nonneg_left h1 h12
  -- cancel `r` and rewrite `p = 6b`
  have h3 : 12 * (T / R) * ((3 * R * P) * A + 1) = 216 * (T * B) * A + 12 * (T / R) := by
    rw [hP]
    field_simp
    ring
  -- `216 T b A = 1728 · (T b / (8n)) · n A ≤ 1728 n A`
  have h4 : 216 * (T * B) * A ≤ 1728 * n * A := by
    have := mul_le_mul_of_nonneg_right hTb hA
    nlinarith
  -- `12 T/r ≤ 12 T ≤ 96 n`, since `b ≥ 1`
  have h5 : 12 * (T / R) ≤ 96 * n := by
    have hle : T / R ≤ T := div_le_self hT hR1
    have hT8 : T ≤ 8 * n := by nlinarith
    linarith
  -- the key inequality, transported to `n * size n`
  have h6 : 1728 * n * A + 96 * n ≤ (1 - 1 / (2 * rD)) * (n * S) := by
    have hc := one_sub_nonneg
    calc 1728 * n * A + 96 * n = n * (1728 * A + 96) := by ring
      _ ≤ n * ((1 - 1 / (2 * rD)) * L) := mul_le_mul_of_nonneg_left hkey hn
      _ = (1 - 1 / (2 * rD)) * (n * L) := by ring
      _ ≤ (1 - 1 / (2 * rD)) * (n * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLS hn) hc
  linarith [h2, h3, h4, h5, h6]

/-- The transform term of `mainCost` (after cancelling `C`) is at most `(1 - 1/(2d)) n log₂ n`. -/
theorem est1 (n : ℕ) (h : Work.Recursion.Est1Hyp n) : Work.Recursion.Est1 n := by
  obtain ⟨hb1, hR1, hTb, hs, hK, hSn, hkey⟩ := h
  have hTnn : 0 ≤ rT n := by unfold rT; positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hP : rP n = 6 * rB n := rP_eq n
  -- the auxiliary quantity `A = k_T/d + log₂(18b) + 3` is nonnegative
  have hA : 0 ≤ rK n / rD + Real.logb 2 (18 * rB n) + 3 := by
    have h1 : 0 ≤ Real.logb 2 (18 * rB n) := Real.logb_nonneg (by norm_num) (by nlinarith)
    have h2 : 0 ≤ rK n / rD := by
      have h3 : (0 : ℝ) ≤ rK n := by unfold rK; positivity
      exact div_nonneg h3 (by rw [rD_eq]; norm_num)
    linarith
  -- transport the key inequality from `k_T` to `A`
  have hkey' : 1728 * (rK n / rD + Real.logb 2 (18 * rB n) + 3) + 96
      ≤ (1 - 1 / (2 * rD)) * Real.logb 2 (n : ℝ) := by
    have hdiv : rK n / rD ≤ (Real.logb 2 (n : ℝ) + 3) / rD := by
      apply div_le_div_of_nonneg_right hK
      rw [rD_eq]; norm_num
    linarith
  exact arith_est1 n (rT n) (rR n) (rP n) (rB n) (rS (3 * rpar n * ppar n))
    (rK n / rD + Real.logb 2 (18 * rB n) + 3) (Real.logb 2 (n : ℝ)) (rS n)
    hn hTnn hR1 hb1 (le_of_lt hTb) hP hs hA hSn hkey'

end

end Work.Recursion
