import Mathlib
import Submission.Work.Fx.piDefs

namespace Work.Fx

/-!
# Lower bound for `√(2 - Aseq p)`

`Aseq p = √(2 + √(2 + ⋯)) = 2 cos (π/2^(p+1))`, so `2 - Aseq p = 4 sin²(π/2^(p+2))`
and the target inequality is the elementary Jordan-type bound
`2 sin (π/2^(p+2)) ≥ 2^{-p}`.

Rather than trigonometry we use the purely algebraic recursion
`2 - Aseq (k+1) = (2 - Aseq k) / (2 + Aseq (k+1))`, whose denominator is at most `4`
because `Aseq (k+1) < 2`.  Hence `2 - Aseq p ≥ 2 / 4^p ≥ 4^{-p}`, and taking square
roots gives `√(2 - Aseq p) ≥ 2^{-p}`, which is exactly the statement.
-/

/-- The exact recursion satisfied by `2 - Aseq ·`.  Since `Aseq (k+1) = √(2 + Aseq k)`,
multiplying `2 - Aseq (k+1)` by the conjugate `2 + Aseq (k+1)` produces `2 - Aseq k`. -/
theorem two_sub_Aseq_succ (k : ℕ) :
    2 - Aseq (k + 1) = (2 - Aseq k) / (2 + Aseq (k + 1)) := by
  have hnn : 0 ≤ Aseq k := Real.sqrtTwoAddSeries_zero_nonneg k
  have hs : Aseq (k + 1) ^ 2 = 2 + Aseq k := by
    rw [Aseq_succ, Real.sq_sqrt (by linarith)]
  have hden : 2 + Aseq (k + 1) ≠ 0 := by
    have h1 : 0 ≤ Aseq (k + 1) := Real.sqrtTwoAddSeries_zero_nonneg (k + 1)
    linarith
  rw [eq_div_iff hden]
  nlinarith [hs]

/-- `2 - Aseq p` decreases by at most a factor `4` per step. -/
theorem pow_quarter_le_two_sub_Aseq (p : ℕ) : (1 / 4 : ℝ) ^ p ≤ 2 - Aseq p := by
  induction p with
  | zero => simp [Aseq_zero]
  | succ p ih =>
    rw [two_sub_Aseq_succ p]
    have hnum : 0 ≤ 2 - Aseq p := by linarith [two_sub_Aseq_pos p]
    have hlt : Aseq (p + 1) < 2 := Real.sqrtTwoAddSeries_lt_two (p + 1)
    have hpos : 0 < 2 + Aseq (p + 1) := by
      have h1 : 0 ≤ Aseq (p + 1) := Real.sqrtTwoAddSeries_zero_nonneg (p + 1)
      linarith
    have h4 : 2 + Aseq (p + 1) ≤ 4 := by linarith
    have hstep : (2 - Aseq p) / 4 ≤ (2 - Aseq p) / (2 + Aseq (p + 1)) :=
      div_le_div_of_nonneg_left hnum hpos h4
    have hprev : (1 / 4 : ℝ) ^ (p + 1) ≤ (2 - Aseq p) / 4 := by
      have h := div_le_div_of_nonneg_right ih (show (0 : ℝ) ≤ 4 by norm_num)
      have e : ((1 / 4 : ℝ) ^ p : ℝ) / 4 = (1 / 4) ^ p * (1 / 4) := by ring
      rw [e, ← pow_succ] at h
      exact h
    linarith

-- (file imports Submission.Work.Fx.piDefs; statement belongs in `namespace Work.Fx`)
-- Since Aseq p = sqrtTwoAddSeries 0 p = 2 * cos (π/2^(p+1)), we have
-- √(2 - Aseq p) = 2 sin (π/2^(p+2)) ≥ 2 * (2/π) * (π/2^(p+2)) = 2^(-p)  (Jordan's inequality,
-- `Real.mul_le_sin`), which is the inequality requested below.
theorem AseqSqrtLower (p : ℕ) : (1 / 2) ^ p ≤ Real.sqrt (2 - Aseq p) := by
  have h := pow_quarter_le_two_sub_Aseq p
  have hsq : ((1 / 2 : ℝ) ^ p) ^ 2 = (1 / 4 : ℝ) ^ p := by
    rw [← pow_mul, mul_comm p 2, pow_mul]
    norm_num
  have hs : Real.sqrt ((1 / 4 : ℝ) ^ p) = (1 / 2) ^ p := by
    rw [← hsq, Real.sqrt_sq (by positivity)]
  rw [← hs]
  exact Real.sqrt_le_sqrt h

end Work.Fx
