import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

/-- A numerical bound: `e^{3/2} ≤ 5`.

This is the only numerical input needed by `wExpCmp`; it is proved from
`Real.exp_one_lt_d9 : exp 1 < 2.7182818286` by cubing. -/
lemma exp_three_halves_le_five : Real.exp (3 / 2) ≤ 5 := by
  have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = 1 + (1 + 1) by norm_num, Real.exp_add, Real.exp_add]
    ring
  have hlt : (Real.exp 1) ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h25 : (2.7182818286 : ℝ) ^ 3 < 25 := by norm_num
  have hexp3 : Real.exp 3 < 25 := by rw [h3]; linarith
  have hsq : (Real.exp (3 / 2)) ^ 2 = Real.exp 3 := by
    rw [sq, ← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (3 / 2) := Real.exp_pos _
  nlinarith [hexp3, hsq, hpos]

/-- Comparison of the weight `w(z) = (1+z)²/z²` at `z = e^s` and `z = e^t`
for `|s - t| ≤ 1/2`:
`(w(e^s))² e^s ≤ 5 (w(e^t))² e^t`.

Since `w(e^u)² e^u = (1 + e^u)^4 e^{-3u}`, and writing `Q = e^t`, `R = e^{s-t}`
the claim becomes `(1 + QR)^4 ≤ 5 R^3 (1+Q)^4`, i.e.
`((1+QR)/(1+Q))^4 ≤ 5 R^3`.  For `R ≥ 1` one has `1 + QR ≤ R(1+Q)` and `R ≤ 5`;
for `R ≤ 1` one has `1 + QR ≤ 1 + Q` and `5 R^3 ≥ 1` because
`R ≥ e^{-1/2}` and `e^{3/2} ≤ 5`. -/
theorem wExpCmp (s t : ℝ) (hst : |s - t| ≤ 1 / 2) :
    (Work.Spaces.w (Real.exp s)) ^ 2 * Real.exp s
      ≤ 5 * ((Work.Spaces.w (Real.exp t)) ^ 2 * Real.exp t) := by
  have h5 : Real.exp (3 / 2) ≤ 5 := exp_three_halves_le_five
  obtain ⟨hu1, hu2⟩ := abs_le.mp hst
  set Q : ℝ := Real.exp t with hQdef
  set R : ℝ := Real.exp (s - t) with hRdef
  have hQpos : 0 < Q := by rw [hQdef]; exact Real.exp_pos t
  have hRpos : 0 < R := by rw [hRdef]; exact Real.exp_pos (s - t)
  have hP : Real.exp s = Q * R := by
    rw [hQdef, hRdef, ← Real.exp_add]
    rw [show t + (s - t) = s by ring]
  have hkey : (1 + Q * R) ^ 4 ≤ 5 * R ^ 3 * (1 + Q) ^ 4 := by
    have h4 : (0 : ℝ) ≤ (1 + Q) ^ 4 := by positivity
    rcases le_total 0 (s - t) with hu | hu
    · -- `R ≥ 1`
      have hR1 : 1 ≤ R := by
        rw [hRdef, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr hu
      have hle : 1 + Q * R ≤ R * (1 + Q) := by nlinarith [hR1, hQpos]
      have hR5 : R ≤ 5 := by
        rw [hRdef]
        calc Real.exp (s - t) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hu2
          _ ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ 5 := h5
      have hpow : (1 + Q * R) ^ 4 ≤ (R * (1 + Q)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hle 4
      have hR45 : R ^ 4 ≤ 5 * R ^ 3 := by
        have hh := mul_le_mul_of_nonneg_left hR5 (pow_nonneg hRpos.le 3)
        nlinarith [hh]
      calc (1 + Q * R) ^ 4 ≤ (R * (1 + Q)) ^ 4 := hpow
        _ = R ^ 4 * (1 + Q) ^ 4 := by ring
        _ ≤ 5 * R ^ 3 * (1 + Q) ^ 4 := mul_le_mul_of_nonneg_right hR45 h4
    · -- `R ≤ 1`
      have hR1 : R ≤ 1 := by
        rw [hRdef, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr hu
      have hle : 1 + Q * R ≤ 1 + Q := by nlinarith [hR1, hQpos]
      have hpow : (1 + Q * R) ^ 4 ≤ (1 + Q) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hle 4
      have hR3eq : R ^ 3 = Real.exp (3 * (s - t)) := by
        rw [hRdef]
        exact (Real.exp_nat_mul (s - t) 3).symm
      have hu3 : -(3 / 2) ≤ 3 * (s - t) := by linarith [hu1]
      have hExp : Real.exp (-(3 / 2)) ≤ R ^ 3 := by
        rw [hR3eq]
        exact Real.exp_le_exp.mpr hu3
      have h5inv : (5 : ℝ)⁻¹ ≤ Real.exp (-(3 / 2)) := by
        rw [Real.exp_neg]
        have h := one_div_le_one_div_of_le (Real.exp_pos (3 / 2)) h5
        simpa [one_div] using h
      have h5R3 : 1 ≤ 5 * R ^ 3 := by
        have h := mul_le_mul_of_nonneg_left (le_trans h5inv hExp) (by norm_num : (0 : ℝ) ≤ 5)
        rw [mul_inv_cancel₀ (by norm_num : (5 : ℝ) ≠ 0)] at h
        exact h
      calc (1 + Q * R) ^ 4 ≤ (1 + Q) ^ 4 := hpow
        _ = 1 * (1 + Q) ^ 4 := by ring
        _ ≤ 5 * R ^ 3 * (1 + Q) ^ 4 := mul_le_mul_of_nonneg_right h5R3 h4
  have hL : (Work.Spaces.w (Real.exp s)) ^ 2 * Real.exp s
      = (1 + Real.exp s) ^ 4 / (Real.exp s) ^ 3 := by
    rw [Work.Spaces.w]; field_simp
  have hRside : (Work.Spaces.w (Real.exp t)) ^ 2 * Real.exp t
      = (1 + Real.exp t) ^ 4 / (Real.exp t) ^ 3 := by
    rw [Work.Spaces.w]; field_simp
  rw [hL, hRside, hP]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Q * R) ^ 3)]
  have hsimp : 5 * ((1 + Q) ^ 4 / Q ^ 3) * (Q * R) ^ 3 = 5 * R ^ 3 * (1 + Q) ^ 4 := by
    field_simp
  rw [hsimp]
  exact hkey

end Work.FTS.EllSol.EllPkgAux
