import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Pointwise logarithmic form of the Vinogradov–Korobov growth bound on the strip
`1/2 ≤ σ < 1`.  With `1 - σ ≤ R` and `|t| + 3 ≤ 2τ + 3` the growth bound implies
`log ‖ζ(σ+it)‖ ≤ log(A+1) + B R^{3/2} log(2τ+3) + log(log(2τ+3)+1)`.
The right-hand side is nonnegative, so the estimate also covers the (possible) zeros of `ζ` on the
critical strip, where `Real.log 0 = 0`. -/
theorem zeta_circle_regionB_pointwise {A B σ t τ R : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hgr : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ))
    (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ < 1) (ht : 3 ≤ |t|) (hR : 0 ≤ R)
    (h1σR : 1 - σ ≤ R) (htτ : |t| + 3 ≤ 2 * τ + 3) :
    Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log (A + 1) + B * R ^ (3 / 2 : ℝ) * Real.log (2 * τ + 3)
        + Real.log (Real.log (2 * τ + 3) + 1) := by
  have ht3pos : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have h1σpos : 0 < 1 - σ := by linarith
  have h2τ3 : (0 : ℝ) < 2 * τ + 3 := by linarith [htτ, abs_nonneg t]
  have hlt3pos : 0 < Real.log (|t| + 3) := by
    apply Real.log_pos; linarith [abs_nonneg t]
  have hlt3one : 1 ≤ Real.log (|t| + 3) := by
    have : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h6 : (Real.exp 1 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
    exact le_of_lt ((Real.lt_log_iff_exp_lt ht3pos).mpr h6)
  have hτlog : 0 ≤ Real.log (2 * τ + 3) := by
    apply Real.log_nonneg; linarith [htτ, abs_nonneg t]
  have hτlog1 : 0 ≤ Real.log (Real.log (2 * τ + 3) + 1) :=
    Real.log_nonneg (by linarith)
  have hRnn : 0 ≤ R := hR
  have hRA : 0 ≤ B * R ^ (3 / 2 : ℝ) :=
    mul_nonneg (le_of_lt hB) (Real.rpow_nonneg hRnn _)
  by_cases hz : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = 0
  · rw [hz, Real.log_zero]
    have hA1 : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith)
    have hB2 : 0 ≤ B * R ^ (3 / 2 : ℝ) * Real.log (2 * τ + 3) :=
      mul_nonneg hRA hτlog
    linarith
  · have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hb := hgr σ t hσ1 hσ2 ht
    have hXpos : 0 < (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht3pos _
    have hYpos : 0 < (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hlt3pos _
    have hlog := Real.log_le_log hzpos hb
    rw [Real.log_mul (mul_ne_zero (ne_of_gt hA) (ne_of_gt hXpos)) (ne_of_gt hYpos),
        Real.log_mul (ne_of_gt hA) (ne_of_gt hXpos),
        Real.log_rpow ht3pos, Real.log_rpow hlt3pos] at hlog
    -- now bound the three pieces
    have hpow : (1 - σ) ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt h1σpos) h1σR (by norm_num)
    have hlogle : Real.log (|t| + 3) ≤ Real.log (2 * τ + 3) :=
      Real.log_le_log ht3pos htτ
    have hterm2 : B * (1 - σ) ^ (3 / 2 : ℝ) * Real.log (|t| + 3)
        ≤ B * R ^ (3 / 2 : ℝ) * Real.log (2 * τ + 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (le_of_lt hB)) hlogle
        (le_of_lt hlt3pos) hRA
    have hterm1 : Real.log A ≤ Real.log (A + 1) := Real.log_le_log hA (by linarith)
    have hterm3 : (2 / 3 : ℝ) * Real.log (Real.log (|t| + 3))
        ≤ Real.log (Real.log (2 * τ + 3) + 1) := by
      have h0 : 0 ≤ Real.log (Real.log (|t| + 3)) := Real.log_nonneg hlt3one
      have h1 : Real.log (Real.log (|t| + 3)) ≤ Real.log (Real.log (2 * τ + 3) + 1) := by
        apply Real.log_le_log hlt3pos
        linarith
      nlinarith
    linarith

end Work.BMF
