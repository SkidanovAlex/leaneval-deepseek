import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

/-!
# The elementary row bound `Σ_{r ≤ R}(|log(Y/r)| + 1) ≤ 10 Y` for `R ≤ 2Y`

The summand is bounded pointwise by `2√(Y/r) + 2`.  Indeed, for `r ≤ Y` one has
`|log(Y/r)| = log(Y/r) ≤ 2√(Y/r)` (from `log t = 2 log √t ≤ 2(√t - 1) ≤ 2√t`,
which is `Real.log_le_rpow_div` at `ε = 1/2`), while for `r > Y` one has
`|log(Y/r)| = log(r/Y) ≤ log 2 ≤ 1 ≤ 2√(Y/r) + 1`.
Summing, `Σ 2√(Y/r) ≤ 2√Y · 2√R = 4√(YR) ≤ 4√2 · Y` (using `R ≤ 2Y`) and the
constant terms contribute `2R ≤ 4Y`, giving `≤ (4√2 + 4)Y ≤ 10Y` since `√2 < 3/2`.
-/

/-- `log t ≤ 2√t` for `t ≥ 0`. -/
private lemma log_le_two_sqrt {t : ℝ} (ht : 0 ≤ t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h := Real.log_le_rpow_div (x := t) (ε := (1 : ℝ) / 2) ht (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  have h' : Real.sqrt t / ((1 : ℝ) / 2) = 2 * Real.sqrt t := by ring
  rwa [h'] at h

/-- Telescoping: `Σ_{m=1}^{M} 1/√m ≤ 2√M`. -/
private lemma sum_inv_sqrt_le (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ)) ≤ 2 * Real.sqrt (M : ℝ) := by
  have htel : ∀ n : ℕ,
      (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)
        ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
    intro n
    have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hpos]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity),
               Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity),
               sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))]
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega)]
    have hk := htel k
    simp only [Nat.cast_add, Nat.cast_one] at hk ih ⊢
    linarith

/-- `Σ_{r=1}^{R}(|log(Y/r)| + 1) ≤ 10 Y` whenever `Y ≥ 1` and `R ≤ 2Y`. -/
lemma rowSum_abs_log_le {Y : ℝ} (hY : 1 ≤ Y) {R : ℕ} (hR : (R : ℝ) ≤ 2 * Y) :
    ∑ r ∈ Finset.Icc 1 R, (|Real.log (Y / (r : ℝ))| + 1) ≤ 10 * Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  -- pointwise bound
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      |Real.log (Y / (r : ℝ))| + 1 ≤ 2 * Real.sqrt (Y / (r : ℝ)) + 2 := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      have := (Finset.mem_Icc.mp hr).1
      exact_mod_cast this
    have hrR : (r : ℝ) ≤ (R : ℝ) := by
      have := (Finset.mem_Icc.mp hr).2
      exact_mod_cast this
    have hr2Y : (r : ℝ) ≤ 2 * Y := le_trans hrR hR
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    rcases le_or_gt (r : ℝ) Y with h | h
    · -- `r ≤ Y`: `log(Y/r) ≥ 0` and `log(Y/r) ≤ 2√(Y/r)`
      have ht : 1 ≤ Y / (r : ℝ) := (one_le_div hrpos).mpr h
      rw [abs_of_nonneg (Real.log_nonneg ht)]
      have := log_le_two_sqrt (le_of_lt (div_pos hY0 hrpos))
      linarith
    · -- `r > Y`: `|log(Y/r)| = log(r/Y) ≤ log 2 ≤ 1`
      have hlt : Y / (r : ℝ) < 1 := (div_lt_one hrpos).mpr h
      have hpos : 0 < Y / (r : ℝ) := div_pos hY0 hrpos
      rw [abs_of_nonpos (Real.log_nonpos (le_of_lt hpos) (le_of_lt hlt))]
      have h1 : -Real.log (Y / (r : ℝ)) = Real.log ((r : ℝ) / Y) := by
        rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hrpos),
            Real.log_div (ne_of_gt hrpos) (ne_of_gt hY0)]
        ring
      rw [h1]
      have hrY : (r : ℝ) / Y ≤ 2 := by rw [div_le_iff₀ hY0]; linarith
      have hlog2 : Real.log ((r : ℝ) / Y) ≤ Real.log 2 := Real.log_le_log (by positivity) hrY
      have hlog2le1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have hnn : (0 : ℝ) ≤ 2 * Real.sqrt (Y / (r : ℝ)) := by positivity
      linarith
  have hstep1 : ∑ r ∈ Finset.Icc 1 R, (|Real.log (Y / (r : ℝ))| + 1)
      ≤ ∑ r ∈ Finset.Icc 1 R, (2 * Real.sqrt (Y / (r : ℝ)) + 2) :=
    Finset.sum_le_sum hterm
  -- pull out the factor `√Y`
  have hsqrt : ∀ r ∈ Finset.Icc 1 R,
      Real.sqrt (Y / (r : ℝ)) = Real.sqrt Y * (1 / Real.sqrt (r : ℝ)) := by
    intro r _
    rw [Real.sqrt_div (le_of_lt hY0), div_eq_mul_inv, one_div]
  have hstep2 : ∑ r ∈ Finset.Icc 1 R, (2 * Real.sqrt (Y / (r : ℝ)) + 2)
      = 2 * Real.sqrt Y * (∑ r ∈ Finset.Icc 1 R, 1 / Real.sqrt (r : ℝ)) + 2 * R := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r hr
      rw [hsqrt r hr]; ring
    · rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
  have hstep3 : 2 * Real.sqrt Y * (∑ r ∈ Finset.Icc 1 R, 1 / Real.sqrt (r : ℝ)) + 2 * R
      ≤ 2 * Real.sqrt Y * (2 * Real.sqrt R) + 2 * R := by
    have hnn : (0 : ℝ) ≤ 2 * Real.sqrt Y := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left (sum_inv_sqrt_le R) hnn) le_rfl
  -- `√Y·√R ≤ √2·Y`
  have hYR : Real.sqrt Y * Real.sqrt R ≤ Real.sqrt 2 * Y := by
    rw [← Real.sqrt_mul (le_of_lt hY0)]
    have h1 : Y * (R : ℝ) ≤ 2 * Y ^ 2 := by nlinarith [hR, hY0]
    calc Real.sqrt (Y * R) ≤ Real.sqrt (2 * Y ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 2 * Y := by
          rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_sq (le_of_lt hY0)]
  have hsqrt2 : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
    rw [Real.sqrt_le_iff]; norm_num
  nlinarith [hstep1, hstep2.le, hstep3, hYR, hsqrt2, hR]

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
