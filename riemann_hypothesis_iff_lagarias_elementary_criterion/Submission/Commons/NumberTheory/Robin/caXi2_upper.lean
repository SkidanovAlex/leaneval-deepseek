import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.Real.log_le_half_sub_inv
import Submission.Commons.Analysis.Real.log_one_add_inv_bounds

namespace Commons.NumberTheory.Robin

open Real

/-! ### helpers for `caXi2_upper` -/

/-- `log ξ ≥ 20.7` for `ξ ≥ 10⁹`. -/
lemma caXi2_upper_logXi_ge (ξ : ℝ) (hξ : (10 : ℝ) ^ 9 ≤ ξ) :
    (20.7 : ℝ) ≤ Real.log ξ := by
  have hlog10 : (23 : ℝ) / 10 ≤ Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hpow : Real.log ((10 : ℝ) ^ 9) = 9 * Real.log 10 := Real.log_pow 10 9
  have hle : Real.log ((10 : ℝ) ^ 9) ≤ Real.log ξ := Real.log_le_log (by positivity) hξ
  rw [hpow] at hle
  linarith

/-- `x ↦ log (1 + 1/(x+x²)) / log x` is strictly decreasing on `(1, ∞)`. -/
lemma caXi2_upper_f2_strict {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    Real.log (1 + 1 / (b + b ^ 2)) / Real.log b
      < Real.log (1 + 1 / (a + a ^ 2)) / Real.log a := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlab : Real.log a < Real.log b := Real.log_lt_log hapos hab
  have ha2 : a ^ 2 < b ^ 2 := by
    have h1 : 0 < b - a := by linarith
    have h2 : 0 < b + a := by linarith
    nlinarith [mul_pos h1 h2]
  have hsab : a + a ^ 2 < b + b ^ 2 := by linarith
  have hsa : 0 < a + a ^ 2 := by positivity
  have hinv : 1 / (b + b ^ 2) < 1 / (a + a ^ 2) := one_div_lt_one_div_of_lt hsa hsab
  have hU1 : 1 + 1 / (b + b ^ 2) < 1 + 1 / (a + a ^ 2) := by linarith
  have hUp : 0 < 1 + 1 / (b + b ^ 2) := by positivity
  have hlogU : Real.log (1 + 1 / (b + b ^ 2)) < Real.log (1 + 1 / (a + a ^ 2)) :=
    Real.log_lt_log hUp hU1
  have hVal : 0 < Real.log (1 + 1 / (a + a ^ 2)) := by
    apply Real.log_pos
    have : 0 < 1 / (a + a ^ 2) := one_div_pos.mpr hsa
    linarith
  rw [div_lt_div_iff₀ hlb hla]
  exact lt_trans (mul_lt_mul_of_pos_right hlogU hla) (mul_lt_mul_of_pos_left hlab hVal)

/-- For `0 ≤ t < 1`: `-t(1-t)(2-t) ≤ 2(1-t)² log (1-t)`. -/
lemma caXi2_upper_log_sub_quad {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -t * (1 - t) * (2 - t) ≤ 2 * (1 - t) ^ 2 * Real.log (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  have hu : 1 ≤ (1 - t)⁻¹ := by
    rw [one_le_inv₀ hpos]; linarith
  have h := Commons.Analysis.Real.log_le_half_sub_inv hu
  have h' : Real.log (1 - t)⁻¹ ≤ ((1 - t)⁻¹ - (1 - t)) / 2 := by
    have hinv : ((1 - t)⁻¹)⁻¹ = 1 - t := inv_inv _
    simpa [hinv] using h
  have hkey : ((1 - t) - (1 - t)⁻¹) / 2 ≤ Real.log (1 - t) := by
    have hlog : Real.log (1 - t) = - Real.log (1 - t)⁻¹ := by
      rw [Real.log_inv]; ring
    rw [hlog]; linarith
  have hmul : 2 * (1 - t) ^ 2 * (((1 - t) - (1 - t)⁻¹) / 2)
      ≤ 2 * (1 - t) ^ 2 * Real.log (1 - t) := by
    apply mul_le_mul_of_nonneg_left hkey
    positivity
  have heq : 2 * (1 - t) ^ 2 * (((1 - t) - (1 - t)⁻¹) / 2) = -t * (1 - t) * (2 - t) := by
    field_simp
    ring
  rw [heq] at hmul
  exact hmul

/-- The polynomial `φ(t) = (log2-2r) + t(r-2log2-2) + t²(log2+3) - t³` (with `r = 0.323`)
is decreasing on `[0, 0.323/20.7]`; here `s = log 2 ∈ [0,1]`. -/
lemma caXi2_upper_phi_anti {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (htt : t ≤ 0.323 / 20.7) :
    (s - 2 * 0.323) + (0.323 / 20.7) * (0.323 - 2 * s - 2)
        + (0.323 / 20.7) ^ 2 * (s + 3) - (0.323 / 20.7) ^ 3
      ≤ (s - 2 * 0.323) + t * (0.323 - 2 * s - 2) + t ^ 2 * (s + 3) - t ^ 3 := by
  have hfac : (s - 2 * 0.323) + t * (0.323 - 2 * s - 2) + t ^ 2 * (s + 3) - t ^ 3
      - ((s - 2 * 0.323) + (0.323 / 20.7) * (0.323 - 2 * s - 2)
        + (0.323 / 20.7) ^ 2 * (s + 3) - (0.323 / 20.7) ^ 3)
      = (t - 0.323 / 20.7) * ((0.323 - 2 * s - 2) + (t + 0.323 / 20.7) * (s + 3)
          - (t ^ 2 + t * (0.323 / 20.7) + (0.323 / 20.7) ^ 2)) := by ring
  have hq : ((0.323 - 2 * s - 2) + (t + 0.323 / 20.7) * (s + 3)
      - (t ^ 2 + t * (0.323 / 20.7) + (0.323 / 20.7) ^ 2)) ≤ 0 := by
    have h1 : (t + 0.323 / 20.7) * (s + 3) ≤ 2 * (0.323 / 20.7) * (s + 3) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have h2 : (0 : ℝ) ≤ t ^ 2 + t * (0.323 / 20.7) + (0.323 / 20.7) ^ 2 := by positivity
    have h3 : (0.323 - 2 * s - 2) + 2 * (0.323 / 20.7) * (s + 3) ≤ 0 := by
      have hscoef : (-2 + 2 * (0.323 / 20.7) : ℝ) ≤ 0 := by norm_num
      have hconst : (0.323 - 2 + 6 * (0.323 / 20.7) : ℝ) ≤ 0 := by norm_num
      have hdecomp : (0.323 - 2 * s - 2) + 2 * (0.323 / 20.7) * (s + 3)
          = (0.323 - 2 + 6 * (0.323 / 20.7)) + s * (-2 + 2 * (0.323 / 20.7)) := by ring
      rw [hdecomp]
      nlinarith [hs0, hscoef, hconst]
    linarith
  rw [← sub_nonneg, hfac]
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hq

/-- Numeric: `φ(0.323/20.7) ≥ 1/5000`. -/
lemma caXi2_upper_phi0_ge :
    (1 / 5000 : ℝ)
      ≤ (Real.log 2 - 2 * 0.323) + (0.323 / 20.7) * (0.323 - 2 * Real.log 2 - 2)
        + (0.323 / 20.7) ^ 2 * (Real.log 2 + 3) - (0.323 / 20.7) ^ 3 := by
  have h2 : (0.6931471803 : ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
  have hadj : (Real.log 2 - 2 * 0.323) + (0.323 / 20.7) * (0.323 - 2 * Real.log 2 - 2)
        + (0.323 / 20.7) ^ 2 * (Real.log 2 + 3) - (0.323 / 20.7) ^ 3
      = Real.log 2 * (1 - 2 * (0.323 / 20.7) + (0.323 / 20.7) ^ 2)
        + (-2 * 0.323 + (0.323 / 20.7) * (0.323 - 2) + 3 * (0.323 / 20.7) ^ 2
            - (0.323 / 20.7) ^ 3) := by ring
  rw [hadj]
  have hcoef : (0 : ℝ) ≤ 1 - 2 * (0.323 / 20.7) + (0.323 / 20.7) ^ 2 := by norm_num
  have hnum : (1 / 5000 : ℝ)
      ≤ 0.6931471803 * (1 - 2 * (0.323 / 20.7) + (0.323 / 20.7) ^ 2)
        + (-2 * 0.323 + (0.323 / 20.7) * (0.323 - 2) + 3 * (0.323 / 20.7) ^ 2
            - (0.323 / 20.7) ^ 3) := by norm_num
  have hmul := mul_le_mul_of_nonneg_right h2 hcoef
  linarith [hmul, hnum]

/-- Core numeric estimate: for `L ≥ 20.7`,
`(1 + e^{-L}) L ≤ 2 (1 - 0.323/L)² ( (L + log 2)/2 + log (1 - 0.323/L) )`. -/
lemma caXi2_upper_core (L : ℝ) (hL : (20.7 : ℝ) ≤ L) :
    (1 + Real.exp (-L)) * L
      ≤ 2 * (1 - 0.323 / L) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - 0.323 / L)) := by
  have hLpos : 0 < L := by linarith
  set t : ℝ := 0.323 / L with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hLpos]; linarith
  have htt : t ≤ 0.323 / 20.7 := by
    rw [ht]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have htL : t * L = 0.323 := by rw [ht, div_mul_cancel₀ _ hLpos.ne']
  have hs0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs1 : Real.log 2 ≤ 1 := by have h := Real.log_two_lt_d9; linarith
  -- `Le^{-L} ≤ 1/20000`
  have hLe : L * Real.exp (-L) ≤ 1 / 20000 := by
    have hexp10 : (20000 : ℝ) < Real.exp 10 := by
      have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hp : Real.exp 10 = (Real.exp 1) ^ 10 := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 10)
      rw [hp]
      calc (20000 : ℝ) < (2.7 : ℝ) ^ 10 := by norm_num
        _ < (Real.exp 1) ^ 10 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    have hLhalf : L ≤ Real.exp (L / 2) := by
      have h0 : (0 : ℝ) ≤ L / 2 := by linarith
      have hsum := Real.sum_le_exp_of_nonneg h0 3
      have heqsum : (∑ i ∈ Finset.range 3, (L / 2) ^ i / ((Nat.factorial i : ℕ) : ℝ))
          = 1 + L / 2 + (L / 2) ^ 2 * (1 / 2) := by
        simp [Finset.sum_range_succ, Nat.factorial]
        ring
      have hpoly : L ≤ 1 + L / 2 + (L / 2) ^ 2 * (1 / 2) := by
        nlinarith [sq_nonneg (L - 2)]
      rw [heqsum] at hsum
      linarith
    have hbound : L * Real.exp (-L) ≤ Real.exp (-L / 2) := by
      calc L * Real.exp (-L) ≤ Real.exp (L / 2) * Real.exp (-L) :=
            mul_le_mul_of_nonneg_right hLhalf (Real.exp_pos _).le
        _ = Real.exp (-L / 2) := by
            rw [← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (-L / 2) ≤ Real.exp (-10) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-10) < 1 / 20000 := by
      rw [Real.exp_neg, one_div, inv_lt_inv₀ (Real.exp_pos 10) (by norm_num)]
      exact hexp10
    linarith
  -- `1/5000 ≤ F(L)`
  have hFt : (1 / 5000 : ℝ)
      ≤ 2 * (1 - t) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - t)) - L := by
    have hB1 := caXi2_upper_log_sub_quad ht0 ht1
    have hB2 : (1 - t) ^ 2 * (L + Real.log 2) - t * (1 - t) * (2 - t) - L
        = (Real.log 2 - 2 * 0.323) + t * (0.323 - 2 * Real.log 2 - 2)
            + t ^ 2 * (Real.log 2 + 3) - t ^ 3 := by
      have hLt : t * L = 0.323 := htL
      have hLt2 : t ^ 2 * L = t * 0.323 := by
        calc t ^ 2 * L = t * (t * L) := by ring
          _ = t * 0.323 := by rw [hLt]
      nlinarith [hLt, hLt2]
    have hphi_ge := caXi2_upper_phi_anti hs0 hs1 ht0 htt
    have hphi0 := caXi2_upper_phi0_ge
    have hstep : (Real.log 2 - 2 * 0.323) + t * (0.323 - 2 * Real.log 2 - 2)
          + t ^ 2 * (Real.log 2 + 3) - t ^ 3
        ≤ 2 * (1 - t) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - t)) - L := by
      have he : 2 * (1 - t) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - t)) - L
          = (1 - t) ^ 2 * (L + Real.log 2) + 2 * (1 - t) ^ 2 * Real.log (1 - t) - L := by ring
      rw [he]
      have hmono : (1 - t) ^ 2 * (L + Real.log 2) - t * (1 - t) * (2 - t) - L
          ≤ (1 - t) ^ 2 * (L + Real.log 2) + 2 * (1 - t) ^ 2 * Real.log (1 - t) - L := by
        linarith [hB1]
      rw [hB2] at hmono
      exact hmono
    linarith [hphi0, hphi_ge, hstep]
  have hleF : L * Real.exp (-L)
      ≤ 2 * (1 - t) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - t)) - L := by linarith
  calc (1 + Real.exp (-L)) * L = L + L * Real.exp (-L) := by ring
    _ ≤ L + (2 * (1 - t) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - t)) - L) := by linarith
    _ = 2 * (1 - t) ^ 2 * ((L + Real.log 2) / 2 + Real.log (1 - t)) := by ring

theorem caXi2_upper (ξ ξ2 : ℝ) (hξ : (10 : ℝ) ^ 9 ≤ ξ) (hξ2 : 1 < ξ2)
    (hF : Real.log (1 + 1 / (ξ2 + ξ2 ^ 2)) / Real.log ξ2
        = Real.log (1 + 1 / ξ) / Real.log ξ) :
    ξ2 ≤ Real.sqrt (2 * ξ) * (1 - 0.323 / Real.log ξ) := by
  set L : ℝ := Real.log ξ with hL
  set B : ℝ := Real.sqrt (2 * ξ) * (1 - 0.323 / L) with hB
  have hξpos : 0 < ξ := by positivity
  have hL20 : (20.7 : ℝ) ≤ L := by rw [hL]; exact caXi2_upper_logXi_ge ξ hξ
  have hLpos : 0 < L := by linarith
  have h1mL : (0 : ℝ) < 1 - 0.323 / L := by
    have : 0.323 / L < 1 := by rw [div_lt_one hLpos]; linarith
    linarith
  have hBpos : 0 < B := by
    rw [hB]; exact mul_pos (Real.sqrt_pos.mpr (by positivity)) h1mL
  have hB2 : B ^ 2 = 2 * ξ * (1 - 0.323 / L) ^ 2 := by
    rw [hB, mul_pow, Real.sq_sqrt (by positivity)]
  have hB1 : 1 < B := by
    have hge : (1 : ℝ) < B ^ 2 := by
      rw [hB2]
      have hfac : (1 / 2 : ℝ) ≤ 1 - 0.323 / L := by
        have h : 0.323 / L ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
        linarith
      have hfac2 : (1 / 2 : ℝ) ^ 2 ≤ (1 - 0.323 / L) ^ 2 := pow_le_pow_left₀ (by norm_num) hfac 2
      calc (1 : ℝ) < 2 * ξ * (1 / 2) ^ 2 := by nlinarith [hξ]
        _ ≤ 2 * ξ * (1 - 0.323 / L) ^ 2 := mul_le_mul_of_nonneg_left hfac2 (by positivity)
    have hs : |(1 : ℝ)| < |B| := sq_lt_sq.mp (by simpa using hge)
    rwa [abs_of_pos zero_lt_one, abs_of_pos hBpos] at hs
  have hlogB : Real.log B = (L + Real.log 2) / 2 + Real.log (1 - 0.323 / L) := by
    rw [hB, Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by positivity))) (ne_of_gt h1mL),
        Real.log_sqrt (by positivity)]
    have hlog2ξ : Real.log (2 * ξ) = Real.log 2 + L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hξpos), hL]
    rw [hlog2ξ]; ring
  have hlogBpos : 0 < Real.log B := Real.log_pos hB1
  -- step 1
  have hstep1 : Real.log (1 + 1 / (B + B ^ 2)) / Real.log B ≤ 1 / (B ^ 2 * Real.log B) := by
    have hlog_le : Real.log (1 + 1 / (B + B ^ 2)) ≤ 1 / B ^ 2 := by
      have h1 : Real.log (1 + 1 / (B + B ^ 2)) ≤ 1 / (B + B ^ 2) := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (B + B ^ 2) by positivity)
        linarith
      have h2 : 1 / (B + B ^ 2) ≤ 1 / B ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [hBpos]
      linarith
    have he : 1 / (B ^ 2 * Real.log B) = (1 / B ^ 2) / Real.log B := by rw [div_div]
    rw [he, div_le_div_iff₀ hlogBpos hlogBpos]
    exact mul_le_mul_of_nonneg_right hlog_le (le_of_lt hlogBpos)
  -- step 2
  have hstep2 : 1 / (B ^ 2 * Real.log B) ≤ Real.log (1 + 1 / ξ) / L := by
    have hmain : (ξ + 1) * L ≤ B ^ 2 * Real.log B := by
      have hcore := caXi2_upper_core L hL20
      have hexp : Real.exp (-L) = 1 / ξ := by
        rw [hL, Real.exp_neg, Real.exp_log hξpos, one_div]
      rw [hexp] at hcore
      have hcore2 : ξ * ((1 + 1 / ξ) * L)
          ≤ ξ * (2 * (1 - 0.323 / L) ^ 2
              * ((L + Real.log 2) / 2 + Real.log (1 - 0.323 / L))) :=
        mul_le_mul_of_nonneg_left hcore (le_of_lt hξpos)
      have heq1 : ξ * ((1 + 1 / ξ) * L) = (ξ + 1) * L := by field_simp
      have heq2 : B ^ 2 * Real.log B
          = ξ * (2 * (1 - 0.323 / L) ^ 2
              * ((L + Real.log 2) / 2 + Real.log (1 - 0.323 / L))) := by
        rw [hB2, hlogB]; ring
      rw [heq1] at hcore2
      rw [← heq2] at hcore2
      exact hcore2
    have hloglb : 1 / (ξ + 1) < Real.log (1 + 1 / ξ) :=
      (Commons.Analysis.Real.log_one_add_inv_bounds hξpos).1
    have h1 : 1 / (B ^ 2 * Real.log B) ≤ 1 / ((ξ + 1) * L) := by
      apply one_div_le_one_div_of_le (by positivity) hmain
    have h2 : 1 / ((ξ + 1) * L) ≤ Real.log (1 + 1 / ξ) / L := by
      rw [show (1 : ℝ) / ((ξ + 1) * L) = (1 / (ξ + 1)) / L by rw [div_div]]
      exact div_le_div_of_nonneg_right (le_of_lt hloglb) (le_of_lt hLpos)
    linarith [h1, h2]
  have hf2B : Real.log (1 + 1 / (B + B ^ 2)) / Real.log B ≤ Real.log (1 + 1 / ξ) / L :=
    le_trans hstep1 hstep2
  by_contra hcon
  rw [not_le] at hcon
  have hf2strict := caXi2_upper_f2_strict hB1 hcon
  rw [hF] at hf2strict
  linarith [hf2B, hf2strict]

end Commons.NumberTheory.Robin