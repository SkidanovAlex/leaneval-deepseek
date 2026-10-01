import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaCountCombined
import Submission.Work.ZeroDensity.Ingham.detFarTailSmall
import Submission.Work.ZeroDensity.Ingham.tsumIteExpNegDivTail
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.mkOneNormBound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_upper_stirling_shift
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Work.Sieve.sum_Icc_rpow_neg_half_le
import Submission.Work.ZeroDensity.Ingham.setIntegral_Ioi_add_const
import Submission.Work.ZeroDensity.Ingham.zetaDetector12
import Submission.Work.ZeroDensity.Ingham.zetaDetectorOneSelf
import Submission.Work.ZeroDensity.Ingham.perronIntIntegrableSelf
import Submission.Work.ZeroDensity.Ingham.detSumSplit
import Submission.Work.ZeroDensity.Ingham.zetaPerronIdentity
import Submission.Work.ZeroDensity.Ingham.zetaTailCountEtaSelf
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.critTailSmallBig
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.zetaIntegralCountWide

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-! ## Elementary arithmetic for the wide detector

The three smallness estimates of Montgomery's detector (`detFarTailSmallBig`, and the
corresponding residue and critical-line-tail estimates) hold in the wide range
`K ≤ T^4`, `Y ≤ (A T)^2`, `A ≥ 6` because the extra hypothesis
`(log (A T))^2 ≤ |Im ρ| ≤ T` forces `log (A T) ≥ 4`: with `x = log (A T)` one gets
`x^2 ≤ T = e^{log T} ≤ e^x / 6` (as `A ≥ 6`), i.e. `6 x^2 ≤ e^x`, while `e^x / x^2 ≤ e^4/16 < 6`
on `[log 12, 4]`. -/

/-- `e^x / x^2` is decreasing on `[2,4]`, with endpoint value `e^4/16`. -/
lemma exp_div_sq_le_four {x : ℝ} (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    Real.exp x / x ^ 2 ≤ Real.exp 4 / 16 := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (Real.exp x / x ^ 2) = x - 2 * Real.log x := by
    rw [Real.log_div (Real.exp_ne_zero x) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  have hlog4 : Real.log (Real.exp 4 / 16) = 4 - 2 * Real.log 4 := by
    rw [Real.log_div (Real.exp_ne_zero 4) (by norm_num), Real.log_exp]
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← Real.log_le_log_iff (div_pos (Real.exp_pos x) (by positivity))
      (div_pos (Real.exp_pos 4) (by norm_num)), hlog, hlog4]
  have hsplit : Real.log x = Real.log 4 + Real.log (x / 4) := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : x / 4 ≠ 0)]
    congr 1
    field_simp
  have hge : 1 - 4 / x ≤ Real.log (x / 4) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < x / 4 by positivity)
    have hinv : (x / 4)⁻¹ = 4 / x := by field_simp
    rwa [hinv] at h
  have hx4' : x - 4 ≤ 2 - 8 / x := by
    have h : (x - 4) * x ≤ (2 - 8 / x) * x := by
      have e : (2 - 8 / x) * x = 2 * x - 8 := by
        field_simp
      rw [e]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 4 - x)]
    exact le_of_mul_le_mul_right h hx0
  have hge2 : 2 - 8 / x ≤ 2 * Real.log (x / 4) := by
    have h := mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2)
    have e : (2 : ℝ) * (1 - 4 / x) = 2 - 8 / x := by
      field_simp
      ring
    linarith [h, e.le, e.ge]
  rw [hsplit]
  nlinarith [hx4', hge2]

/-- Under the detector's hypotheses (`A ≥ 6`, `T ≥ 2`, `(log (A T))^2 ≤ T`) one has
`4 ≤ log (A T)`. -/
lemma log_AT_ge_four {A T : ℝ} (hA : 6 ≤ A) (hT : 2 ≤ T)
    (h : (Real.log (A * T)) ^ 2 ≤ T) : 4 ≤ Real.log (A * T) := by
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  set x : ℝ := Real.log (A * T) with hxdef
  have hx2 : 2 ≤ x := by
    have h12 : Real.log 12 ≤ x := by
      rw [hxdef]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    have h2log : (2 : ℝ) ≤ Real.log 12 := by
      have h := Real.log_two_gt_d9
      have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
      have h3 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_three]
      rw [show (12 : ℝ) = 6 * 2 by norm_num,
        Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), hlog6]
      linarith
    linarith
  have hTle : T ≤ Real.exp x / 6 := by
    have h1 : Real.log T = x - Real.log A := by
      rw [hxdef, Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)]
      ring
    have h2 : Real.log 6 ≤ Real.log A := Real.log_le_log (by norm_num) hA
    have h3 : Real.exp (Real.log T) ≤ Real.exp (x - Real.log 6) := by
      apply Real.exp_le_exp.mpr
      rw [h1]
      linarith
    rw [Real.exp_log hTpos, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 6)] at h3
    linarith
  have h6 : 6 * x ^ 2 ≤ Real.exp x := by
    have hx2T : x ^ 2 ≤ T := by rw [hxdef]; exact h
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hratio : Real.exp x / x ^ 2 ≤ Real.exp 4 / 16 := exp_div_sq_le_four hx2 (le_of_lt hlt)
  have hx2pos : 0 < x ^ 2 := by positivity
  have h6' : 6 ≤ Real.exp x / x ^ 2 := by
    rw [le_div_iff₀ hx2pos]
    linarith
  have h4 : Real.exp 4 / 16 < 6 := by
    have he4 : Real.exp 4 < 81 := by
      have h1 : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h2 := Real.exp_one_lt_three
      have h3 : (Real.exp 1) ^ 4 < (3 : ℝ) ^ 4 := by
        gcongr
      rw [← h1] at h3
      linarith
    linarith
  linarith

/-- `e^5 < 150`: from the Taylor remainder `Real.exp_bound` at `x = 1`, `n = 8`
(`|e - Σ_{m<8} 1/m!| ≤ 9/322560`), giving `e ≤ 2.7182819`. -/
lemma exp5_lt_150 : Real.exp 5 < 150 := by
  have hb := Real.exp_bound (x := (1 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 8, (1 : ℝ) ^ m / (m.factorial : ℝ)) = (13700 : ℝ) / 5040 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hb
  have he : Real.exp 1 ≤ 2.7182819 := by
    have h2 : |Real.exp 1 - 13700 / 5040| ≤ 9 / 322560 := by
      convert hb using 1 <;> norm_num
    have := (abs_le.mp h2).2
    linarith
  have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
    have := Real.exp_nsmul (1 : ℝ) 5
    simpa using this
  rw [h5]
  have h6 : (Real.exp 1) ^ 5 ≤ (2.7182819 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he 5
  have h7 : (2.7182819 : ℝ) ^ 5 < 150 := by norm_num
  linarith

/-- `e^x / x^2` is decreasing on `[2,5]`, with endpoint value `e^5/25` (sibling of
`exp_div_sq_le_four`). -/
lemma exp_div_sq_le_five {x : ℝ} (h2 : 2 ≤ x) (h5 : x ≤ 5) :
    Real.exp x / x ^ 2 ≤ Real.exp 5 / 25 := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (Real.exp x / x ^ 2) = x - 2 * Real.log x := by
    rw [Real.log_div (Real.exp_ne_zero x) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  have hlog5 : Real.log (Real.exp 5 / 25) = 5 - 2 * Real.log 5 := by
    rw [Real.log_div (Real.exp_ne_zero 5) (by norm_num), Real.log_exp]
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← Real.log_le_log_iff (div_pos (Real.exp_pos x) (by positivity))
      (div_pos (Real.exp_pos 5) (by norm_num)), hlog, hlog5]
  have hsplit : Real.log x = Real.log 5 + Real.log (x / 5) := by
    rw [← Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity : x / 5 ≠ 0)]
    congr 1
    field_simp
  have hge : 1 - 5 / x ≤ Real.log (x / 5) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < x / 5 by positivity)
    have hinv : (x / 5)⁻¹ = 5 / x := by field_simp
    rwa [hinv] at h
  have hx5' : x - 5 ≤ 2 - 10 / x := by
    have h : (x - 5) * x ≤ (2 - 10 / x) * x := by
      have e : (2 - 10 / x) * x = 2 * x - 10 := by field_simp
      rw [e]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 5 - x)]
    exact le_of_mul_le_mul_right h hx0
  have hge2 : 2 - 10 / x ≤ 2 * Real.log (x / 5) := by
    have h := mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2)
    have e : (2 : ℝ) * (1 - 5 / x) = 2 - 10 / x := by
      field_simp
      ring
    linarith [h, e.le, e.ge]
  rw [hsplit]
  nlinarith [hx5', hge2]

/-- Strengthened vacuity: the detector's hypotheses force `5 ≤ log (A*T)`
(sibling of `log_AT_ge_four`, which gives only `4`). -/
lemma log_AT_ge_five {A T : ℝ} (hA : 6 ≤ A) (hT : 2 ≤ T)
    (h : (Real.log (A * T)) ^ 2 ≤ T) : 5 ≤ Real.log (A * T) := by
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  set x : ℝ := Real.log (A * T) with hxdef
  have hx2 : 2 ≤ x := by
    have h12 : Real.log 12 ≤ x := by
      rw [hxdef]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    have h2log : (2 : ℝ) ≤ Real.log 12 := by
      have h := Real.log_two_gt_d9
      have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
      have h3 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_three]
      rw [show (12 : ℝ) = 6 * 2 by norm_num,
        Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), hlog6]
      linarith
    linarith
  have hTle : T ≤ Real.exp x / 6 := by
    have h1 : Real.log T = x - Real.log A := by
      rw [hxdef, Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)]
      ring
    have h2 : Real.log 6 ≤ Real.log A := Real.log_le_log (by norm_num) hA
    have h3 : Real.exp (Real.log T) ≤ Real.exp (x - Real.log 6) := by
      apply Real.exp_le_exp.mpr
      rw [h1]
      linarith
    rw [Real.exp_log hTpos, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 6)] at h3
    linarith
  have h6 : 6 * x ^ 2 ≤ Real.exp x := by
    have hx2T : x ^ 2 ≤ T := by rw [hxdef]; exact h
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hratio : Real.exp x / x ^ 2 ≤ Real.exp 5 / 25 := exp_div_sq_le_five hx2 (le_of_lt hlt)
  have hx2pos : 0 < x ^ 2 := by positivity
  have h6' : 6 ≤ Real.exp x / x ^ 2 := by
    rw [le_div_iff₀ hx2pos]
    linarith
  have h4 : Real.exp 5 / 25 < 6 := by
    have := exp5_lt_150
    linarith
  linarith

/-! ## The far tail of the detector sum -/

/-- **The discarded far tail of Montgomery's detector sum is small, in the wide range
`K ≤ T^4`, `Y ≤ (A T)^2`, `A ≥ 6`** (the hypotheses of the wide zero detector): for every
`A ≥ 6`, `T ≥ 2`, `K ≥ 1`, `1 ≤ Y ≤ (A T)^2` and every `ρ` with `1/2 ≤ Re ρ ≤ 1`,
`|Im ρ| ≤ T`, `(log (A T))^2 ≤ |Im ρ|`,
`‖Σ_{n > Y (log (A T))^2} a_K(n) n^{-ρ} e^{-n/Y}‖ ≤ 1/20`.

This is `detFarTailSmall` with the hypotheses weakened from `K ≤ T`, `Y ≤ T^2` (the `K`-dependence
is absent from the estimate, since `‖a_K(n) n^{-ρ} e^{-n/Y}‖ ≤ 2 e^{-n/Y}`). -/
theorem detFarTailSmallBig :
    ∀ (A : ℝ), 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ ≤ 1 / 20 := by
  intro A hA T hT K Y hK1 hKT hY1 hYT ρ hρ1 hρ2 hγ hlog
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  set x : ℝ := Real.log (A * T) with hxdef
  have hxpos : 0 < x := Real.log_pos hAT1
  have hxT : x ^ 2 ≤ T := by rw [hxdef]; exact le_trans hlog hγ
  have hx4 : 4 ≤ x := by
    rw [hxdef]
    exact log_AT_ge_four hA hT (by
      rw [← hxdef]; exact hxT)
  have hfar : ‖detFarTail K Y (Y * x ^ 2) ρ‖
      ≤ 2 * (Y + 1) * Real.exp (-(⌊Y * x ^ 2⌋₊ : ℝ) / Y) := by
    rw [detFarTail]
    have hexpr : (fun n : ℕ => Real.exp (-(n : ℝ) / Y))
        = (fun n : ℕ => Real.exp (-(1 / Y)) ^ n) := by
      funext n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hnorm_lt : ‖Real.exp (-(1 / Y))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      have : (0 : ℝ) < 1 / Y := by positivity
      linarith
    have hexpsum : Summable (fun n : ℕ => Real.exp (-(n : ℝ) / Y)) := by
      rw [hexpr]
      exact summable_geometric_iff_norm_lt_one.mpr hnorm_lt
    have h2sum : Summable (fun n : ℕ => 2 * Real.exp (-(n : ℝ) / Y)) :=
      hexpsum.mul_left 2
    have hf_le_g : ∀ n : ℕ,
        ‖(if ⌊Y * x ^ 2⌋₊ < n then mCoef K n * (n : ℂ) ^ (-ρ)
            * Complex.exp (-(n : ℂ) / Y) else 0)‖
          ≤ (if ⌊Y * x ^ 2⌋₊ < n then 2 * Real.exp (-(n : ℝ) / Y) else 0) := by
      intro n
      by_cases h : ⌊Y * x ^ 2⌋₊ < n
      · rw [if_pos h, if_pos h]
        exact norm_term_le K n Y ρ (by omega) hρ1
      · rw [if_neg h, if_neg h]
        simp
    have hf_le_full : ∀ n : ℕ,
        ‖(if ⌊Y * x ^ 2⌋₊ < n then mCoef K n * (n : ℂ) ^ (-ρ)
            * Complex.exp (-(n : ℂ) / Y) else 0)‖
          ≤ 2 * Real.exp (-(n : ℝ) / Y) := by
      intro n
      by_cases h : ⌊Y * x ^ 2⌋₊ < n
      · rw [if_pos h]
        exact norm_term_le K n Y ρ (by omega) hρ1
      · rw [if_neg h]
        simp only [norm_zero]
        positivity
    have hgsum : Summable
        (fun n : ℕ => (if ⌊Y * x ^ 2⌋₊ < n then 2 * Real.exp (-(n : ℝ) / Y) else 0)) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h2sum
      · by_cases h : ⌊Y * x ^ 2⌋₊ < n
        · rw [if_pos h]; positivity
        · rw [if_neg h]
      · by_cases h : ⌊Y * x ^ 2⌋₊ < n
        · rw [if_pos h]
        · rw [if_neg h]; positivity
    have hfsum : Summable (fun n : ℕ => (if ⌊Y * x ^ 2⌋₊ < n then mCoef K n * (n : ℂ) ^ (-ρ)
        * Complex.exp (-(n : ℂ) / Y) else 0)) :=
      Summable.of_norm_bounded h2sum hf_le_full
    calc ‖∑' n, (if ⌊Y * x ^ 2⌋₊ < n then mCoef K n * (n : ℂ) ^ (-ρ)
            * Complex.exp (-(n : ℂ) / Y) else 0)‖
        ≤ ∑' n, ‖(if ⌊Y * x ^ 2⌋₊ < n then mCoef K n * (n : ℂ) ^ (-ρ)
            * Complex.exp (-(n : ℂ) / Y) else 0)‖ := norm_tsum_le_tsum_norm hfsum.norm
      _ ≤ ∑' n, (if ⌊Y * x ^ 2⌋₊ < n then 2 * Real.exp (-(n : ℝ) / Y) else 0) :=
          Summable.tsum_le_tsum hf_le_g hfsum.norm hgsum
      _ ≤ 2 * (Y + 1) * Real.exp (-(⌊Y * x ^ 2⌋₊ : ℝ) / Y) :=
          tsumIteExpNegDivTail Y hYpos ⌊Y * x ^ 2⌋₊ 2 (by norm_num)
  have hML : x ^ 2 - 1 ≤ (⌊Y * x ^ 2⌋₊ : ℝ) / Y := by
    have h1 : Y * x ^ 2 - 1 < (⌊Y * x ^ 2⌋₊ : ℝ) := Nat.sub_one_lt_floor (Y * x ^ 2)
    have h2 : (Y * x ^ 2 - 1) / Y < (⌊Y * x ^ 2⌋₊ : ℝ) / Y :=
      div_lt_div_of_pos_right h1 hYpos
    have h3 : (Y * x ^ 2 - 1) / Y = x ^ 2 - 1 / Y := by
      rw [sub_div, mul_div_cancel_left₀ (x ^ 2) (ne_of_gt hYpos)]
    have h4 : x ^ 2 - 1 ≤ (Y * x ^ 2 - 1) / Y := by
      rw [h3]
      have : 1 / Y ≤ 1 := by
        rw [div_le_one hYpos]; linarith
      linarith
    linarith
  have hYe : Y ≤ Real.exp (2 * x) := by
    have h2 : Real.exp (2 * x) = (A * T) ^ 2 := by
      have h3 : Real.exp (2 * x) = Real.exp x ^ 2 := by
        rw [show (2 : ℝ) * x = ((2 : ℕ) : ℝ) * x by ring, Real.exp_nat_mul]
      rw [h3, hxdef, Real.exp_log (by positivity : (0 : ℝ) < A * T)]
    linarith [h2.le, hYT]
  have hbound : 2 * (Y + 1) * Real.exp (-(⌊Y * x ^ 2⌋₊ : ℝ) / Y) ≤ 1 / 20 := by
    have hexp1 : Real.exp (-(⌊Y * x ^ 2⌋₊ : ℝ) / Y) ≤ Real.exp (1 - x ^ 2) := by
      apply Real.exp_le_exp.mpr
      have h2 := neg_le_neg hML
      simp only [neg_sub] at h2
      rwa [neg_div]
    have hY1' : 0 ≤ 2 * (Y + 1) := by positivity
    have h1 : 2 * (Y + 1) * Real.exp (-(⌊Y * x ^ 2⌋₊ : ℝ) / Y)
        ≤ 2 * (Y + 1) * Real.exp (1 - x ^ 2) :=
      mul_le_mul_of_nonneg_left hexp1 hY1'
    have h2 : 2 * (Y + 1) * Real.exp (1 - x ^ 2) ≤ 4 * Real.exp (2 * x + 1 - x ^ 2) := by
      have h4 : 2 * (Y + 1) ≤ 4 * Real.exp (2 * x) := by
        have h5 : (1 : ℝ) ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
        linarith
      calc 2 * (Y + 1) * Real.exp (1 - x ^ 2)
          ≤ 4 * Real.exp (2 * x) * Real.exp (1 - x ^ 2) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
        _ = 4 * (Real.exp (2 * x) * Real.exp (1 - x ^ 2)) := by ring
        _ = 4 * Real.exp (2 * x + (1 - x ^ 2)) := by rw [← Real.exp_add]
        _ = 4 * Real.exp (2 * x + 1 - x ^ 2) := by
            congr 1
            ring
    have htail : 2 * x + 1 - x ^ 2 ≤ -7 := by nlinarith
    have h6 : Real.exp (2 * x + 1 - x ^ 2) ≤ Real.exp (-7) := Real.exp_le_exp.mpr htail
    have he6 : 4 * Real.exp (-7) ≤ 1 / 20 := by
      have h2 : Real.exp 7 = (Real.exp 1) ^ 7 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : (2 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := by
        gcongr
        exact Real.exp_one_gt_two.le
      have h4 : (128 : ℝ) ≤ Real.exp 7 := by
        rw [h2]
        norm_num at h3 ⊢
        linarith
      rw [Real.exp_neg]
      rw [show (4 : ℝ) * (Real.exp 7)⁻¹ = 4 / Real.exp 7 by ring]
      rw [div_le_iff₀ (Real.exp_pos 7)]
      linarith
    linarith [h1, h2, h6, he6]
  calc ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖
      = ‖detFarTail K Y (Y * x ^ 2) ρ‖ := by rw [hxdef]
    _ ≤ 1 / 20 := le_trans hfar hbound

/-- **Sharp vertical upper bound for `Γ` on the strip `1/2 ≤ Re ≤ 2`, explicit constant.** -/
lemma gamma_sharp_strip (u v : ℝ) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 2) :
    ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |v|) := by
  have hlog := Commons.Analysis.SpecialFunctions.Gamma.log_Gamma_vertical_le u v h1 (by linarith)
  have hpos : 0 < ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ := by
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [Complex.add_re, Complex.mul_re]
    linarith
  have hv1 : (0 : ℝ) < 1 + |v| := by positivity
  have hle : 4 + 2 * |v| ≤ 4 * (1 + |v|) := by
    have := abs_nonneg v
    linarith
  have hexp : Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|))
      = (4 + 2 * |v|) ^ (u - 1 / 2) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    ring_nf
  have h4 : (4 + 2 * |v|) ^ (u - 1 / 2) ≤ (4 * (1 + |v|)) ^ (u - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) hle (by linarith)
  have h5 : (4 * (1 + |v|)) ^ (u - 1 / 2)
      = 4 ^ (u - 1 / 2) * (1 + |v|) ^ (u - 1 / 2) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have h6 : (4 : ℝ) ^ (u - 1 / 2) ≤ 8 := by
    calc (4 : ℝ) ^ (u - 1 / 2) ≤ (4 : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have hpow_nn : 0 ≤ (1 + |v|) ^ (u - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have h1' : Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1)
      ≤ 8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) := by
    have h7 : (4 + 2 * |v|) ^ (u - 1 / 2) ≤ 8 * (1 + |v|) ^ (u - 1 / 2) := by
      calc (4 + 2 * |v|) ^ (u - 1 / 2) ≤ (4 * (1 + |v|)) ^ (u - 1 / 2) := h4
        _ = 4 ^ (u - 1 / 2) * (1 + |v|) ^ (u - 1 / 2) := h5
        _ ≤ 8 * (1 + |v|) ^ (u - 1 / 2) := mul_le_mul_of_nonneg_right h6 hpow_nn
    calc Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1)
        = Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|)) * Real.exp 1 := Real.exp_add _ _
      _ = (4 + 2 * |v|) ^ (u - 1 / 2) * Real.exp 1 := by rw [hexp]
      _ ≤ (8 * (1 + |v|) ^ (u - 1 / 2)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h7 (Real.exp_pos 1).le
      _ = 8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) := by ring
  rw [← Real.exp_log hpos]
  refine le_trans (Real.exp_le_exp.mpr hlog) ?_
  rw [show (u - 1 / 2) * Real.log (4 + 2 * |v|) + 1 - (Real.pi / 2) * |v|
      = ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1) + (-((Real.pi / 2) * |v|)) by ring,
    Real.exp_add]
  calc Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1) * Real.exp (-((Real.pi / 2) * |v|))
      ≤ (8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2)) * Real.exp (-((Real.pi / 2) * |v|)) :=
        mul_le_mul_of_nonneg_right h1' (Real.exp_nonneg _)
    _ = 8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |v|) := by ring

/-- **The residue of the `ζ`-pole is small, in the wide range `K ≤ T^4`, `Y ≤ (A T)^2`, `A ≥ 6`.** -/
theorem residueTermSmallBig :
    ∀ (A : ℝ), 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        ‖residueTerm K Y ρ‖ ≤ 1 / 20 := by
  intro A hA T hT K Y hK1 hKT hY1 hYT ρ hρ1 hρ2 hγ hlog
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  set x : ℝ := Real.log (A * T) with hxdef
  have hxT : x ^ 2 ≤ T := by rw [hxdef]; exact le_trans hlog hγ
  have hx4 : 4 ≤ x := by
    rw [hxdef]
    exact log_AT_ge_four hA hT (by rw [← hxdef]; exact hxT)
  have hxpos : 0 < x := by linarith
  have hlogT_le : Real.log T ≤ x := by
    have h1 : Real.log T ≤ Real.log (A * T) := Real.log_le_log hTpos (by nlinarith)
    rwa [← hxdef] at h1
  have him1 : 1 ≤ |ρ.im| := by nlinarith [hlog, hx4, sq_nonneg x]
  have himpos : 0 < |ρ.im| := by linarith
  have hne1 : (1 : ℂ) - ρ ≠ 0 := by
    intro h
    have h0 : ((1 : ℂ) - ρ).im = 0 := by rw [h]; simp
    simp at h0
    rw [h0, abs_zero] at him1
    norm_num at him1
  have hGam : Complex.Gamma (1 - ρ) = Complex.Gamma (2 - ρ) / (1 - ρ) := by
    have h := Complex.Gamma_add_one (1 - ρ) hne1
    rw [show (1 - ρ) + 1 = 2 - ρ by ring] at h
    rw [eq_div_iff hne1, h]
    ring
  have hΓ2 : ‖Complex.Gamma (2 - ρ)‖
      ≤ 8 * Real.exp 1 * (1 + |ρ.im|) ^ ((2 - ρ.re) - 1 / 2)
        * Real.exp (-(Real.pi / 2) * |ρ.im|) := by
    have h := gamma_sharp_strip (2 - ρ.re) (-ρ.im) (by linarith) (by linarith)
    have harg : ((2 - ρ.re : ℝ) : ℂ) + ((-ρ.im : ℝ) : ℂ) * Complex.I = 2 - ρ := by
      apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
    rw [← harg]
    simpa [abs_neg] using h
  have hΓ1 : ‖Complex.Gamma (1 - ρ)‖ ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * |ρ.im|) := by
    have hnorm : ‖Complex.Gamma (1 - ρ)‖ = ‖Complex.Gamma (2 - ρ)‖ / ‖(1 : ℂ) - ρ‖ := by
      rw [hGam, norm_div]
    have hden : |ρ.im| ≤ ‖(1 : ℂ) - ρ‖ := by
      have h : |(((1 : ℂ) - ρ)).im| ≤ ‖(1 : ℂ) - ρ‖ := Complex.abs_im_le_norm _
      simpa using h
    have hpow : (1 + |ρ.im|) ^ ((2 - ρ.re) - 1 / 2) ≤ 1 + |ρ.im| := by
      have h1 : (2 - ρ.re) - 1 / 2 ≤ 1 := by linarith [hρ1]
      calc (1 + |ρ.im|) ^ ((2 - ρ.re) - 1 / 2) ≤ (1 + |ρ.im|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) h1
        _ = 1 + |ρ.im| := Real.rpow_one _
    have hstep : ‖Complex.Gamma (2 - ρ)‖
        ≤ 8 * Real.exp 1 * (1 + |ρ.im|) * Real.exp (-(Real.pi / 2) * |ρ.im|) :=
      le_trans hΓ2 (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (Real.exp_nonneg _))
    have h2 : ‖Complex.Gamma (2 - ρ)‖ / ‖(1 : ℂ) - ρ‖ ≤
        (8 * Real.exp 1 * (1 + |ρ.im|) * Real.exp (-(Real.pi / 2) * |ρ.im|)) / |ρ.im| := by
      apply div_le_div₀ (by positivity) hstep (by positivity)
      simpa [Complex.norm_def] using hden
    have h3 : (8 * Real.exp 1 * (1 + |ρ.im|) * Real.exp (-(Real.pi / 2) * |ρ.im|)) / |ρ.im|
        ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * |ρ.im|) := by
      rw [div_le_iff₀ himpos]
      have hE : 0 < Real.exp (-(Real.pi / 2) * |ρ.im|) := Real.exp_pos _
      have he1 : 0 < Real.exp 1 := Real.exp_pos 1
      have h4 : (1 + |ρ.im|) ≤ 2 * |ρ.im| := by linarith
      have h5 : 8 * Real.exp 1 * (1 + |ρ.im|) ≤ 16 * Real.exp 1 * |ρ.im| := by nlinarith [h4, he1]
      calc 8 * Real.exp 1 * (1 + |ρ.im|) * Real.exp (-(Real.pi / 2) * |ρ.im|)
          = (8 * Real.exp 1 * (1 + |ρ.im|)) * Real.exp (-(Real.pi / 2) * |ρ.im|) := by ring
        _ ≤ (16 * Real.exp 1 * |ρ.im|) * Real.exp (-(Real.pi / 2) * |ρ.im|) :=
            mul_le_mul_of_nonneg_right h5 hE.le
        _ = 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * |ρ.im|) * |ρ.im| := by ring
    calc ‖Complex.Gamma (1 - ρ)‖ = ‖Complex.Gamma (2 - ρ)‖ / ‖(1 : ℂ) - ρ‖ := hnorm
      _ ≤ (8 * Real.exp 1 * (1 + |ρ.im|) * Real.exp (-(Real.pi / 2) * |ρ.im|)) / |ρ.im| := h2
      _ ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * |ρ.im|) := h3
  have hYnorm : ‖(Y : ℂ) ^ (1 - ρ)‖ = Y ^ (1 - ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp
  have hYpow : Y ^ (1 - ρ.re) ≤ Real.exp x := by
    have h1 : 1 - ρ.re ≤ 1 / 2 := by linarith
    have h2 : Y ^ (1 - ρ.re) ≤ ((A * T) ^ 2) ^ (1 - ρ.re) :=
      Real.rpow_le_rpow (le_of_lt hYpos) hYT (by linarith : (0 : ℝ) ≤ 1 - ρ.re)
    have h3 : ((A * T) ^ 2) ^ (1 - ρ.re) ≤ ((A * T) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [hApos, hTpos]) h1
    have h4 : ((A * T) ^ 2 : ℝ) ^ (1 / 2 : ℝ) = A * T := by
      rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ A * T)]
      norm_num
    have h5 : A * T ≤ Real.exp x := by
      rw [hxdef, Real.exp_log (by positivity : (0 : ℝ) < A * T)]
    linarith [h2, h3, h4.le, h4.ge, h5]
  have hMK : ‖MK K 1‖ ≤ 1 + 4 * x := by
    have h := mkOneNormBound K
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have hlogK : Real.log (K : ℝ) ≤ Real.log (T ^ 4) := Real.log_le_log hKpos hKT
    rw [Real.log_pow] at hlogK
    push_cast at hlogK
    linarith
  have hres : ‖residueTerm K Y ρ‖ ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2)
      * Real.exp x * (1 + 4 * x) := by
    have h_re : ‖residueTerm K Y ρ‖
        = ‖Complex.Gamma (1 - ρ)‖ * ‖(Y : ℂ) ^ (1 - ρ)‖ * ‖MK K 1‖ := by
      rw [residueTerm, norm_mul, norm_mul]
    have hexp_le : Real.exp (-(Real.pi / 2) * |ρ.im|) ≤ Real.exp (-(Real.pi / 2) * x ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      nlinarith [hlog]
    have h1 : ‖Complex.Gamma (1 - ρ)‖ * ‖(Y : ℂ) ^ (1 - ρ)‖ ≤
        (16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2)) * Real.exp x := by
      rw [hYnorm]
      refine mul_le_mul ?_ hYpow (by positivity) (by positivity)
      calc ‖Complex.Gamma (1 - ρ)‖ ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * |ρ.im|) := hΓ1
        _ ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
    calc ‖residueTerm K Y ρ‖
        = ‖Complex.Gamma (1 - ρ)‖ * ‖(Y : ℂ) ^ (1 - ρ)‖ * ‖MK K 1‖ := h_re
      _ ≤ (16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x) * (1 + 4 * x) :=
          mul_le_mul h1 hMK (norm_nonneg _) (by positivity)
      _ = 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x * (1 + 4 * x) := by ring
  have hlin : 1 + 4 * x ≤ 2 * Real.exp x := by
    have h1 : Real.exp x = (Real.exp (x / 4)) ^ 4 := by
      rw [show (Real.exp (x / 4)) ^ 4
          = Real.exp (x / 4) * Real.exp (x / 4) * Real.exp (x / 4) * Real.exp (x / 4) by ring]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h2 : 1 + x / 4 ≤ Real.exp (x / 4) := by
      have := Real.add_one_le_exp (x / 4)
      linarith
    have h3 : (1 + x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + x / 4) h2 4
    have hu1 : (1 : ℝ) ≤ x / 4 := by linarith
    have h4 : 4 * x ≤ (1 + x / 4) ^ 4 := by
      have hsq : 4 * (x / 4) ≤ (1 + x / 4) ^ 2 := by nlinarith [sq_nonneg (x / 4 - 1)]
      have h2' : (4 * (x / 4)) ^ 2 ≤ ((1 + x / 4) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hsq 2
      have h3' : (4 * (x / 4)) ^ 2 ≤ (1 + x / 4) ^ 4 := by
        have h := h2'
        rw [show ((1 + x / 4) ^ 2) ^ 2 = (1 + x / 4) ^ 4 by ring] at h
        exact h
      have h4' : 16 * (x / 4) ≤ (4 * (x / 4)) ^ 2 := by nlinarith [hu1]
      nlinarith [h3', h4']
    have h5 : 4 * x ≤ Real.exp x := by rw [h1]; linarith
    linarith [h5, hx4]
  have hfin : 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x * (1 + 4 * x)
      ≤ 1 / 20 := by
    have hexp17 : Real.exp (-(Real.pi / 2) * x ^ 2 + 2 * x) ≤ Real.exp (-16) := by
      apply Real.exp_le_exp.mpr
      have h1 : (0 : ℝ) ≤ x - 4 := by linarith
      have h2 : (0 : ℝ) ≤ (Real.pi / 2) * (x + 4) - 2 := by
        nlinarith [Real.pi_gt_three, hx4]
      have h3 : -(Real.pi / 2) * x ^ 2 + 2 * x ≤ -(Real.pi / 2) * 16 + 8 := by
        nlinarith [mul_nonneg h1 h2]
      have h4 : -(Real.pi / 2) * 16 + 8 ≤ -16 := by nlinarith [Real.pi_gt_three]
      linarith
    have hstep : 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x * (1 + 4 * x)
        ≤ 16 * Real.exp 1 * 2 * Real.exp (-(Real.pi / 2) * x ^ 2 + 2 * x) := by
      have h9 : Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x * Real.exp x
          = Real.exp (-(Real.pi / 2) * x ^ 2 + 2 * x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x * (1 + 4 * x)
          ≤ 16 * Real.exp 1 * Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x
              * (2 * Real.exp x) := by
            apply mul_le_mul_of_nonneg_left hlin
            positivity
        _ = 16 * Real.exp 1 * 2 * (Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp x * Real.exp x) := by
            ring
        _ = 16 * Real.exp 1 * 2 * Real.exp (-(Real.pi / 2) * x ^ 2 + 2 * x) := by rw [h9]
    have hlast : 16 * Real.exp 1 * 2 * Real.exp (-16) ≤ 1 / 20 := by
      have he16 : 0 < Real.exp 16 := Real.exp_pos 16
      have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      have h216 : (1920 : ℝ) ≤ Real.exp 16 := by
        have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 16 by norm_num) 5
        have hsum : (1920 : ℝ) ≤ ∑ k ∈ Finset.range 5, (16 : ℝ) ^ k / (k.factorial : ℝ) := by
          simp [Finset.sum_range_succ]
          norm_num
        linarith
      have heq : 16 * Real.exp 1 * 2 * Real.exp (-16) = 32 * Real.exp 1 / Real.exp 16 := by
        rw [Real.exp_neg]
        field_simp
        ring
      rw [heq, div_le_iff₀ he16]
      norm_num at h216
      nlinarith [h216, he1, he16]
    have hmid : 16 * Real.exp 1 * 2 * Real.exp (-(Real.pi / 2) * x ^ 2 + 2 * x)
        ≤ 16 * Real.exp 1 * 2 * Real.exp (-16) :=
      mul_le_mul_of_nonneg_left hexp17 (by positivity)
    linarith [hstep, hmid, hlast]
  linarith [hres, hfin]

theorem zetaCriticalLineBoundExplicit :
    ∃ C : ℝ, 0 < C ∧ C ≤ 9000000 ∧ ∀ τ : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (3 + |τ|) ^ 4 := by
  refine ⟨8, by norm_num, by norm_num, ?_⟩
  intro τ
  set s : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = τ := by simp [hs]
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈|τ|⌉₊ + 1 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hNdef]; omega
  have hNs : (|τ| : ℝ) ≤ (N : ℝ) := by
    rw [hNdef]; push_cast
    exact le_trans (Nat.le_ceil (|τ|)) (by linarith)
  have hNup : (N : ℝ) ≤ |τ| + 2 := by
    rw [hNdef]; push_cast
    have := Nat.ceil_lt_add_one (abs_nonneg τ)
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    norm_num at this
  have hs0 : 0 < s.re := by rw [hsre]; norm_num
  have hemN := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hs1 N hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- (a) the finite sum
  have hsum : ‖∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))‖ ≤ 2 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hpw : ∀ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℕ) < n := by omega
      rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re, hsre]
    rw [Finset.sum_congr rfl hpw]
    exact Work.Sieve.sum_Icc_rpow_neg_half_le N hN1
  -- (b) the pole term
  have hsinorm : ‖s - 1‖ ^ 2 = 1 / 4 + τ ^ 2 := by
    have h1 : (s - 1).re = -(1 / 2) := by rw [Complex.sub_re, hsre]; norm_num
    have h2 : (s - 1).im = τ := by rw [Complex.sub_im, Complex.one_im, hsim]; ring
    rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
    ring
  have hmid : ‖(((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ ≤ 4 := by
    have h1 : ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ = (N : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega : (0 : ℕ) < N)]
      have : (1 - s).re = 1 / 2 := by rw [Complex.sub_re, Complex.one_re, hsre]; norm_num
      rw [this]
    rw [norm_div, h1]
    have hden : 0 < ‖s - 1‖ := by
      have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      simpa using norm_pos_iff.mpr this
    rw [div_le_iff₀ hden]
    have hsq : (N : ℝ) ≤ (4 * ‖s - 1‖) ^ 2 := by
      rw [show (4 * ‖s - 1‖) ^ 2 = 16 * ‖s - 1‖ ^ 2 by ring, hsinorm]
      nlinarith [hNup, abs_nonneg τ, sq_nonneg τ, le_abs_self τ, neg_abs_le τ, sq_abs τ]
    rw [show (N : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (N : ℝ) from (Real.sqrt_eq_rpow N).symm,
      Real.sqrt_le_iff]
    exact ⟨by positivity, hsq⟩
  -- (c) the Euler–Maclaurin tail
  have htail : ‖∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
      (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖
      ≤ 2 * (1 + |τ|) := by
    have hem := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN1 s hs0 hs1
    refine le_trans (norm_tsum_le_tsum_norm hem.1.norm) ?_
    refine le_trans hem.2 ?_
    have hsnorm : ‖s‖ ≤ 1 + |τ| := by
      have h : ‖s‖ ^ 2 = 1 / 4 + τ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [hs, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
        ring
      nlinarith [h, sq_nonneg τ, abs_nonneg τ, sq_abs τ]
    have hspos : 0 < s.re := hs0
    have hNroot : (N : ℝ) ^ (-s.re) ≤ 1 := by
      rw [hsre]
      calc (N : ℝ) ^ (-(1 / 2) : ℝ) ≤ (N : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
        _ = 1 := Real.rpow_zero _
    have hcoef : ‖s‖ / s.re ≤ 2 * (1 + |τ|) := by
      have h2 : ‖s‖ / s.re = 2 * ‖s‖ := by rw [hsre, one_div, div_inv_eq_mul]; ring
      rw [h2]
      linarith [hsnorm]
    calc (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) ≤ (2 * (1 + |τ|)) * (N : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hNpos.le _)
      _ ≤ (2 * (1 + |τ|)) * 1 := by
          have hpos2 : (0 : ℝ) ≤ 2 * (1 + |τ|) := by positivity
          nlinarith [hNroot, hpos2]
      _ = 2 * (1 + |τ|) := by ring
  -- assemble
  have hb1 : 2 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 2) ≤ 2 * (3 + |τ|) := by
    have h : ((N : ℝ) + 1) ^ ((1 : ℝ) / 2) ≤ 3 + |τ| := by
      have h2 : (N : ℝ) + 1 ≤ |τ| + 3 := by linarith
      calc ((N : ℝ) + 1) ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) + 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = (N : ℝ) + 1 := Real.rpow_one _
        _ ≤ 3 + |τ| := by linarith
    linarith
  have hkey : ‖riemannZeta s‖ ≤ 2 * (3 + |τ|) + 4 + 2 * (1 + |τ|) := by
    rw [hemN]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    nlinarith [hsum, hb1, hmid, htail]
  have hfin : 2 * (3 + |τ|) + 4 + 2 * (1 + |τ|) ≤ 8 * (3 + |τ|) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 3 + |τ| := by linarith [abs_nonneg τ]
    have habs : |τ| ≤ 3 + |τ| := by linarith [abs_nonneg τ]
    have hx4 : (3 + |τ|) ≤ (3 + |τ|) ^ 4 := by
      have h := pow_le_pow_right₀ h1 (by norm_num : (1 : ℕ) ≤ 4)
      simpa using h
    have hlin : 2 * (3 + |τ|) + 4 + 2 * (1 + |τ|) ≤ 4 * (3 + |τ|) + 4 := by linarith
    have hlin2 : 4 * (3 + |τ|) + 4 ≤ 8 * (3 + |τ|) := by linarith
    have hx8 : 8 * (3 + |τ|) ≤ 8 * (3 + |τ|) ^ 4 := by linarith [hx4]
    linarith
  have hkey' : ‖riemannZeta ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖
      ≤ 2 * (3 + |τ|) + 4 + 2 * (1 + |τ|) := by
    rw [← hs]
    exact hkey
  linarith [hkey', hfin]

/-! ## The numerical bookkeeping of the detector -/

/-- **The assembly of Montgomery's detector.**  From the Perron identity, the contour shift, the
splitting of the detector sum and the three smallness estimates (far tail, residue, critical-line
tails) the disjunction of alternatives follows.  This is the bookkeeping of
`Work.ZeroDensity.Ingham.zetaDetector12`'s private `assembly_step`, restated with the *tail*
estimate as an explicit hypothesis so that it can be instantiated with the wide-range
`critTailSmallBig`. -/
lemma assemblyStepWide (T : ℝ) (hT : 2 ≤ T) (K : ℕ) (Y : ℝ) (ρ : ℂ) (A : ℝ)
    (hA : 6 ≤ A) (hY1 : 1 ≤ Y)
    (hfar : ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ ≤ 1 / 20)
    (hres : ‖residueTerm K Y ρ‖ ≤ 1 / 20)
    (hcrit : Y ^ (1 / 2 - ρ.re) * ((∫ v in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ v)
          + (∫ v in Set.Iic (-(A * Real.log (A * T))), critIntegrand K ρ v)) ≤ Real.pi / 10)
    (hline : Integrable (fun t : ℝ =>
        perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)))
    (hperron : detSum K Y ρ = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I))
    (hshift : (1 / (2 * Real.pi)) * (∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I))
        = residueTerm K Y ρ + (1 / (2 * Real.pi)) *
            (∫ t : ℝ, perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)))
    (hsplit : detSum K Y ρ = ((Real.exp (-(1 / Y)) : ℝ) : ℂ)
        + detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
        + detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ) :
    (1 / 12 ≤ ‖detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖)
      ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
            ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)), critIntegrand K ρ v) := by
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  have hH0 : 0 ≤ A * Real.log (A * T) :=
    mul_nonneg hApos.le (Real.log_nonneg (by linarith))
  have hH1 : 1 ≤ A * Real.log (A * T) := by
    have h2 : (1 : ℝ) ≤ Real.log (A * T) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      nlinarith [Real.exp_one_lt_three, hA, hT]
    nlinarith
  rcases lt_or_ge (‖detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖) (1 / 12) with hlt | hge
  · refine Or.inr ?_
    by_contra hcon
    have hcon' : Y ^ (1 / 2 - ρ.re) *
        (∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)), critIntegrand K ρ v) < 1 / 12 :=
      not_le.mp hcon
    -- the middle integral is small
    have hmid : ‖∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
        perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ < 1 / 12 := by
      refine lt_of_le_of_lt ?_ hcon'
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith [hH0])) ?_
      rw [intervalIntegral.integral_congr (fun t _ => norm_perronInt_critLine K Y hYpos ρ t),
        intervalIntegral.integral_const_mul]
    -- the two tails are small
    have htails : ‖∫ t in Set.Ioi (A * Real.log (A * T)),
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
        + ‖∫ t in Set.Iic (-(A * Real.log (A * T))),
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ ≤ Real.pi / 10 := by
      have h1 : ‖∫ t in Set.Ioi (A * Real.log (A * T)),
            perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
          ≤ Y ^ (1 / 2 - ρ.re) * ∫ t in Set.Ioi (A * Real.log (A * T)),
              critIntegrand K ρ t := by
        refine le_trans (norm_integral_le_integral_norm _) ?_
        rw [show (∫ t in Set.Ioi (A * Real.log (A * T)),
              ‖perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖)
            = ∫ t in Set.Ioi (A * Real.log (A * T)),
                Y ^ (1 / 2 - ρ.re) * critIntegrand K ρ t from
            setIntegral_congr_fun measurableSet_Ioi
              (fun t _ => norm_perronInt_critLine K Y hYpos ρ t)]
        exact le_of_eq (integral_const_mul _ _)
      have h2 : ‖∫ t in Set.Iic (-(A * Real.log (A * T))),
            perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
          ≤ Y ^ (1 / 2 - ρ.re) * ∫ t in Set.Iic (-(A * Real.log (A * T))),
              critIntegrand K ρ t := by
        refine le_trans (norm_integral_le_integral_norm _) ?_
        rw [show (∫ t in Set.Iic (-(A * Real.log (A * T))),
              ‖perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖)
            = ∫ t in Set.Iic (-(A * Real.log (A * T))),
                Y ^ (1 / 2 - ρ.re) * critIntegrand K ρ t from
            setIntegral_congr_fun measurableSet_Iic
              (fun t _ => norm_perronInt_critLine K Y hYpos ρ t)]
        exact le_of_eq (integral_const_mul _ _)
      linarith
    -- so the full line integral is `≤ 1/12 + π/10`
    have hIcrit : ‖∫ t : ℝ,
        perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
        ≤ 1 / 12 + Real.pi / 10 := by
      rw [integral_eq_Ioc_add_tails hline hH0]
      have hAi : ‖∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ < 1 / 12 := hmid
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      linarith [hAi.le, htails]
    have hIcrit' : ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))‖
        ≤ (1 / (2 * Real.pi)) * (1 / 12 + Real.pi / 10) := by
      have hcast : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
        push_cast
        ring
      have hcn : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hcast, norm_mul, hcn]
      exact mul_le_mul_of_nonneg_left hIcrit (by positivity)
    have hdet : ‖detSum K Y ρ‖ ≤ 1 / 20 + (1 / (2 * Real.pi)) * (1 / 12 + Real.pi / 10) := by
      rw [hperron, hshift]
      refine le_trans (norm_add_le _ _) ?_
      linarith [hres, hIcrit']
    have hexpbd : Real.exp (-(1 / Y)) ≤ 3 / 20 + 1 / (24 * Real.pi) + 1 / 12 := by
      have hnorm : Real.exp (-(1 / Y)) = ‖((Real.exp (-(1 / Y)) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hrepr : ((Real.exp (-(1 / Y)) : ℝ) : ℂ)
          = detSum K Y ρ - detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
            - detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ := by
        rw [hsplit]
        ring
      have harith : (1 / (2 * Real.pi)) * (1 / 12 + Real.pi / 10) = 1 / (24 * Real.pi) + 1 / 20 := by
        field_simp
        ring
      rw [hnorm, hrepr]
      have h1 : ‖detSum K Y ρ - detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
            - detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖
          ≤ ‖detSum K Y ρ‖ + ‖detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖
            + ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        exact add_le_add (norm_sub_le _ _) le_rfl
      linarith [h1, hdet, hlt.le, hfar, harith.le]
    have hge1 : Real.exp (-1) ≤ Real.exp (-(1 / Y)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      simpa using one_div_le_one_div_of_le (zero_lt_one) hY1
    linarith [hge1, hexpbd, detector_error_lt_exp_neg_one]
  · exact Or.inl hge

/-- **The wide zero detector**, obtained by instantiating the assembly with the three
smallness estimates.  The critical-line tail estimate is kept as an explicit hypothesis
(`hcrit`), so that this can be instantiated with the wide-range `critTailSmallBig`. -/
theorem zetaDetectorWide
    (hcrit : ∀ (A : ℝ), 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        Y ^ (1 / 2 - ρ.re) * ((∫ v in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ v)
            + (∫ v in Set.Iic (-(A * Real.log (A * T))), critIntegrand K ρ v)) ≤ Real.pi / 10)
    : ∀ (A : ℝ), 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        (1 / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖)
          ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
              ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
                critIntegrand K ρ v) := by
  intro A hA T hT K Y hK1 hKT hY1 hYT ρ hζ hρ0 hρ1 hγ hlog
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  have hlog1 : (1 : ℝ) ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_three, hA, hT]
  have hZ1 : 1 ≤ Y * (Real.log (A * T)) ^ 2 := by nlinarith
  have him1 : 1 ≤ |ρ.im| := by nlinarith [hlog, hlog1]
  have himne : ρ.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him1
    norm_num at him1
  have hρne1 : ρ ≠ 1 := by
    intro h
    apply himne
    rw [h]
    simp
  have hline := perronIntIntegrableSelf K Y hYpos ρ hζ hρne1 (c := (1 / 2 : ℝ) - ρ.re)
    (by linarith) (by linarith)
    (by intro h; rw [Complex.sub_re, Complex.one_re] at h; linarith)
    (by linarith) (by linarith)
  have hperron := zetaPerronIdentity K Y hYpos ρ (by linarith)
  have hshift := perronShiftOne K Y hYpos ρ hζ hρ0 hρ1 hρne1
  have hsplit := detSumSplit K Y (Y * (Real.log (A * T)) ^ 2) hYpos hK1 hZ1 ρ
  have hfar := detFarTailSmallBig A hA T hT K Y hK1 hKT hY1 hYT ρ hρ0 hρ1 hγ hlog
  have hres := residueTermSmallBig A hA T hT K Y hK1 hKT hY1 hYT ρ hρ0 hρ1 hγ hlog
  have hct := hcrit A hA T hT K Y hK1 hKT hY1 hYT ρ hρ0 hρ1 hγ hlog
  rcases assemblyStepWide T hT K Y ρ A hA hY1 hfar hres hct hline hperron hshift hsplit with h | h
  · exact Or.inl (by simpa only [detTail] using h)
  · exact Or.inr h

/-- **The wide zero detector, unconditional**: `zetaDetectorWide` instantiated with the
critical-line tail estimate `Work.ZeroDensity.Ingham.zetaDetectorBig.critTailSmallBig`. -/
theorem zetaDetectorBigAll :
    ∀ (A : ℝ), 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        (1 / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖)
          ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
              ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
                critIntegrand K ρ v) :=
  zetaDetectorWide Work.ZeroDensity.Ingham.zetaDetectorBig.critTailSmallBig

/-! ## Reduction of the target to two inputs -/

/-- **Reduction of `zetaCountCombinedClean` to the wide detector's tail estimate and the
contour-integral count.**  The cut-off split, the low zeros and the two large-values counts are
all handled by `zetaCountCombined_of_pieces`; the only inputs are `hcrit` (the critical-line tail
estimate, being proved as `zetaDetectorBig.critTailSmallBig`) and `hint` (the contour-integral
count). -/
theorem zetaCountCombinedClean_of_pieces (A : ℝ) (hA : 6 ≤ A)
    (hcrit : ∀ (A' : ℝ), 6 ≤ A' → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A' * T) ^ 2 →
      ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A' * T)) ^ 2 ≤ |ρ.im| →
        Y ^ (1 / 2 - ρ.re) * ((∫ v in Set.Ioi (A' * Real.log (A' * T)), critIntegrand K ρ v)
            + (∫ v in Set.Iic (-(A' * Real.log (A' * T))), critIntegrand K ρ v)) ≤ Real.pi / 10)
    (hint : ∀ A' : ℝ, 6 ≤ A' → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ),
      1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A' * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (∀ z ∈ R, (1 : ℝ) / 12 ≤ Y ^ (1 / 2 - z.re) *
            ∫ v in (-(A' * Real.log (A' * T)))..(A' * Real.log (A' * T)),
              ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                * ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                * ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) →
          (R.card : ℝ) ≤ C * T ^ ε *
            (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)))
    : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (R.card : ℝ) ≤ C * T ^ ε *
            ((Real.log (A * T)) ^ 2 + Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)
              + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3)
                  * Y ^ ((2 - 4 * σ) / 3)) :=
  zetaCountCombined_of_pieces (zetaDetectorWide hcrit) zetaTailCountEtaSelf hint A hA

/-- The combined large-values count of Montgomery's argument for `ζ` (Montgomery–Vaughan §28.4.1: the tail count, the contour-integral count and the count of the small-height zeros combined), cleaned of the `sorry` in `Submission/Work/ZeroDensity/Ingham/zetaCountCombined.lean` (same statement there): for every truncation parameter `A ≥ 6` and every `ε > 0` there is `C > 0` such that for every `σ ∈ [1/2,1]`, every `T ≥ 2`, every `K ≥ 1` and every `Y` with `1 ≤ Y ≤ (A T)²`, every `1`-separated finite set `R` of zeros of the completed `ζ` in the box `σ ≤ Re ≤ 1`, `|Im| ≤ T` satisfies

`#R ≤ C T^ε ( (log (A T))² + Y^{2-2σ} + (A T) K^{1-2σ} + T^{1/3} (T+K)^{2/3} Y^{(2-4σ)/3} )`.

To be proved `sorry`-free.  Structure already in the workspace: the same file's `zetaCountCombined_of_pieces` is fully proved and reduces this to Montgomery's ζ zero-detector `Work.ZeroDensity.Ingham.zetaDetector12`, the tail count `Work.ZeroDensity.Ingham.zetaTailCountEta` and the contour-integral count `Work.ZeroDensity.Ingham.zetaIntegralCount`.  Those three, and their own transitive dependencies, are where `sorryAx` enters today: `zetaDetector12.lean` (through `critTailNumeric`, `integral_Ioi_polyexp_le`, `perronH_differentiable`, `perronH_horizontal`, `perronInt_integrable`, `vertical_shift_patched_pole`), `zetaIntegralCount.lean` (its own statement), and `zetaTailCountEta.lean` (through `zetaTailTermLogWeightBound`).  The `zetaIntegralCountPieceSelf`/`zetaTailCountEtaSelf` family of variants in the same directory stages the intended proofs of those two counts, and the detector's perron/contour toolkit is present; filling those `sorry`s (or proving the two counts and the detector directly) is the whole task. -/
theorem zetaCountCombinedClean (A : ℝ) (hA : 6 ≤ A) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (R.card : ℝ) ≤ C * T ^ ε *
            ((Real.log (A * T)) ^ 2 + Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)
              + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3)
                  * Y ^ ((2 - 4 * σ) / 3)) :=
  zetaCountCombinedClean_of_pieces A hA
    Work.ZeroDensity.Ingham.zetaDetectorBig.critTailSmallBig
    Work.ZeroDensity.Ingham.zetaDetectorBig.zetaIntegralCountWide

end Work.ZeroDensity.Ingham
