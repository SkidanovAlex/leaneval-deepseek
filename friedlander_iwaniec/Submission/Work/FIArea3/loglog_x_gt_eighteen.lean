/-
# `Work.FIArea3.loglog_x_gt_eighteen`

The numeric consequence of the non-emptiness of the `β`-box used all over area 3 of the FI
contract: with `u = θ√N ≥ 1/10` (the paper's `u ≍ θ√N` is `≥ 0.16`; the constant `1/10` is the
workspace's), the parameters of `(4.4)`–`(4.19)` force `loglog x > 18`, i.e. `x > e^{e^{18}}`.

The mathematics is the remark of `FIArea3/NOTES.md` §(defect 5)/(5.2.5): from `1/10 ≤ θ√N`, the
upper end `N < x^{1/2}(log x)^{-B}` of the range `(4.6)`, the definition `θ = (log x)^{-A'}`
(`4.15`) and the paper's §18 choice `A' ≥ 2^{20}` (`(10.12)`),

  `(2^{20})·loglog x < log 10 + (log x)/4`.

So `log x ≥ 4·2^{20}·loglog x`, and since `4·2^{20}·log t > t/4 + log 10` for every
`t ∈ [log 3, e^{18}]` (a one-line chord argument: `t ↦ 2^{20} log t − t/4 − log 10` is concave on
`t > 0` and positive at `t = log 3` — value `≳ 9.8·10^4` — and at `t = e^{18}` — value `≳ 2.4·10^6`),
the inequality is impossible unless `loglog x > 18`.

The file is self-contained: the only inputs are Mathlib's `Real.log`/`Real.exp` bounds
(`Real.log_three_gt_d9`, `Real.exp_one_lt_d9`, `Real.one_sub_inv_le_log_of_pos`) and the weighted
AM–GM inequality (`Real.geom_mean_le_arith_mean2_weighted`).
-/
import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea3

/-- **From the parameters to the basic inequality on `loglog x`.**

`1/10 ≤ θ√N` together with `N < x^{1/2}(log x)^{-B}` gives, since `(log x)^{-B} < 1`,

  `1/10 < θ x^{1/4} = (log x)^{-A'} x^{1/4}`,

and taking logarithms of the two sides (`log (1/10) = -log 10`):

  `A'·loglog x < log 10 + (log x)/4`.

With `A' ≥ 2^{20}` and `loglog x > 0` this is
`2^{20}·loglog x < log 10 + (log x)/4`. -/
lemma two_pow_twenty_mul_loglog_lt (Pa : Work.FITop.Params)
    (hu : (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N) :
    (2 ^ 20 : ℝ) * Real.log (Real.log (Pa.x : ℝ)) <
      Real.log 10 + Real.log (Pa.x : ℝ) / 4 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlog1 : (1 : ℝ) < Real.log (Pa.x : ℝ) :=
    lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hx3)
  have hlogpos : 0 < Real.log (Pa.x : ℝ) := lt_trans one_pos hlog1
  have hLLpos : 0 < Real.log (Real.log (Pa.x : ℝ)) := Real.log_pos hlog1
  have hA20 : (2 : ℝ) ^ 20 ≤ Pa.A' := by linarith [Pa.hA, Pa.hA']
  -- `(log x)^{-B} < 1`, hence `N < x^{1/2}`
  have hrpow : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hlog1 (by linarith [Pa.hB])
  have hxhalf_pos : (0 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos _
  have hNlt : Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    have hlt : (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B) <
        (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
      simpa using mul_lt_mul_of_pos_left hrpow hxhalf_pos
    exact lt_trans Pa.hNhi hlt
  -- `√N < x^{1/4}`
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hsqrt_lt : Real.sqrt Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.sqrt_lt_sqrt hNpos.le hNlt
    have h2 : Real.sqrt ((Pa.x : ℝ) ^ ((1 : ℝ) / 2)) = (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
      norm_num
    rwa [h2] at h
  -- `1/10 < (log x)^{-A'} x^{1/4}`
  have h5 : (1 / 10 : ℝ) < (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    have hlt : Pa.θ * Real.sqrt Pa.N < Pa.θ * (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      mul_lt_mul_of_pos_left hsqrt_lt Pa.hθ0
    have h := lt_of_le_of_lt hu hlt
    rwa [Pa.hθ] at h
  -- take logarithms
  have hlogineq : Pa.A' * Real.log (Real.log (Pa.x : ℝ)) <
      Real.log 10 + Real.log (Pa.x : ℝ) / 4 := by
    have hXpos : (0 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hxpos _
    have hdpos : (0 : ℝ) < (Real.log (Pa.x : ℝ)) ^ (-Pa.A') := Real.rpow_pos_of_pos hlogpos _
    have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 10) h5
    rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hdpos) (ne_of_gt hXpos),
      Real.log_rpow hlogpos, Real.log_rpow hxpos] at hlog
    linarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hA20 hLLpos.le) hlogineq

/-- **The chord (concavity) step.**  `f(t) = 2^{20}·log t − t/4 − log 10` is concave on
`(0,∞)`; the weighted AM–GM inequality turns this into positivity of `f` on `[log 3, e^{18}]`
from positivity at the two endpoints (which is what `Real.log_three_gt_d9`, `Real.exp_one_lt_d9`
and `Real.one_sub_inv_le_log_of_pos` certify). -/
lemma log_chord_numeric_bound (t : ℝ) (h1 : Real.log 3 ≤ t) (h2 : t ≤ Real.exp 18) :
    t / 4 + Real.log 10 ≤ (2 ^ 20 : ℝ) * Real.log t := by
  have hlog3pos : 0 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlog3lt : Real.log 3 < 1.1 := by linarith [Real.log_three_lt_d9]
  have hlog10le : Real.log 10 ≤ 9 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    linarith
  have hexp18gt : (2 : ℝ) < Real.exp 18 := by
    have h' : Real.exp 1 ≤ Real.exp 18 := Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, h']
  have hexp18pos : 0 < Real.exp 18 := Real.exp_pos 18
  -- value at the left endpoint: `2^{20}·log(log 3) > (log 3)/4 + log 10`
  have hA_end : Real.log 3 / 4 + Real.log 10 < (2 ^ 20 : ℝ) * Real.log (Real.log 3) := by
    have hll_lb : (1 : ℝ) / 100 < Real.log (Real.log 3) := by
      have hll := Real.one_sub_inv_le_log_of_pos hlog3pos
      have hinv : (Real.log 3)⁻¹ ≤ ((1.0986122885 : ℝ))⁻¹ := by
        rw [inv_le_inv₀ hlog3pos (by norm_num)]
        exact le_of_lt Real.log_three_gt_d9
      linarith
    have h1 : (10485 : ℝ) < (2 ^ 20 : ℝ) * Real.log (Real.log 3) := by
      have := mul_lt_mul_of_pos_left hll_lb (by norm_num : (0 : ℝ) < (2 ^ 20 : ℝ))
      norm_num at this ⊢
      linarith
    have h2 : Real.log 3 / 4 + Real.log 10 < 9.3 := by linarith
    linarith
  -- value at the right endpoint: `2^{20}·18 > e^{18}/4 + log 10`
  have hexp18lt : Real.exp 18 < 75497436 := by
    have h1 : Real.exp 18 = (Real.exp 1) ^ 18 := by
      simp [← Real.exp_nat_mul]
    rw [h1]
    have h3 : (Real.exp 1) ^ 18 < (2.7182818286 : ℝ) ^ 18 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have h4 : (2.7182818286 : ℝ) ^ 18 < 75497436 := by
      have hc : (2.7182818286 : ℝ) ^ 2 < 7.4 := by norm_num
      have h5 : ((2.7182818286 : ℝ) ^ 2) ^ 9 < (7.4 : ℝ) ^ 9 :=
        pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
      have h6 : (7.4 : ℝ) ^ 9 < 75497436 := by norm_num
      rw [show (18 : ℕ) = 2 * 9 by norm_num, pow_mul]
      linarith
    linarith
  have hB_end : Real.exp 18 / 4 + Real.log 10 < (2 ^ 20 : ℝ) * 18 := by
    have h : (2 ^ 20 : ℝ) * 18 = 18874368 := by norm_num
    linarith
  -- write `t` as a convex combination `(1-λ)·log 3 + λ·e^{18}`
  set lam := (t - Real.log 3) / (Real.exp 18 - Real.log 3) with hlam
  have hden : 0 < Real.exp 18 - Real.log 3 := by linarith
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg (by linarith) hden.le
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
  have ht_eq : (1 - lam) * Real.log 3 + lam * Real.exp 18 = t := by
    rw [hlam]
    field_simp
    ring
  -- weighted AM–GM (concavity of `log`):
  -- `(log 3)^{1-λ} (e^{18})^λ ≤ (1-λ)log 3 + λ e^{18} = t`
  have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - lam) (w₂ := lam)
    (p₁ := Real.log 3) (p₂ := Real.exp 18) (by linarith) hlam0 hlog3pos.le hexp18pos.le (by ring)
  have hgm' : (Real.log 3) ^ (1 - lam) * (Real.exp 18) ^ lam ≤ t := by
    rw [ht_eq] at hgm
    exact hgm
  have hlog_le : (1 - lam) * Real.log (Real.log 3) + lam * 18 ≤ Real.log t := by
    have hpos : 0 < (Real.log 3) ^ (1 - lam) * (Real.exp 18) ^ lam :=
      mul_pos (Real.rpow_pos_of_pos hlog3pos _) (Real.rpow_pos_of_pos hexp18pos _)
    have hlog := Real.log_le_log hpos hgm'
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hlog3pos _))
        (ne_of_gt (Real.rpow_pos_of_pos hexp18pos _)),
      Real.log_rpow hlog3pos, Real.log_rpow hexp18pos, Real.log_exp] at hlog
    exact hlog
  have hkey : (2 ^ 20 : ℝ) * ((1 - lam) * Real.log (Real.log 3) + lam * 18) ≤
      (2 ^ 20 : ℝ) * Real.log t := mul_le_mul_of_nonneg_left hlog_le (by norm_num)
  have hstep1 : (1 - lam) * (Real.log 3 / 4 + Real.log 10) ≤
      (1 - lam) * ((2 ^ 20 : ℝ) * Real.log (Real.log 3)) :=
    mul_le_mul_of_nonneg_left hA_end.le (by linarith)
  have hstep2 : lam * (Real.exp 18 / 4 + Real.log 10) ≤ lam * ((2 ^ 20 : ℝ) * 18) :=
    mul_le_mul_of_nonneg_left hB_end.le hlam0
  calc t / 4 + Real.log 10
      = (1 - lam) * (Real.log 3 / 4 + Real.log 10) + lam * (Real.exp 18 / 4 + Real.log 10) := by
        rw [← ht_eq]; ring
    _ ≤ (1 - lam) * ((2 ^ 20 : ℝ) * Real.log (Real.log 3)) + lam * ((2 ^ 20 : ℝ) * 18) :=
        add_le_add hstep1 hstep2
    _ = (2 ^ 20 : ℝ) * ((1 - lam) * Real.log (Real.log 3) + lam * 18) := by ring
    _ ≤ (2 ^ 20 : ℝ) * Real.log t := hkey

/-- **`loglog x > 18` for every admissible `Params` with `θ√N ≥ 1/10`.**

`two_pow_twenty_mul_loglog_lt` gives `2^{20} loglog x < log 10 + (log x)/4`; if `loglog x ≤ 18`
then `log x = e^{loglog x} ≤ e^{18}`, and `log x ≥ log 3`, so
`log_chord_numeric_bound` gives the reverse inequality. -/
lemma loglog_x_gt_eighteen (Pa : Work.FITop.Params)
    (hu : (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N) :
    (18 : ℝ) < Real.log (Real.log (Pa.x : ℝ)) := by
  have hkey := two_pow_twenty_mul_loglog_lt Pa hu
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlog1 : (1 : ℝ) < Real.log (Pa.x : ℝ) :=
    lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hx3)
  have hlogxpos : 0 < Real.log (Pa.x : ℝ) := lt_trans one_pos hlog1
  by_contra hcon
  have hcon' : Real.log (Real.log (Pa.x : ℝ)) ≤ 18 := not_lt.mp hcon
  have ht_le : Real.log (Pa.x : ℝ) ≤ Real.exp 18 := by
    have h := Real.exp_le_exp.mpr hcon'
    rwa [Real.exp_log hlogxpos] at h
  have ht_ge : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
  have hnum := log_chord_numeric_bound (Real.log (Pa.x : ℝ)) ht_ge ht_le
  linarith [hkey, hnum]

end Work.FIArea3
