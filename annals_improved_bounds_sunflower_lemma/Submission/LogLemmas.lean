import Mathlib

/-!
# Generic real-log inequalities used in the final assembly
-/
open scoped Real

namespace Submission.LogLemmas

/-- natural log of base-1.9 log: `logb 1.9 w ≥ logb 1.9 2` for `w ≥ 2` -/
lemma logb_ge_of_ge {b x y : ℝ} (hb : 1 < b) (hx : 0 < x) (hxy : x ≤ y) :
    Real.logb b x ≤ Real.logb b y := by
  exact Real.logb_le_logb_of_le hb hx hxy

/-- log is monotone on positives -/
lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

/-- `Real.logb 1.9 2 ≥ 1` (since 2 ≥ 1.9) -/
lemma logb19_two_ge_one : 1 ≤ Real.logb (1.9 : ℝ) 2 := by
  have hcpos : 0 < Real.log (1.9 : ℝ) := Real.log_pos (by norm_num : 1 < (1.9 : ℝ))
  rw [show Real.logb (1.9 : ℝ) 2 = Real.log 2 / Real.log (1.9 : ℝ) by rfl]
  rw [le_div_iff₀ hcpos]
  have hmono : Real.log (1.9 : ℝ) ≤ Real.log 2 :=
    Real.log_le_log (x := (1.9 : ℝ)) (y := (2 : ℝ)) (by norm_num) (by norm_num : (1.9 : ℝ) ≤ 2)
  simpa using hmono

/-- `Real.logb 1.9 2 > 0` -/
lemma logb19_two_pos : 0 < Real.logb (1.9 : ℝ) 2 := by
  linarith [logb19_two_ge_one]

/-- for w ≥ 2: `(w:ℝ) ≥ 2` and helpers -/
lemma nat_two_le_real {w : ℕ} (hw : 2 ≤ w) : (2 : ℝ) ≤ (w : ℝ) := by
  exact_mod_cast hw

/-- w ≥ 2 implies base-1.9 log ≥ log 2 (both positive) -/
lemma logb19_w_ge_logb19_two {w : ℕ} (hw : 2 ≤ w) :
    Real.logb (1.9 : ℝ) 2 ≤ Real.logb (1.9 : ℝ) (w : ℝ) := by
  exact logb_ge_of_ge (b := (1.9 : ℝ)) (x := (2 : ℝ)) (y := (w : ℝ))
    (by norm_num : 1 < (1.9 : ℝ)) (by norm_num : 0 < (2 : ℝ)) (nat_two_le_real hw)

/-- `Real.logb 1.9 2 ≥ 16/15` (so the inner log is comfortably above 1) -/
lemma logb19_two_ge_16div15 : (16 : ℝ) / 15 ≤ Real.logb (1.9 : ℝ) 2 := by
  rw [show Real.logb (1.9 : ℝ) 2 = Real.log 2 / Real.log (1.9 : ℝ) by rfl]
  have hcpos : 0 < Real.log (1.9 : ℝ) := Real.log_pos (by norm_num : 1 < (1.9 : ℝ))
  have hpow2 : Real.log ((2 : ℝ) ^ 15) = (15 : ℝ) * Real.log 2 := Real.log_pow (2 : ℝ) 15
  have hpow19 : Real.log ((1.9 : ℝ) ^ 16) = (16 : ℝ) * Real.log (1.9 : ℝ) :=
    Real.log_pow (1.9 : ℝ) 16
  have hcmp : (1.9 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 15 := by norm_num
  have hmono : Real.log ((1.9 : ℝ) ^ 16) ≤ Real.log ((2 : ℝ) ^ 15) :=
    Real.log_le_log (x := (1.9 : ℝ) ^ 16) (y := (2 : ℝ) ^ 15) (by positivity) hcmp
  rw [hpow19, hpow2] at hmono
  field_simp [hcpos.ne']
  nlinarith

/-- `Real.logb 1.9 (16/15) ≥ 1/20` (since `(16/15)^20 ≥ 1.9`) -/
lemma logb19_16div15_ge_twentieth : (1 : ℝ) / 20 ≤ Real.logb (1.9 : ℝ) ((16 : ℝ) / 15) := by
  have hb : 1 < (1.9 : ℝ) := by norm_num
  have hpowcmp : (1.9 : ℝ) ≤ ((16 : ℝ) / 15) ^ 20 := by norm_num
  have hmono : Real.logb (1.9 : ℝ) (1.9 : ℝ) ≤ Real.logb (1.9 : ℝ) (((16 : ℝ) / 15) ^ 20) := by
    exact Real.logb_le_logb_of_le hb (by norm_num : 0 < (1.9 : ℝ)) hpowcmp
  have hbase : Real.logb (1.9 : ℝ) (1.9 : ℝ) = 1 := by
    unfold Real.logb
    have hcpos : 0 < Real.log (1.9 : ℝ) := Real.log_pos (by norm_num : 1 < (1.9 : ℝ))
    field_simp [hcpos.ne']
  have h20 : Real.logb (1.9 : ℝ) (((16 : ℝ) / 15) ^ 20) =
      (20 : ℝ) * Real.logb (1.9 : ℝ) ((16 : ℝ) / 15) := by
    exact Real.logb_pow (1.9 : ℝ) ((16 : ℝ) / 15) 20
  rw [hbase] at hmono
  rw [h20] at hmono
  nlinarith

/-- double base-1.9 log of w ≥ 2 is at least 1/20 -/
lemma logb19_logb19_w_ge {w : ℕ} (hw : 2 ≤ w) :
    (1 : ℝ) / 20 ≤ Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
  have hb : 1 < (1.9 : ℝ) := by norm_num
  have hBw : Real.logb (1.9 : ℝ) 2 ≤ Real.logb (1.9 : ℝ) (w : ℝ) := logb19_w_ge_logb19_two hw
  have hB2pos : 0 < Real.logb (1.9 : ℝ) 2 := logb19_two_pos
  have hdbl : Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) 2) ≤
      Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) :=
    Real.logb_le_logb_of_le hb hB2pos hBw
  have h16 : (16 : ℝ) / 15 ≤ Real.logb (1.9 : ℝ) 2 := logb19_two_ge_16div15
  have hb16 : 0 < (16 : ℝ) / 15 := by norm_num
  have hB16 : Real.logb (1.9 : ℝ) ((16 : ℝ) / 15) ≤
      Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) 2) :=
    Real.logb_le_logb_of_le hb hb16 h16
  exact le_trans (le_trans logb19_16div15_ge_twentieth hB16) hdbl

/-- logb w ≥ 1 for w ≥ 2 with base 1.9; so logb logb w ≥ logb(logb 2) > 0 -/
lemma logb19_logb19_w_pos {w : ℕ} (hw : 2 ≤ w) :
    0 < Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
  linarith [logb19_logb19_w_ge hw]

/-- `Real.log (2*w) ≤ 2 * Real.log w` for `w ≥ 2` -/
lemma log_two_mul_le {w : ℕ} (hw : 2 ≤ w) : Real.log (2 * (w : ℝ)) ≤ 2 * Real.log (w : ℝ) := by
  have hwR : (2 : ℝ) ≤ (w : ℝ) := nat_two_le_real hw
  have hwpos : 0 < (w : ℝ) := lt_of_lt_of_le (by norm_num) hwR
  have hlogmul : Real.log (2 * (w : ℝ)) = Real.log 2 + Real.log (w : ℝ) :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hwpos)
  have hlog2_le : Real.log 2 ≤ Real.log (w : ℝ) :=
    Real.log_le_log (x := (2 : ℝ)) (y := (w : ℝ)) (by norm_num) hwR
  calc
    Real.log (2 * (w : ℝ)) = Real.log 2 + Real.log (w : ℝ) := hlogmul
    _ ≤ Real.log (w : ℝ) + Real.log (w : ℝ) := by linarith
    _ = 2 * Real.log (w : ℝ) := by ring

/-- the ratio log(2w)/(logb w logb logb w) is bounded by 40 for w ≥ 2 -/
lemma log_ratio_bound {w : ℕ} (hw : 2 ≤ w) :
    Real.log (2 * (w : ℝ)) ≤
      40 * Real.logb (1.9 : ℝ) (w : ℝ) * Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
  let c : ℝ := Real.log (1.9 : ℝ)
  have hcpos : 0 < c := by
    unfold c
    exact Real.log_pos (by norm_num : 1 < (1.9 : ℝ))
  have hcl : c ≤ 1 := by
    unfold c
    have h := Real.log_le_sub_one_of_pos (x := (1.9 : ℝ)) (by norm_num)
    have h2 : (1.9 : ℝ) - 1 ≤ 1 := by norm_num
    exact le_trans h h2
  -- step 1: log(2w) ≤ 2 log w
  have h1 : Real.log (2 * (w : ℝ)) ≤ 2 * Real.log (w : ℝ) := log_two_mul_le hw
  -- log w = c * logb_{1.9} w, and c ≤ 1, logb_{1.9} w ≥ 1, so log w ≤ logb w
  have hdef : Real.logb (1.9 : ℝ) (w : ℝ) = Real.log (w : ℝ) / c := by rfl
  have hlogw : Real.log (w : ℝ) = c * Real.logb (1.9 : ℝ) (w : ℝ) := by
    rw [hdef]
    field_simp [hcpos.ne']
  have hBnonneg : 0 ≤ Real.logb (1.9 : ℝ) (w : ℝ) := by
    exact le_trans (by norm_num : 0 ≤ (1 : ℝ))
      (le_trans logb19_two_ge_one (logb19_w_ge_logb19_two hw))
  have h2 : 2 * Real.log (w : ℝ) ≤ 2 * Real.logb (1.9 : ℝ) (w : ℝ) := by
    calc
      2 * Real.log (w : ℝ) = 2 * (c * Real.logb (1.9 : ℝ) (w : ℝ)) := by rw [hlogw]
      _ ≤ 2 * Real.logb (1.9 : ℝ) (w : ℝ) := by
        have hclbw : c * Real.logb (1.9 : ℝ) (w : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) := by
          simpa using (mul_le_mul_of_nonneg_right hcl hBnonneg)
        exact mul_le_mul_of_nonneg_left hclbw (by norm_num : 0 ≤ (2 : ℝ))
  -- step 3: double log ≥ 1/20 gives 2 logb w ≤ 40 logb w * double log
  have hd : (1 : ℝ) / 20 ≤ Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) :=
    logb19_logb19_w_ge hw
  have h3 : 2 * Real.logb (1.9 : ℝ) (w : ℝ) ≤
      40 * Real.logb (1.9 : ℝ) (w : ℝ) * Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
    have hmul : (40 * Real.logb (1.9 : ℝ) (w : ℝ)) * (1 / 20) ≤
        (40 * Real.logb (1.9 : ℝ) (w : ℝ)) * Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : 0 ≤ (40 : ℝ)) hBnonneg)
    calc
      2 * Real.logb (1.9 : ℝ) (w : ℝ)
          = (40 * Real.logb (1.9 : ℝ) (w : ℝ)) * (1 / 20) := by ring
      _ ≤ (40 * Real.logb (1.9 : ℝ) (w : ℝ)) * Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := hmul
  exact le_trans (le_trans h1 h2) h3

/-- big constant absorbs small powers: `(w+1)^{1/w}`-free formulation:
`(w+1) * a ^ w ≤ (2a)^w` for `a ≥ 1` -/
lemma mul_pow_le {w : ℕ} (hw : 2 ≤ w) {a : ℝ} (ha : 1 ≤ a) :
    ((w : ℝ) + 1) * a ^ w ≤ (2 * a) ^ w := by
  have hnat : w + 1 ≤ 2 ^ w := by
    refine Nat.le_induction (m := 2) ?base ?step w hw
    · norm_num
    · intro n hn ih
      have h2 : 2 * (n + 1) ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      have h3 : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
      omega
  have hreal : ((w : ℝ) + 1) ≤ (2 : ℝ) ^ w := by
    exact_mod_cast hnat
  have hanonneg : 0 ≤ a ^ w := by
    exact pow_nonneg (by linarith) w
  have h := mul_le_mul_of_nonneg_right hreal hanonneg
  calc
    ((w : ℝ) + 1) * a ^ w ≤ (2 : ℝ) ^ w * a ^ w := h
    _ = (2 * a) ^ w := by rw [mul_pow]

/-- `log w ≤ w/2`-type growth for w ≥ 2 (natural log) -/
lemma log_le_half_self {w : ℕ} (hw : 2 ≤ w) : Real.log (w : ℝ) ≤ (w : ℝ) / 2 := by
  have hwR : (2 : ℝ) ≤ (w : ℝ) := nat_two_le_real hw
  have hwpos : 0 < (w : ℝ) := lt_of_lt_of_le (by norm_num) hwR
  have hhalf : 0 < (w : ℝ) / 2 := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hloghalf : Real.log ((w : ℝ) / 2) ≤ (w : ℝ) / 2 - 1 :=
    Real.log_le_sub_one_of_pos hhalf
  have hsplit : Real.log (w : ℝ) = Real.log 2 + Real.log ((w : ℝ) / 2) := by
    calc Real.log (w : ℝ) = Real.log (2 * ((w : ℝ) / 2)) := by congr; ring
      _ = Real.log 2 + Real.log ((w : ℝ) / 2) := by
        exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hhalf)
  calc
    Real.log (w : ℝ) = Real.log 2 + Real.log ((w : ℝ) / 2) := hsplit
    _ ≤ 1 + ((w : ℝ) / 2 - 1) := by linarith
    _ = (w : ℝ) / 2 := by ring

end Submission.LogLemmas
