import Mathlib
import Submission.Work.HP.IcVolAux

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace

namespace Work.HP.IcVolEst

/-! ## Elementary bounds on the fibre radius `fiberA`

`fiberA s rv` is, for `1 < s²`, `min (√(1-rv²)) (rv/√(s²-1))`; these two lemmas
give the upper bound and the exact value below the crossover `√(1-1/s²)`. -/

lemma fiberA_le_div {s y : ℝ} (h : 1 < s ^ 2) :
    fiberA s y ≤ y / Real.sqrt (s ^ 2 - 1) := by
  unfold fiberA
  rw [if_pos h]
  exact min_le_right _ _

lemma fiberA_eq_div {s y : ℝ} (h : 1 < s ^ 2) (hy : 0 ≤ y)
    (hy' : y ≤ Real.sqrt (1 - 1 / s ^ 2)) :
    fiberA s y = y / Real.sqrt (s ^ 2 - 1) := by
  have hs2 : (0 : ℝ) < s ^ 2 := by nlinarith
  have hs1 : (0 : ℝ) < s ^ 2 - 1 := by nlinarith
  have h1 : (0 : ℝ) ≤ 1 - 1 / s ^ 2 := by
    have : (1 : ℝ) / s ^ 2 ≤ 1 := by
      rw [div_le_iff₀ hs2]; linarith
    linarith
  have hsq : y ^ 2 ≤ 1 - 1 / s ^ 2 := by
    have h2 : y ^ 2 ≤ (Real.sqrt (1 - 1 / s ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hy hy' 2
    rwa [Real.sq_sqrt h1] at h2
  have hsq' : y ^ 2 * s ^ 2 ≤ s ^ 2 - 1 := by
    have h2 : y ^ 2 * s ^ 2 ≤ (1 - 1 / s ^ 2) * s ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (le_of_lt hs2)
    have heq : (1 - 1 / s ^ 2) * s ^ 2 = s ^ 2 - 1 := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hs2)]
    rwa [heq] at h2
  rw [fiberA, if_pos h, min_eq_right]
  calc y / Real.sqrt (s ^ 2 - 1) = Real.sqrt (y ^ 2 / (s ^ 2 - 1)) := by
        rw [Real.sqrt_div (sq_nonneg y), Real.sqrt_sq hy]
    _ ≤ Real.sqrt (1 - y ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hs1]; nlinarith

/-! ## The scalar radial integral -/

/-- `∫_0^∞ y^{n-1} · fiberA s y dy`, the scalar reduction of the band-volume asymptotic. -/
def bandP (n : ℕ) (s : ℝ) : ℝ := ∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * fiberA s y

lemma bandP_nonneg (n : ℕ) (s : ℝ) : 0 ≤ bandP n s := by
  rw [bandP]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact mul_nonneg (pow_nonneg (le_of_lt hy) _) (fiberA_nonneg s y (le_of_lt hy))

/-- Since `fiberA s y = 0` for `y ≥ 1`, the integral over `(0,∞)` equals that over `(0,1]`. -/
lemma bandP_eq_Ioc (n : ℕ) (s : ℝ) :
    bandP n s = ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (n - 1) * fiberA s y := by
  rw [bandP, ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hy]
    by_cases h1 : y ≤ 1
    · rw [Set.indicator_of_mem (show y ∈ Set.Ioc (0 : ℝ) 1 from ⟨hy, h1⟩)]
    · rw [Set.indicator_of_notMem (show y ∉ Set.Ioc (0 : ℝ) 1 from fun hh => h1 hh.2)]
      rw [fiberA_eq_zero_of_one_le (s := s) (rv := y) (le_of_lt (lt_of_not_ge h1)), mul_zero]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
    exact fun hh => hy (Set.Ioc_subset_Ioi_self hh)

lemma integral_Ioc_pow (b : ℝ) (hb : 0 ≤ b) (k : ℕ) :
    ∫ y in Set.Ioc (0 : ℝ) b, y ^ k = b ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  rw [← intervalIntegral.integral_of_le hb, integral_pow]
  rw [zero_pow (by omega : k + 1 ≠ 0), sub_zero]
  simp only [Nat.cast_add_one]

/-- Integrability of a bounded, measurable function on the finite interval `(0,1]`. -/
lemma integrableOn_Ioc_one {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖f y‖ ≤ C) :
    IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := by
  refine Measure.integrableOn_of_bounded (M := C) ?_ hf.aestronglyMeasurable ?_
  · rw [volume_Ioc]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact hb y hy

lemma integrable_Ioc_bandP (n : ℕ) (s : ℝ) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) * fiberA s y) (Set.Ioc (0 : ℝ) 1) volume := by
  refine integrableOn_Ioc_one (C := 1) (((measurable_id.pow_const (n - 1)).mul
    ((measurable_fiberA s).comp measurable_id))) ?_
  intro y hy
  have hy0 : 0 ≤ y := le_of_lt hy.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hy0 _) (fiberA_nonneg s y hy0))]
  have hpw : y ^ (n - 1) ≤ 1 := pow_le_one₀ hy0 hy.2
  have hpn : fiberA s y ≤ 1 := fiberA_le_one s y
  nlinarith [pow_nonneg hy0 (n - 1), fiberA_nonneg s y hy0]

/-- Case `s² ≤ 2`: the integral is at most `1/n`. -/
lemma bandP_le_caseA (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    bandP n s ≤ 1 / (n : ℝ) := by
  rw [bandP_eq_Ioc]
  have hf := integrable_Ioc_bandP n s
  have hg : IntegrableOn (fun y : ℝ => y ^ (n - 1)) (Set.Ioc (0 : ℝ) 1) volume := by
    refine integrableOn_Ioc_one (C := 1) (measurable_id.pow_const (n - 1)) ?_
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt hy.1) _)]
    exact pow_le_one₀ (le_of_lt hy.1) hy.2
  have hle : ∫ y, y ^ (n - 1) * fiberA s y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ ∫ y, y ^ (n - 1) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (pow_nonneg (le_of_lt hy.1) _) (fiberA_nonneg s y (le_of_lt hy.1))
    · exact hg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hp : fiberA s y ≤ 1 := fiberA_le_one s y
      calc y ^ (n - 1) * fiberA s y ≤ y ^ (n - 1) * 1 :=
            mul_le_mul_of_nonneg_left hp (pow_nonneg (le_of_lt hy.1) _)
        _ = y ^ (n - 1) := mul_one _
  calc ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (n - 1) * fiberA s y
      = ∫ y, y ^ (n - 1) * fiberA s y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := rfl
    _ ≤ ∫ y, y ^ (n - 1) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := hle
    _ = ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (n - 1) := rfl
    _ = 1 ^ ((n - 1) + 1) / (((n - 1) + 1 : ℕ) : ℝ) := integral_Ioc_pow 1 (by norm_num) (n - 1)
    _ = 1 / (n : ℝ) := by rw [Nat.sub_add_cancel hn]; norm_num

/-- Case `1 < s²`: upper bound for the integral. -/
lemma bandP_le_caseB (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 1 < s ^ 2) :
    bandP n s ≤ (1 / ((n : ℝ) + 1)) * (1 / Real.sqrt (s ^ 2 - 1)) := by
  have hs1 : (0 : ℝ) < Real.sqrt (s ^ 2 - 1) := Real.sqrt_pos.mpr (by linarith)
  rw [bandP_eq_Ioc]
  have hf := integrable_Ioc_bandP n s
  have hg : IntegrableOn (fun y : ℝ => y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1)))
      (Set.Ioc (0 : ℝ) 1) volume := by
    refine integrableOn_Ioc_one (C := 1 / Real.sqrt (s ^ 2 - 1))
      (((measurable_id.pow_const (n - 1)).mul (measurable_id.div_const _))) ?_
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt hy.1
    have hdiv : 0 ≤ y / Real.sqrt (s ^ 2 - 1) := div_nonneg hy0 (le_of_lt hs1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hy0 _) hdiv)]
    have hpw : y ^ (n - 1) ≤ 1 := pow_le_one₀ hy0 hy.2
    have hq : y / Real.sqrt (s ^ 2 - 1) ≤ 1 / Real.sqrt (s ^ 2 - 1) :=
      div_le_div_of_nonneg_right hy.2 (le_of_lt hs1)
    calc y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
        ≤ 1 * (1 / Real.sqrt (s ^ 2 - 1)) := mul_le_mul hpw hq hdiv (by norm_num)
      _ = 1 / Real.sqrt (s ^ 2 - 1) := one_mul _
  have hle : ∫ y, y ^ (n - 1) * fiberA s y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ ∫ y, y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (pow_nonneg (le_of_lt hy.1) _) (fiberA_nonneg s y (le_of_lt hy.1))
    · exact hg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_le_mul_of_nonneg_left (fiberA_le_div hs) (pow_nonneg (le_of_lt hy.1) _)
  have hcomp : ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
      = (1 / Real.sqrt (s ^ 2 - 1)) * ∫ y in Set.Ioc (0 : ℝ) 1, y ^ n := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have key : y ^ (n - 1) * y = y ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
    simp only [div_eq_mul_inv, one_mul]
    rw [← key]
    ring
  calc ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (n - 1) * fiberA s y
      = ∫ y, y ^ (n - 1) * fiberA s y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := rfl
    _ ≤ ∫ y, y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := hle
    _ = (1 / Real.sqrt (s ^ 2 - 1)) * ∫ y in Set.Ioc (0 : ℝ) 1, y ^ n := hcomp
    _ = (1 / Real.sqrt (s ^ 2 - 1)) * (1 / ((n : ℝ) + 1)) := by
        rw [integral_Ioc_pow 1 (by norm_num) n]
        simp only [Nat.cast_add_one, one_pow]
    _ = (1 / ((n : ℝ) + 1)) * (1 / Real.sqrt (s ^ 2 - 1)) := by ring

/-- Case `1 < s²`: lower bound for the integral. -/
lemma bandP_ge_caseB (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) (hsq : 1 < s ^ 2) :
    (1 / ((n : ℝ) + 1)) * (Real.sqrt (1 - 1 / s ^ 2)) ^ (n + 1) / Real.sqrt (s ^ 2 - 1)
      ≤ bandP n s := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hrad0 : (0 : ℝ) ≤ 1 - 1 / s ^ 2 := by
    have : (1 : ℝ) / s ^ 2 ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 2)]; linarith
    linarith
  set r := Real.sqrt (1 - 1 / s ^ 2) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    apply Real.sqrt_pos.mpr
    have : (1 : ℝ) / s ^ 2 < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < s ^ 2)]; linarith
    linarith
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hrle1 : r ≤ 1 := by
    rw [hrdef]
    calc Real.sqrt (1 - 1 / s ^ 2) ≤ Real.sqrt 1 := by
          apply Real.sqrt_le_sqrt
          have h : (0 : ℝ) ≤ 1 / s ^ 2 := by positivity
          linarith
      _ = 1 := Real.sqrt_one
  have hrs : r * s = Real.sqrt (s ^ 2 - 1) := by
    have step1 : r * s = Real.sqrt (1 - 1 / s ^ 2) * Real.sqrt (s ^ 2) := by
      rw [hrdef, Real.sqrt_sq (le_of_lt hs)]
    have step2 : Real.sqrt (1 - 1 / s ^ 2) * Real.sqrt (s ^ 2)
        = Real.sqrt ((1 - 1 / s ^ 2) * s ^ 2) := (Real.sqrt_mul hrad0 (s ^ 2)).symm
    rw [step1, step2]
    congr 1
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < s ^ 2))]
  rw [bandP_eq_Ioc]
  have hf := integrable_Ioc_bandP n s
  have hEq : ∫ y in Set.Ioc (0 : ℝ) r, y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
      = ∫ y in Set.Ioc (0 : ℝ) r, y ^ (n - 1) * fiberA s y := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only []
    rw [fiberA_eq_div hsq (le_of_lt hy.1) (le_trans hy.2 (le_of_eq hrdef))]
  have hmono : ∫ y in Set.Ioc (0 : ℝ) r, y ^ (n - 1) * fiberA s y
      ≤ ∫ y in Set.Ioc (0 : ℝ) 1, y ^ (n - 1) * fiberA s y := by
    refine MeasureTheory.setIntegral_mono_set hf ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg (pow_nonneg (le_of_lt hu.1) _) (fiberA_nonneg s u (le_of_lt hu.1))
    · filter_upwards with u hu
      exact ⟨hu.1, le_trans hu.2 hrle1⟩
  have hint : ∫ y in Set.Ioc (0 : ℝ) r, y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
      = (1 / ((n : ℝ) + 1)) * r ^ (n + 1) / Real.sqrt (s ^ 2 - 1) := by
    have hcomp : ∫ y in Set.Ioc (0 : ℝ) r, y ^ (n - 1) * (y / Real.sqrt (s ^ 2 - 1))
        = (1 / Real.sqrt (s ^ 2 - 1)) * ∫ y in Set.Ioc (0 : ℝ) r, y ^ n := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      have key : y ^ (n - 1) * y = y ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
      simp only [div_eq_mul_inv, one_mul]
      rw [← key]
      ring
    rw [hcomp, integral_Ioc_pow r hr0 n]
    simp only [Nat.cast_add_one]
    ring
  have h1 : (1 / ((n : ℝ) + 1)) * r ^ (n + 1) / Real.sqrt (s ^ 2 - 1)
      = ∫ y in Set.Ioc (0 : ℝ) r, y ^ (n - 1) * fiberA s y := by
    rw [← hint, hEq]
  rw [h1]
  exact hmono

/-! ## The asymptotic for `bandP` -/

lemma bandP_asymp (n : ℕ) (hn : 1 ≤ n) :
    ∀ s : ℝ, 0 < s →
      |bandP n s - 1 / (((n : ℝ) + 1) * s)| ≤
        (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * min 1 (1 / s ^ 2) := by
  intro s hs
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs2pos : (0 : ℝ) < s ^ 2 := by positivity
  have hQpos : (0 : ℝ) < 1 / (((n : ℝ) + 1) * s) := by positivity
  rcases lt_or_ge (2 : ℝ) (s ^ 2) with hB | hA
  · -- Case `2 < s²`
    have hs1 : 1 < s ^ 2 := by linarith
    set r := Real.sqrt (1 - 1 / s ^ 2) with hrdef
    have hrad0 : (0 : ℝ) ≤ 1 - 1 / s ^ 2 := by
      have : (1 : ℝ) / s ^ 2 ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 2)]; linarith
      linarith
    have hrpos : 0 < r := by
      rw [hrdef]
      apply Real.sqrt_pos.mpr
      have : (1 : ℝ) / s ^ 2 < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < s ^ 2)]; linarith
      linarith
    have hr0 : 0 ≤ r := le_of_lt hrpos
    have hrle1 : r ≤ 1 := by
      rw [hrdef]
      calc Real.sqrt (1 - 1 / s ^ 2) ≤ Real.sqrt 1 := by
            apply Real.sqrt_le_sqrt
            have h : (0 : ℝ) ≤ 1 / s ^ 2 := by positivity
            linarith
        _ = 1 := Real.sqrt_one
    have hrs : r * s = Real.sqrt (s ^ 2 - 1) := by
      have step1 : r * s = Real.sqrt (1 - 1 / s ^ 2) * Real.sqrt (s ^ 2) := by
        rw [hrdef, Real.sqrt_sq (le_of_lt hs)]
      have step2 : Real.sqrt (1 - 1 / s ^ 2) * Real.sqrt (s ^ 2)
          = Real.sqrt ((1 - 1 / s ^ 2) * s ^ 2) := (Real.sqrt_mul hrad0 (s ^ 2)).symm
      rw [step1, step2]
      congr 1
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < s ^ 2))]
    have hmin : min 1 (1 / s ^ 2) = 1 / s ^ 2 := by
      rw [min_eq_right]
      rw [div_le_iff₀ hs2pos]; linarith
    have hQ : (1 / ((n : ℝ) + 1)) * (1 / Real.sqrt (s ^ 2 - 1))
        = (1 / (((n : ℝ) + 1) * s)) * (1 / r) := by
      rw [← hrs]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    have hQr : (1 / ((n : ℝ) + 1)) * r ^ (n + 1) / Real.sqrt (s ^ 2 - 1)
        = (1 / (((n : ℝ) + 1) * s)) * r ^ n := by
      have hrne : r ≠ 0 := ne_of_gt hrpos
      have hsne : s ≠ 0 := ne_of_gt hs
      have hnne : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [← hrs, pow_succ]
      field_simp
      try ring
    have hup : bandP n s - 1 / (((n : ℝ) + 1) * s)
        ≤ (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * min 1 (1 / s ^ 2) := by
      rw [hmin]
      have hPu := bandP_le_caseB n hn s hs1
      rw [hQ] at hPu
      have h3 : 1 / r - 1 ≤ 1 / s ^ 2 := by
        rw [hrdef]
        exact inv_sqrt_one_sub_sub_le (by positivity) (by rw [div_le_iff₀ hs2pos]; linarith)
      have e1 : bandP n s - 1 / (((n : ℝ) + 1) * s)
          ≤ (1 / (((n : ℝ) + 1) * s)) * (1 / r - 1) := by nlinarith [hPu]
      have e2 : (1 / (((n : ℝ) + 1) * s)) * (1 / r - 1)
          ≤ (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hQpos.le
      have hd : (0 : ℝ) ≤ 1 / s ^ 2 := by positivity
      have e3 : (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2)
          ≤ (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2) := by
        have hle : (1 : ℝ) ≤ 2 * (n : ℝ) + 100 := by linarith
        calc (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2)
            = 1 * ((1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2)) := by ring
          _ ≤ (2 * (n : ℝ) + 100) * ((1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2)) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hQpos.le hd)
          _ = (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2) := by ring
      linarith [e1, e2, e3]
    have hlo : 1 / (((n : ℝ) + 1) * s) - bandP n s
        ≤ (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * min 1 (1 / s ^ 2) := by
      rw [hmin]
      have hPl := bandP_ge_caseB n hn s hs hs1
      rw [hQr] at hPl
      have h4 : 1 - r ^ n ≤ (n : ℝ) * (1 / s ^ 2) := by
        have h5 : 1 - r ^ n ≤ (n : ℝ) * (1 - r) := one_sub_pow_le hr0 hrle1 n
        have h6 : 1 - r ≤ 1 / s ^ 2 := by
          rw [hrdef]
          exact one_sub_sqrt_le (by positivity) (by rw [div_le_iff₀ hs2pos]; linarith)
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [h5, h6, hn0]
      have f1 : 1 / (((n : ℝ) + 1) * s) - bandP n s
          ≤ (1 / (((n : ℝ) + 1) * s)) * (1 - r ^ n) := by nlinarith [hPl]
      have f2 : (1 / (((n : ℝ) + 1) * s)) * (1 - r ^ n)
          ≤ (1 / (((n : ℝ) + 1) * s)) * ((n : ℝ) * (1 / s ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 hQpos.le
      have hd : (0 : ℝ) ≤ 1 / s ^ 2 := by positivity
      have f3 : (1 / (((n : ℝ) + 1) * s)) * ((n : ℝ) * (1 / s ^ 2))
          ≤ (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2) := by
        have hle : (n : ℝ) ≤ 2 * (n : ℝ) + 100 := by linarith
        calc (1 / (((n : ℝ) + 1) * s)) * ((n : ℝ) * (1 / s ^ 2))
            = (n : ℝ) * ((1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2)) := by ring
          _ ≤ (2 * (n : ℝ) + 100) * ((1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2)) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hQpos.le hd)
          _ = (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * (1 / s ^ 2) := by ring
      linarith [f1, f2, f3]
    exact abs_sub_le_iff.mpr ⟨hup, hlo⟩
  · -- Case `s² ≤ 2`
    have hP0 : 0 ≤ bandP n s := bandP_nonneg n s
    have hP1 : bandP n s ≤ 1 / (n : ℝ) := bandP_le_caseA n hn s
    have hmin : (1 : ℝ) / 2 ≤ min 1 (1 / s ^ 2) := by
      refine le_min (by norm_num) ?_
      rw [le_div_iff₀ hs2pos]; linarith
    have hsle2 : s ≤ 2 := by
      have h1 : s ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_sq (le_of_lt hs)]; exact Real.sqrt_le_sqrt hA
      have h2 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      linarith
    have hkey2 : 1 / (n : ℝ) ≤ ((n : ℝ) + 49) * (1 / (((n : ℝ) + 1) * s)) := by
      have hden : (0 : ℝ) < ((n : ℝ) + 1) * s := by positivity
      have hmain : ((n : ℝ) + 1) * s ≤ (n : ℝ) * ((n : ℝ) + 49) := by
        have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h1 : ((n : ℝ) + 1) * s ≤ ((n : ℝ) + 1) * 2 :=
          mul_le_mul_of_nonneg_left hsle2 (by linarith)
        have h2 : ((n : ℝ) + 1) * 2 ≤ (n : ℝ) * ((n : ℝ) + 49) := by
          nlinarith [hn1R, sq_nonneg ((n : ℝ))]
        linarith
      rw [div_le_iff₀ hnR]
      rw [show ((n : ℝ) + 49) * (1 / (((n : ℝ) + 1) * s)) * (n : ℝ)
          = ((n : ℝ) * ((n : ℝ) + 49)) / (((n : ℝ) + 1) * s) from by
        rw [div_eq_mul_inv]; ring]
      rw [le_div_iff₀ hden]
      simpa using hmain
    have h1 : |bandP n s - 1 / (((n : ℝ) + 1) * s)|
        ≤ 1 / (n : ℝ) + 1 / (((n : ℝ) + 1) * s) := by
      refine abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have h2 : 1 / (n : ℝ) + 1 / (((n : ℝ) + 1) * s)
        ≤ (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * min 1 (1 / s ^ 2) := by
      have hC : (2 * (n : ℝ) + 100) / 2 ≤ (2 * (n : ℝ) + 100) * min 1 (1 / s ^ 2) := by
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hmin
          (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 100)
      calc 1 / (n : ℝ) + 1 / (((n : ℝ) + 1) * s)
          ≤ ((n : ℝ) + 49) * (1 / (((n : ℝ) + 1) * s)) + 1 / (((n : ℝ) + 1) * s) := by
            linarith [hkey2]
        _ = ((n : ℝ) + 50) * (1 / (((n : ℝ) + 1) * s)) := by ring
        _ ≤ ((2 * (n : ℝ) + 100) / 2) * (1 / (((n : ℝ) + 1) * s)) := by
            apply mul_le_mul_of_nonneg_right _ hQpos.le
            linarith
        _ ≤ ((2 * (n : ℝ) + 100) * min 1 (1 / s ^ 2)) * (1 / (((n : ℝ) + 1) * s)) := by
            apply mul_le_mul_of_nonneg_right hC hQpos.le
        _ = (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * min 1 (1 / s ^ 2) := by ring
    linarith [h1, h2]

/-! ## Radial reduction -/

lemma radial_bandIntegral {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (hW : 1 ≤ Module.finrank ℝ W) (s : ℝ) :
    ∫ v : W, 2 * fiberA s ‖v‖
      = 2 * (Module.finrank ℝ W : ℝ) * ballVol (Module.finrank ℝ W)
          * bandP (Module.finrank ℝ W) s := by
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le Nat.zero_lt_one hW)
  change ∫ v : W, (fun y : ℝ => 2 * fiberA s y) ‖v‖ = _
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := volume) (f := fun y : ℝ => 2 * fiberA s y)]
  have hvol : volume.real (Metric.ball (0 : W) 1) = ballVol (Module.finrank ℝ W) := by
    rw [Measure.real, volume_unitBall hW, ENNReal.toReal_ofReal (ballVol_nonneg _)]
  rw [hvol]
  simp only [nsmul_eq_mul, smul_eq_mul, bandP]
  have h2 : (∫ y in Set.Ioi 0, y ^ (Module.finrank ℝ W - 1) * (2 * fiberA s y))
      = 2 * ∫ y in Set.Ioi 0, y ^ (Module.finrank ℝ W - 1) * fiberA s y := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y hy; ring
  rw [h2]; ring

/-! ## The abstract asymptotic for the radial integral -/

lemma bandInt_asymp {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (n : ℕ) (hfin : Module.finrank ℝ W = n) (hn : 1 ≤ n) :
    ∀ s : ℝ, 0 < s →
      |(∫ v : W, 2 * fiberA s ‖v‖) -
        2 * ((n : ℝ) / ((n : ℝ) + 1)) * ballVol n / s| ≤
      (2 * (n : ℝ) + 100) *
        (2 * ((n : ℝ) / ((n : ℝ) + 1)) * ballVol n / s) * min 1 (1 / s ^ 2) := by
  intro s hs
  have hrad := radial_bandIntegral (W := W) (by rw [hfin]; exact hn) s
  rw [hrad, hfin]
  have hK0 : (0 : ℝ) ≤ 2 * (n : ℝ) * ballVol n :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (ballVol_nonneg n)
  have hB : 2 * ((n : ℝ) / ((n : ℝ) + 1)) * ballVol n / s
      = (2 * (n : ℝ) * ballVol n) * (1 / (((n : ℝ) + 1) * s)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [hB]
  have h1 := bandP_asymp n hn s hs
  have key : |bandP n s - 1 / (((n : ℝ) + 1) * s)| * (2 * (n : ℝ) * ballVol n)
      ≤ (2 * (n : ℝ) + 100) * (1 / (((n : ℝ) + 1) * s)) * min 1 (1 / s ^ 2)
          * (2 * (n : ℝ) * ballVol n) :=
    mul_le_mul_of_nonneg_right h1 hK0
  have hlhs : |2 * (n : ℝ) * ballVol n * bandP n s
        - (2 * (n : ℝ) * ballVol n) * (1 / (((n : ℝ) + 1) * s))|
      = |bandP n s - 1 / (((n : ℝ) + 1) * s)| * (2 * (n : ℝ) * ballVol n) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hK0, mul_comm]
  rw [hlhs]
  refine le_trans key (le_of_eq ?_)
  ring

/-! ## The main theorem -/

theorem bandVolAsymp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E), c ≠ 0 →
      |(MeasureTheory.volume {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖}).toReal -
        2 * ((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ) *
          ballVol (Module.finrank ℝ E - 1) / ‖c‖| ≤
      C * (2 * ((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ) *
          ballVol (Module.finrank ℝ E - 1) / ‖c‖) * min 1 (1 / ‖c‖ ^ 2) := by
  refine ⟨2 * (Module.finrank ℝ E : ℝ) + 100, by positivity, fun c hc => ?_⟩
  have hfinW : Module.finrank ℝ ↥(Submodule.span ℝ {c})ᗮ = Module.finrank ℝ E - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {c})
    rw [finrank_span_singleton (K := ℝ) (V := E) hc] at h
    omega
  have hn1 : 1 ≤ Module.finrank ℝ E - 1 := by omega
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hvol : (MeasureTheory.volume {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖}).toReal
      = ∫ v : ↥(Submodule.span ℝ {c})ᗮ, 2 * fiberA ‖c‖ ‖v‖ := by
    rw [bandRegion_real_eq c hc]
  rw [hvol]
  have hA := bandInt_asymp (W := ↥(Submodule.span ℝ {c})ᗮ) (Module.finrank ℝ E - 1) hfinW hn1 ‖c‖ hs
  have hnat : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 :=
    (Nat.sub_add_cancel (by omega : 1 ≤ Module.finrank ℝ E)).symm
  have hdR : (Module.finrank ℝ E : ℝ) = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1 := by
    rw [hnat]; push_cast; ring
  have hM : 2 * ((Module.finrank ℝ E : ℝ) - 1) / (Module.finrank ℝ E : ℝ)
        * ballVol (Module.finrank ℝ E - 1) / ‖c‖
      = 2 * (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1))
        * ballVol (Module.finrank ℝ E - 1) / ‖c‖ := by
    rw [hdR]; ring_nf
  rw [hM]
  refine le_trans hA ?_
  have hCle : (2 * (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) + 100)
      ≤ (2 * (Module.finrank ℝ E : ℝ) + 100) := by
    have : (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
    linarith
  have hX0 : (0 : ℝ) ≤ 2 * (((Module.finrank ℝ E - 1 : ℕ) : ℝ)
        / (((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1)) * ballVol (Module.finrank ℝ E - 1) / ‖c‖ := by
    apply div_nonneg
    · exact mul_nonneg (by positivity) (ballVol_nonneg _)
    · exact norm_nonneg c
  have hmin0 : (0 : ℝ) ≤ min 1 (1 / ‖c‖ ^ 2) := le_min (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hX0) hmin0

end Work.HP.IcVolEst
