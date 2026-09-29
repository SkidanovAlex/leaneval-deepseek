import Mathlib
import Submission.Commons.GeometryOfNumbers.Counting.sum_int_points_annulus_le_radial
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume
import Submission.Commons.Probability.Gaussian.stdGaussian_map_neg

namespace Commons.GeometryOfNumbers.Counting

open _root_.MeasureTheory Metric
open scoped ENNReal

noncomputable section

def tailG (z : ℝ) : ℝ := (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | z ≤ y}
lemma tailG_nonneg (z : ℝ) : 0 ≤ tailG z := measureReal_nonneg
lemma tailG_le_one (z : ℝ) : tailG z ≤ 1 := by
  have h := MeasureTheory.measureReal_mono (μ := ProbabilityTheory.stdGaussian ℝ)
    (Set.subset_univ {y : ℝ | z ≤ y}) (by simp)
  have huniv : (ProbabilityTheory.stdGaussian ℝ).real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one]
  rwa [huniv] at h
lemma tailG_mono {a b : ℝ} (hab : a ≤ b) : tailG b ≤ tailG a := by
  refine MeasureTheory.measureReal_mono (μ := ProbabilityTheory.stdGaussian ℝ) ?_ (by simp)
  intro y hy; exact le_trans hab hy
lemma tailG_eq_cdf (z : ℝ) :
    tailG z = ProbabilityTheory.cdf (ProbabilityTheory.stdGaussian ℝ) (-z) := by
  have key : (ProbabilityTheory.stdGaussian ℝ).real (Set.Ici z)
      = (ProbabilityTheory.stdGaussian ℝ).real (Set.Iic (-z)) := by
    have hmap : (ProbabilityTheory.stdGaussian ℝ).map Neg.neg
        = ProbabilityTheory.stdGaussian ℝ :=
      Commons.Probability.Gaussian.stdGaussian_map_neg
    have h1 : (ProbabilityTheory.stdGaussian ℝ).real (Set.Ici z)
        = ((ProbabilityTheory.stdGaussian ℝ).map Neg.neg).real (Set.Ici z) := by rw [hmap]
    rw [h1, MeasureTheory.map_measureReal_apply measurable_neg measurableSet_Ici]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [tailG, ProbabilityTheory.cdf_eq_real]
  exact key
lemma measurable_tailG : Measurable tailG := by
  have h : tailG = fun z => ProbabilityTheory.cdf (ProbabilityTheory.stdGaussian ℝ) (-z) :=
    funext tailG_eq_cdf
  rw [h]
  exact (StieltjesFunction.mono
    (ProbabilityTheory.cdf (ProbabilityTheory.stdGaussian ℝ))).measurable.comp measurable_neg

def prof (d : ℕ) (K : ℕ) (R : ℝ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    tailG ((((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - R ^ 2 / (max v R) ^ 2) * (d : ℝ) ^ 2
      / Real.sqrt (k : ℝ))
lemma prof_nonneg (d K : ℕ) (R : ℝ) (v : ℝ) : 0 ≤ prof d K R v :=
  Finset.sum_nonneg fun _ _ => tailG_nonneg _
lemma prof_le_K (d K : ℕ) (R : ℝ) (v : ℝ) : prof d K R v ≤ (K : ℝ) := by
  have h1 : prof d K R v ≤ ∑ _k ∈ Finset.Icc 1 K, (1 : ℝ) :=
    Finset.sum_le_sum fun _ _ => tailG_le_one _
  have h2 : (∑ _k ∈ Finset.Icc 1 K, (1 : ℝ)) = (K : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc]; simp
  rw [h2] at h1; exact h1
lemma measurable_prof (d K : ℕ) (R : ℝ) : Measurable (prof d K R) := by
  unfold prof
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact measurable_tailG.comp (by fun_prop)
lemma prof_mono (d K : ℕ) (R : ℝ) (hR : 0 < R) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → prof d K R b ≤ prof d K R a := by
  intro a b _ hab
  refine Finset.sum_le_sum fun k hk => tailG_mono ?_
  have hmaxpos : 0 < max a R := lt_of_lt_of_le hR (le_max_right _ _)
  have hmax : max a R ≤ max b R := max_le_max hab le_rfl
  have hsq : max a R ^ 2 ≤ max b R ^ 2 := pow_le_pow_left₀ hmaxpos.le hmax 2
  have h1 : R ^ 2 / max b R ^ 2 ≤ R ^ 2 / max a R ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg R) (pow_pos hmaxpos 2) hsq
  have h2 : (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - R ^ 2 / (max a R) ^ 2)
      ≤ (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - R ^ 2 / (max b R) ^ 2) := by linarith
  have hkpos : (0 : ℝ) < Real.sqrt (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := by
      have := (Finset.mem_Icc.mp hk).1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    exact Real.sqrt_pos.mpr this
  refine div_le_div_of_nonneg_right ?_ hkpos.le
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

lemma sqrt_le_rpow (d : ℕ) (hd : 1 ≤ d) : Real.sqrt (d:ℝ) ≤ (d:ℝ)^(3/2:ℝ) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have h1 : (d:ℝ)^(3/2:ℝ) = (d:ℝ)^(1/2:ℝ) * (d:ℝ)^(1:ℝ) := by
    rw [← Real.rpow_add hdpos]; norm_num
  rw [h1, Real.rpow_one, ← Real.sqrt_eq_rpow]
  simpa using mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (d:ℝ) by exact_mod_cast hd)
    (Real.sqrt_nonneg d)
lemma rpow_eq_sqrt_mul (d : ℕ) (hd : 1 ≤ d) :
    (d:ℝ)^(3/2:ℝ) = Real.sqrt (d:ℝ) * (d:ℝ) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  rw [show (3/2:ℝ) = 1/2 + 1 by norm_num, Real.rpow_add hdpos, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
lemma sqrt_le_R (d : ℕ) (hd : 100000 ≤ d) {R : ℝ} (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) :
    Real.sqrt (d:ℝ) ≤ R :=
  le_trans (sqrt_le_rpow d (by omega)) hRbig
lemma one_add_inv_pow_le_three (d : ℕ) (hd : 1 ≤ d) : (1 + 1/(2*(d:ℝ)))^(d-1) ≤ 3 := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hexp : (1 + 1/(2*(d:ℝ))) ≤ Real.exp (1/(2*(d:ℝ))) := by
    linarith [Real.add_one_le_exp (1/(2*(d:ℝ)))]
  have hle : (1 + 1/(2*(d:ℝ)))^(d-1) ≤ Real.exp (1/(2*(d:ℝ)))^(d-1) :=
    pow_le_pow_left₀ (by positivity) hexp _
  have h2 : Real.exp (1/(2*(d:ℝ)))^(d-1) = Real.exp ((((d-1:ℕ)):ℝ) * (1/(2*(d:ℝ)))) := by
    rw [← Real.exp_nat_mul]
  rw [h2] at hle
  have hcast : (((d-1:ℕ)):ℝ) = (d:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have h3 : ((((d-1:ℕ)):ℝ) * (1/(2*(d:ℝ)))) ≤ 1 := by
    rw [hcast, mul_one_div, div_le_one (by positivity : (0:ℝ) < 2*(d:ℝ))]
    linarith
  calc (1 + 1/(2*(d:ℝ)))^(d-1) ≤ Real.exp ((((d-1:ℕ)):ℝ) * (1/(2*(d:ℝ)))) := hle
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h3
    _ ≤ 3 := le_of_lt Real.exp_one_lt_three

/-- `(1 + s/v)^{d-1} ≤ 3` for `v ≥ R ≥ d^{3/2}`. -/
lemma one_add_ratio_pow_le (d : ℕ) (hd : 100000 ≤ d) {R v : ℝ} (hR0 : 0 < R)
    (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) (hv : R ≤ v) :
    (1 + (Real.sqrt (d:ℝ)/2)/v)^(d-1) ≤ 3 := by
  have hd1 : 1 ≤ d := by omega
  have hvpos : 0 < v := lt_of_lt_of_le hR0 hv
  have hsR : (Real.sqrt (d:ℝ)/2)/R ≤ 1/(2*(d:ℝ)) := by
    have h3 : Real.sqrt (d:ℝ) * (d:ℝ) ≤ R := by
      rw [← rpow_eq_sqrt_mul d hd1]; exact hRbig
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h3]
  have hsv : (Real.sqrt (d:ℝ)/2)/v ≤ (Real.sqrt (d:ℝ)/2)/R :=
    div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ Real.sqrt (d:ℝ)/2) hR0 hv
  have hbase : 1 + (Real.sqrt (d:ℝ)/2)/v ≤ 1 + 1/(2*(d:ℝ)) := by linarith
  calc (1 + (Real.sqrt (d:ℝ)/2)/v)^(d-1) ≤ (1 + 1/(2*(d:ℝ)))^(d-1) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ 3 := one_add_inv_pow_le_three d hd1


lemma integrableOn_Icc_of_bound {f : ℝ → ℝ} (hf : Measurable f) {a b C : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |f x| ≤ C) : IntegrableOn f (Set.Icc a b) volume := by
  refine IntegrableOn.of_bound ?_ hf.aestronglyMeasurable C ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs]; exact h x hx

lemma intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {a b C : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, |f x| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_Icc_of_bound hf h).mono_set Set.Ioc_subset_Icc_self

/-- `(v + √d/2)^{d-1} ≤ 3 v^{d-1}` for `v ≥ R ≥ d^{3/2}`. -/
lemma add_half_sqrt_pow_le (d : ℕ) (hd : 100000 ≤ d) {R v : ℝ} (hR0 : 0 < R)
    (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) (hv : R ≤ v) :
    (v + Real.sqrt (d:ℝ)/2)^(d-1) ≤ 3 * v^(d-1) := by
  have hvpos : 0 < v := lt_of_lt_of_le hR0 hv
  have h1 : v + Real.sqrt (d:ℝ)/2 = v * (1 + (Real.sqrt (d:ℝ)/2)/v) := by
    field_simp
  rw [h1, mul_pow]
  have hb := one_add_ratio_pow_le d hd hR0 hRbig hv
  calc v^(d-1) * (1 + (Real.sqrt (d:ℝ)/2)/v)^(d-1) ≤ v^(d-1) * 3 :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hvpos.le _)
    _ = 3 * v^(d-1) := by ring

lemma measurable_F_aux (d K : ℕ) (R : ℝ) :
    Measurable (fun v : ℝ => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0)) := by
  refine Measurable.mul ?_ ?_
  · exact ((continuous_id.add continuous_const).pow (d-1)).measurable
  · exact (measurable_prof d K R).comp (measurable_id.max measurable_const)

/-- The substitution `u = v + √d/2` in the annulus integral. -/
lemma integral_shift (d K : ℕ) (R : ℝ) :
    (∫ u in (R - Real.sqrt (d:ℝ)/2)..(2*R + Real.sqrt (d:ℝ)/2),
        u^(d-1) * prof d K R (max (u - Real.sqrt (d:ℝ)/2) 0))
    = ∫ v in (R - Real.sqrt (d:ℝ))..(2*R),
        (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0) := by
  set F : ℝ → ℝ := fun v => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0) with hF
  have h : (fun u : ℝ => u^(d-1) * prof d K R (max (u - Real.sqrt (d:ℝ)/2) 0))
      = fun u => F (u - Real.sqrt (d:ℝ)/2) := by
    funext u; rw [hF]; simp only [sub_add_cancel]
  rw [h, intervalIntegral.integral_comp_sub_right]
  congr 1 <;> ring

/-- The lower piece `[R - √d, R]` of the annulus integral. -/
lemma integral_lower_le (d K : ℕ) (hd : 100000 ≤ d) {R : ℝ} (hR0 : 0 < R)
    (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) :
    (∫ v in (R - Real.sqrt (d:ℝ))..R,
        (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0))
      ≤ 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1) := by
  set F : ℝ → ℝ := fun v => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0) with hF
  have hSQ : Real.sqrt (d:ℝ) ≤ R := sqrt_le_R d hd hRbig
  have hle : R - Real.sqrt (d:ℝ) ≤ R := by linarith [Real.sqrt_nonneg (d:ℝ)]
  have hFm : Measurable F := by rw [hF]; exact measurable_F_aux d K R
  have hbound : ∀ v ∈ Set.Icc (R - Real.sqrt (d:ℝ)) R, |F v| ≤ 3 * (K:ℝ) * R^(d-1) := by
    intro v hv
    have hv0 : 0 ≤ v := by linarith [hv.1, hSQ]
    have hvs : 0 ≤ v + Real.sqrt (d:ℝ)/2 := by positivity
    have hvRs : v + Real.sqrt (d:ℝ)/2 ≤ R + Real.sqrt (d:ℝ)/2 := by linarith [hv.2]
    have hp : (v + Real.sqrt (d:ℝ)/2)^(d-1) ≤ 3 * R^(d-1) :=
      le_trans (pow_le_pow_left₀ hvs hvRs _) (add_half_sqrt_pow_le d hd hR0 hRbig le_rfl)
    have hmax : max v 0 = v := max_eq_left hv0
    simp only [hF]
    rw [hmax, abs_of_nonneg (mul_nonneg (pow_nonneg hvs _) (prof_nonneg d K R v))]
    calc (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R v
        ≤ (3 * R^(d-1)) * (K:ℝ) :=
          mul_le_mul hp (prof_le_K d K R v) (prof_nonneg d K R v) (by positivity)
      _ = 3 * (K:ℝ) * R^(d-1) := by ring
  have hFint : IntervalIntegrable F volume (R - Real.sqrt (d:ℝ)) R :=
    intervalIntegrable_of_bound hFm hle hbound
  have hCint : IntervalIntegrable (fun _ : ℝ => 3 * (K:ℝ) * R^(d-1)) volume
      (R - Real.sqrt (d:ℝ)) R := intervalIntegrable_const
  calc (∫ v in (R - Real.sqrt (d:ℝ))..R, F v)
      ≤ ∫ v in (R - Real.sqrt (d:ℝ))..R, (3 * (K:ℝ) * R^(d-1)) :=
        intervalIntegral.integral_mono_on hle hFint hCint
          (fun v hv => le_trans (le_abs_self _) (hbound v hv))
    _ = 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

/-- The upper piece `[R, 2R]` of the annulus integral. -/
lemma integral_upper_le (d K : ℕ) (hd : 100000 ≤ d) {R : ℝ} (hR0 : 0 < R)
    (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) :
    (∫ v in R..(2*R), (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0))
      ≤ 3 * ∫ v in R..(2*R), v^(d-1) * prof d K R v := by
  set F : ℝ → ℝ := fun v => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0) with hF
  set G : ℝ → ℝ := fun v => 3 * (v^(d-1) * prof d K R v) with hG
  have hle : R ≤ 2*R := by linarith
  have hFm : Measurable F := by rw [hF]; exact measurable_F_aux d K R
  have hGm : Measurable G := by
    rw [hG]
    refine Measurable.const_mul ?_ 3
    exact ((continuous_id.pow (d-1)).measurable).mul (measurable_prof d K R)
  have hC2 : (0:ℝ) ≤ 3 * (K:ℝ) * (2*R)^(d-1) := by positivity
  have hboundF : ∀ v ∈ Set.Icc R (2*R), |F v| ≤ 3 * (K:ℝ) * (2*R)^(d-1) := by
    intro v hv
    have hvR : R ≤ v := hv.1
    have hv2 : v ≤ 2*R := hv.2
    have hv0 : 0 ≤ v := le_trans hR0.le hvR
    have hvs : 0 ≤ v + Real.sqrt (d:ℝ)/2 := by positivity
    have hp : (v + Real.sqrt (d:ℝ)/2)^(d-1) ≤ 3 * v^(d-1) :=
      add_half_sqrt_pow_le d hd hR0 hRbig hvR
    have hp2 : (v + Real.sqrt (d:ℝ)/2)^(d-1) ≤ 3 * (2*R)^(d-1) :=
      le_trans hp (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hv2 _) (by norm_num))
    have hmax : max v 0 = v := max_eq_left hv0
    simp only [hF]
    rw [hmax, abs_of_nonneg (mul_nonneg (pow_nonneg hvs _) (prof_nonneg d K R v))]
    calc (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R v
        ≤ (3 * (2*R)^(d-1)) * (K:ℝ) :=
          mul_le_mul hp2 (prof_le_K d K R v) (prof_nonneg d K R v) (by positivity)
      _ = 3 * (K:ℝ) * (2*R)^(d-1) := by ring
  have hboundG : ∀ v ∈ Set.Icc R (2*R), |G v| ≤ 3 * (K:ℝ) * (2*R)^(d-1) := by
    intro v hv
    have hvR : R ≤ v := hv.1
    have hv2 : v ≤ 2*R := hv.2
    have hv0 : 0 ≤ v := le_trans hR0.le hvR
    have hp : v^(d-1) ≤ (2*R)^(d-1) := pow_le_pow_left₀ hv0 hv2 _
    simp only [hG]
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hv0 _) (prof_nonneg d K R v)))]
    calc 3 * (v^(d-1) * prof d K R v)
        ≤ 3 * ((2*R)^(d-1) * (K:ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul hp (prof_le_K d K R v) (prof_nonneg d K R v) (pow_nonneg (by linarith) _)
      _ = 3 * (K:ℝ) * (2*R)^(d-1) := by ring
  have hFint : IntervalIntegrable F volume R (2*R) := intervalIntegrable_of_bound hFm hle hboundF
  have hGint : IntervalIntegrable G volume R (2*R) := intervalIntegrable_of_bound hGm hle hboundG
  calc (∫ v in R..(2*R), F v)
      ≤ ∫ v in R..(2*R), G v :=
        intervalIntegral.integral_mono_on hle hFint hGint (fun v hv => by
          have hvR : R ≤ v := hv.1
          have hmax : max v 0 = v := max_eq_left (le_trans hR0.le hvR)
          have hp : (v + Real.sqrt (d:ℝ)/2)^(d-1) ≤ 3 * v^(d-1) :=
            add_half_sqrt_pow_le d hd hR0 hRbig hvR
          simp only [hF, hG]
          rw [hmax]
          calc (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R v
              ≤ (3 * v^(d-1)) * prof d K R v :=
                mul_le_mul_of_nonneg_right hp (prof_nonneg d K R v)
            _ = 3 * (v^(d-1) * prof d K R v) := by ring)
    _ = 3 * ∫ v in R..(2*R), v^(d-1) * prof d K R v := by
        rw [intervalIntegral.integral_const_mul]

/-- The substitution `v = R y` on `[R, 2R]`. -/
lemma integral_scale (d K : ℕ) (hd : 1 ≤ d) {R : ℝ} (hR : R ≠ 0) :
    (∫ v in R..(2*R), v^(d-1) * prof d K R v)
      = R^d * ∫ y in (1:ℝ)..2, y^(d-1) * prof d K R (R*y) := by
  have hsub := intervalIntegral.integral_comp_mul_left (a := (1:ℝ)) (b := 2)
    (fun v : ℝ => v^(d-1) * prof d K R v) hR
  simp only [smul_eq_mul, mul_one, mul_comm R 2] at hsub
  have hA : (∫ y in (1:ℝ)..2, (R*y)^(d-1) * prof d K R (R*y))
      = R^(d-1) * ∫ y in (1:ℝ)..2, y^(d-1) * prof d K R (R*y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [mul_pow]; ring
  have h2 : R * (∫ y in (1:ℝ)..2, (R*y)^(d-1) * prof d K R (R*y))
      = ∫ v in R..(2*R), v^(d-1) * prof d K R v := by
    rw [hsub, ← mul_assoc, mul_inv_cancel₀ hR, one_mul]
  have hpow : R * R^(d-1) = R^d := by
    have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
    rw [← pow_succ']; congr 1; omega
  rw [← h2, hA, ← mul_assoc, hpow]

/-- Comparing the `[1,2]` integral with the shell hypothesis. -/
lemma integral_shell_le (d K : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hshell : ∫ y in (1 : ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
          (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      ≤ 10 ^ 6 * (d : ℝ) ^ 3) :
    (∫ y in (1:ℝ)..2, y^(d-1) * prof d K R (R*y)) ≤ 10^6 * (d:ℝ)^3 := by
  have hR0 : (0:ℝ) < R := by linarith
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hcongr : (∫ y in (1:ℝ)..2, y^(d-1) * prof d K R (R*y))
      = ∫ y in (1:ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
          (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z}) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hy
    have hy1 : 1 ≤ y := hy.1
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
    have hmax : max (R*y) R = R*y := max_eq_left (by nlinarith)
    have hRy : R^2/(R*y)^2 = 1/y^2 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hprof : prof d K R (R*y)
        = ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
            (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z} := by
      simp only [prof, tailG, hmax, hRy]
    rw [hprof]
  rw [hcongr]
  exact hshell

lemma K_bound_seventeen (d K : ℕ) (hd : 1 ≤ d)
    (hK : (K:ℝ) ≤ 16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1) : (K:ℝ) ≤ 17 * (d:ℝ)^3 := by
  have hd1R : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hlogd : Real.log (d:ℝ) ≤ (d:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (d:ℝ) by linarith)
    linarith
  have h16 : 16 * (d:ℝ)^2 * Real.log (d:ℝ) ≤ 16 * (d:ℝ)^3 := by
    have h2 : (0:ℝ) ≤ 16 * (d:ℝ)^2 := by positivity
    nlinarith [hlogd, h2]
  have hp1 : (1:ℝ) ≤ (d:ℝ)^3 := one_le_pow₀ hd1R
  linarith [hK, h16, hp1]

lemma sqrt_d_le_d (d : ℕ) (hd : 1 ≤ d) : Real.sqrt (d:ℝ) ≤ (d:ℝ) := by
  have h1 : 1 ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg d), Real.sqrt_nonneg (d:ℝ)]

lemma d_le_R (d : ℕ) (hd : 1 ≤ d) {R : ℝ} (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) : (d:ℝ) ≤ R := by
  have h1 : Real.sqrt (d:ℝ) * (d:ℝ) ≤ R := by
    rw [← rpow_eq_sqrt_mul d hd]; exact hRbig
  have h2 : 1 ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  calc (d:ℝ) = 1 * (d:ℝ) := by ring
    _ ≤ Real.sqrt (d:ℝ) * (d:ℝ) := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg d)
    _ ≤ R := h1

lemma K_sqrt_le (d K : ℕ) (hd : 1 ≤ d) (hK : (K:ℝ) ≤ 16 * (d:ℝ)^2 * Real.log (d:ℝ) + 1)
    {R : ℝ} (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) :
    3 * (K:ℝ) * Real.sqrt (d:ℝ) ≤ 7 * 10^6 * (d:ℝ)^3 * R := by
  have hKm : (K:ℝ) ≤ 17 * (d:ℝ)^3 := K_bound_seventeen d K hd hK
  have hsq : Real.sqrt (d:ℝ) ≤ (d:ℝ) := sqrt_d_le_d d hd
  have hdR : (d:ℝ) ≤ R := d_le_R d hd hRbig
  have hdn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  have hsqnn : (0:ℝ) ≤ Real.sqrt (d:ℝ) := Real.sqrt_nonneg _
  have h1 : 3 * (K:ℝ) * Real.sqrt (d:ℝ) ≤ 3 * (17 * (d:ℝ)^3) * (d:ℝ) := by
    nlinarith [hKm, hsq, hdn, hsqnn]
  have h2 : 3 * (17 * (d:ℝ)^3) * (d:ℝ) ≤ 7 * 10^6 * (d:ℝ)^3 * R := by
    nlinarith [hdR, hdn]
  linarith

/-- `F v = (v + √d/2)^{d-1} prof d K R (max v 0)` is interval integrable on any subinterval
of `[R - √d, 2R]`. -/
lemma intervalIntegrable_F (d K : ℕ) (hd : 100000 ≤ d) {R : ℝ} (hR0 : 0 < R)
    (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R) {a b : ℝ} (hab : a ≤ b) (ha : R - Real.sqrt (d:ℝ) ≤ a)
    (hb : b ≤ 2*R) :
    IntervalIntegrable (fun v : ℝ => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0))
      volume a b := by
  have hSQ : Real.sqrt (d:ℝ) ≤ R := sqrt_le_R d hd hRbig
  have hSR : Real.sqrt (d:ℝ)/2 ≤ R := by linarith
  have hbound : ∀ v ∈ Set.Icc a b,
      |(v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0)| ≤ (3*R)^(d-1) * (K:ℝ) := by
    intro v hv
    have hv1 : R - Real.sqrt (d:ℝ) ≤ v := le_trans ha hv.1
    have hv2 : v ≤ 2*R := le_trans hv.2 hb
    have hvs0 : 0 ≤ v + Real.sqrt (d:ℝ)/2 := by linarith
    have hvs : v + Real.sqrt (d:ℝ)/2 ≤ 3*R := by linarith
    have hp : (v + Real.sqrt (d:ℝ)/2)^(d-1) ≤ (3*R)^(d-1) := pow_le_pow_left₀ hvs0 hvs _
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hvs0 _) (prof_nonneg d K R _))]
    exact mul_le_mul hp (prof_le_K d K R _) (prof_nonneg d K R _) (pow_nonneg (by linarith) _)
  exact intervalIntegrable_of_bound (measurable_F_aux d K R) hab hbound

/-- **The analytic core.**  The annulus integral is bounded by the shell integral plus the
lower piece. -/
theorem integral_main_le (d K : ℕ) (hd : 100000 ≤ d) {R : ℝ} (hR : 1 ≤ R)
    (hRbig : (d:ℝ)^(3/2:ℝ) ≤ R)
    (hshell : ∫ y in (1 : ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K, tailG ((((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2)
          * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ)))
      ≤ 10 ^ 6 * (d : ℝ) ^ 3) :
    (∫ u in (R - Real.sqrt (d:ℝ)/2)..(2*R + Real.sqrt (d:ℝ)/2),
        u^(d-1) * prof d K R (max (u - Real.sqrt (d:ℝ)/2) 0))
      ≤ 3 * 10^6 * (d:ℝ)^3 * R^d + 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1) := by
  have hd1 : 1 ≤ d := by omega
  have hR0 : (0:ℝ) < R := by linarith
  have hint1 : IntervalIntegrable
      (fun v : ℝ => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0)) volume
      (R - Real.sqrt (d:ℝ)) R :=
    intervalIntegrable_F d K hd hR0 hRbig (by linarith [Real.sqrt_nonneg (d:ℝ)]) le_rfl (by linarith)
  have hint2 : IntervalIntegrable
      (fun v : ℝ => (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0)) volume R (2*R) :=
    intervalIntegrable_F d K hd hR0 hRbig (by linarith) (by linarith [Real.sqrt_nonneg (d:ℝ)]) le_rfl
  calc (∫ u in (R - Real.sqrt (d:ℝ)/2)..(2*R + Real.sqrt (d:ℝ)/2),
          u^(d-1) * prof d K R (max (u - Real.sqrt (d:ℝ)/2) 0))
      = ∫ v in (R - Real.sqrt (d:ℝ))..(2*R),
          (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0) := integral_shift d K R
    _ = (∫ v in (R - Real.sqrt (d:ℝ))..R,
          (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0))
        + ∫ v in R..(2*R),
          (v + Real.sqrt (d:ℝ)/2)^(d-1) * prof d K R (max v 0) :=
        (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    _ ≤ 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1)
        + 3 * ∫ v in R..(2*R), v^(d-1) * prof d K R v :=
        add_le_add (integral_lower_le d K hd hR0 hRbig) (integral_upper_le d K hd hR0 hRbig)
    _ = 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1)
        + 3 * (R^d * ∫ y in (1:ℝ)..2, y^(d-1) * prof d K R (R*y)) := by
        rw [integral_scale d K hd1 (ne_of_gt hR0)]
    _ ≤ 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1) + 3 * (R^d * (10^6 * (d:ℝ)^3)) := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (integral_shell_le d K hR hshell) (pow_nonneg hR0.le _))
          (by norm_num)
    _ = 3 * 10^6 * (d:ℝ)^3 * R^d + 3 * (K:ℝ) * Real.sqrt (d:ℝ) * R^(d-1) := by ring

theorem sum_tailG_annulus_le_of_shell {d : ℕ} (hd : 100000 ≤ d) {K : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hRbig : (d : ℝ) ^ (3 / 2 : ℝ) ≤ R)
    (hK : (K : ℝ) ≤ 16 * (d : ℝ) ^ 2 * Real.log (d : ℝ) + 1)
    (hshell : ∫ y in (1 : ℝ)..2, y ^ (d - 1) *
        (∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
          (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - 1 / y ^ 2) * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      ≤ 10 ^ 6 * (d : ℝ) ^ 3) :
    (∑ x ∈ ((Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) (2 * R)).toFinset.filter
        (fun x : Fin d → ℤ => R < ‖Commons.GeometryOfNumbers.Counting.intVec x‖)),
      ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
        (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - R ^ 2 / ‖Commons.GeometryOfNumbers.Counting.intVec x‖ ^ 2)
          * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      ≤ 10 ^ 7 * (d : ℝ) ^ 4
          * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
          * R ^ d := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hR0 : (0:ℝ) < R := by linarith
  have hWnn : 0 ≤ (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
    ENNReal.toReal_nonneg
  have hmain := sum_int_points_annulus_le_radial (d := d) hd0 (r := R) (T := 2 * R)
      (by linarith) (by linarith) (prof d K R) (prof_mono d K R hR0) (prof_nonneg d K R)
  have hLHS : (∑ x ∈ ((Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) (2 * R)).toFinset.filter
        (fun x : Fin d → ℤ => R < ‖Commons.GeometryOfNumbers.Counting.intVec x‖)),
      ∑ k ∈ Finset.Icc 1 K, (ProbabilityTheory.stdGaussian ℝ).real {z : ℝ |
        (((1 - 1 / (d : ℝ)) ^ 2)⁻¹ - R ^ 2 / ‖Commons.GeometryOfNumbers.Counting.intVec x‖ ^ 2)
          * (d : ℝ) ^ 2 / Real.sqrt (k : ℝ) ≤ z})
      = ∑ x ∈ ((Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) (2 * R)).toFinset.filter
        (fun x : Fin d → ℤ => R < ‖Commons.GeometryOfNumbers.Counting.intVec x‖)),
        prof d K R ‖Commons.GeometryOfNumbers.Counting.intVec x‖ := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_filter] at hx
    have hmax : max ‖Commons.GeometryOfNumbers.Counting.intVec x‖ R
        = ‖Commons.GeometryOfNumbers.Counting.intVec x‖ := max_eq_left (le_of_lt hx.2)
    simp only [prof, tailG, hmax]
  rw [hLHS]
  refine le_trans hmain ?_
  have hInt := integral_main_le d K hd hR hRbig hshell
  have hcore : (d:ℝ) * (3*10^6*(d:ℝ)^3*R^d + 3*(K:ℝ)*Real.sqrt (d:ℝ)*R^(d-1))
      ≤ 10^7 * (d:ℝ)^4 * R^d := by
    have hkey : 3 * (K:ℝ) * Real.sqrt (d:ℝ) ≤ 7 * 10^6 * (d:ℝ)^3 * R :=
      K_sqrt_le d K hd1 hK hRbig
    have hRp : (0:ℝ) ≤ R^(d-1) := pow_nonneg hR0.le _
    have hdn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hmul : 3 * (K:ℝ) * Real.sqrt (d:ℝ) * ((d:ℝ) * R^(d-1))
        ≤ 7 * 10^6 * (d:ℝ)^3 * R * ((d:ℝ) * R^(d-1)) :=
      mul_le_mul_of_nonneg_right hkey (mul_nonneg hdn hRp)
    have hRd : R * R^(d-1) = R^d := by
      rw [← pow_succ']; congr 1; omega
    calc (d:ℝ) * (3*10^6*(d:ℝ)^3*R^d + 3*(K:ℝ)*Real.sqrt (d:ℝ)*R^(d-1))
        = 3*10^6*(d:ℝ)^4*R^d + 3*(K:ℝ)*Real.sqrt (d:ℝ) * ((d:ℝ)*R^(d-1)) := by ring
      _ ≤ 3*10^6*(d:ℝ)^4*R^d + 7*10^6*(d:ℝ)^4*(R*R^(d-1)) := by
          have e : 7 * 10^6 * (d:ℝ)^3 * R * ((d:ℝ) * R^(d-1))
              = 7 * 10^6 * (d:ℝ)^4 * (R*R^(d-1)) := by ring
          linarith [hmul, e.le, e.ge]
      _ = 10^7 * (d:ℝ)^4 * R^d := by rw [hRd]; ring
  calc (d:ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
        * (∫ u in (R - Real.sqrt (d:ℝ)/2)..(2*R + Real.sqrt (d:ℝ)/2),
            u^(d-1) * prof d K R (max (u - Real.sqrt (d:ℝ)/2) 0))
      ≤ (d:ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
          * (3*10^6*(d:ℝ)^3*R^d + 3*(K:ℝ)*Real.sqrt (d:ℝ)*R^(d-1)) :=
        mul_le_mul_of_nonneg_left hInt (mul_nonneg (Nat.cast_nonneg d) hWnn)
    _ ≤ 10^7 * (d:ℝ)^4
          * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * R^d := by
        calc (d:ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
              * (3*10^6*(d:ℝ)^3*R^d + 3*(K:ℝ)*Real.sqrt (d:ℝ)*R^(d-1))
            = (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
              * ((d:ℝ) * (3*10^6*(d:ℝ)^3*R^d + 3*(K:ℝ)*Real.sqrt (d:ℝ)*R^(d-1))) := by ring
          _ ≤ (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
              * (10^7 * (d:ℝ)^4 * R^d) := mul_le_mul_of_nonneg_left hcore hWnn
          _ = 10^7 * (d:ℝ)^4
              * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * R^d := by ring

end

end Commons.GeometryOfNumbers.Counting
