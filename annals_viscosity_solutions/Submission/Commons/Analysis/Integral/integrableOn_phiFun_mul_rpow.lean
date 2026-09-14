import Mathlib
import Submission.Commons.Analysis.Integral.integral_rpow_inv_sqrt_cos_le
import Submission.Commons.Analysis.Integral.integrableOn_abs_sub_rpow_Icc

/-!
# Integrability of the `phiFun` transfer integrand `phiFun v * v ^ (-3/2)` on `(0, ∞)`

The scalar transfer function of the circle-average transfer is

`phiFun v = (1/(2π)) ∫_θ ((1 + v² + 2 v cos θ) ^ (-(1:ℝ)/2) - 1) dθ`,

and this file proves that `v ↦ phiFun v * v ^ (-(3:ℝ)/2)` is Lebesgue integrable on `(0, ∞)`.

The proof is elementary and splits `(0, ∞)` into three regions:

* on `(0, 1/2]` the θ-integrand is bounded by `6 v`, so the product is `≤ 6 v ^ (-1/2)`;
* on `[1/2, 2]` the θ-integral is bounded by `100 |v - 1| ^ (-1/2) + 2π` (the logarithmic
  divergence at `v = 1` is integrable), so the product is `≤ 200 (|v - 1| ^ (-1/2) + 1)`;
* on `[2, ∞)` the θ-integrand is bounded by `2`, so the product is `≤ 2 v ^ (-3/2)`.

Each dominating function is integrable on its region.
-/

namespace Commons.Analysis.Integral

open MeasureTheory Set Real
open scoped Topology

private lemma measurable_phiIntegral :
    Measurable (fun v : ℝ => ∫ θ in (0)..(2*Real.pi),
      ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)) := by
  have h : Measurable (fun p : ℝ × ℝ => (1 + p.1^2 + 2*p.1*Real.cos p.2) ^ (-(1:ℝ)/2) - 1) := by fun_prop
  have h2 : StronglyMeasurable (fun p : ℝ × ℝ =>
      (Set.univ ×ˢ Set.Ioc (0:ℝ) (2*Real.pi)).indicator
        (fun q : ℝ × ℝ => ((1 + q.1^2 + 2*q.1*Real.cos q.2) ^ (-(1:ℝ)/2) - 1)) p) :=
    h.stronglyMeasurable.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
  have h3 : StronglyMeasurable (fun v : ℝ => ∫ θ, (Set.univ ×ˢ Set.Ioc (0:ℝ) (2*Real.pi)).indicator
        (fun q : ℝ × ℝ => ((1 + q.1^2 + 2*q.1*Real.cos q.2) ^ (-(1:ℝ)/2) - 1)) (v, θ)) :=
    h2.integral_prod_right'
  have hEq : (fun v : ℝ => ∫ θ in (0)..(2*Real.pi),
      ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1))
      = fun v : ℝ => ∫ θ, (Set.univ ×ˢ Set.Ioc (0:ℝ) (2*Real.pi)).indicator
          (fun q : ℝ × ℝ => ((1 + q.1^2 + 2*q.1*Real.cos q.2) ^ (-(1:ℝ)/2) - 1)) (v, θ) := by
    funext v
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    by_cases hθ : θ ∈ Set.Ioc (0:ℝ) (2*Real.pi)
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem (by simpa using hθ)]
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem (by simpa using hθ)]
  rw [hEq]
  exact h3.measurable

private lemma abs_phiIntegral_le_small {v : ℝ} (hv0 : 0 < v) (hv : v ≤ 1/2) :
    |∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)| ≤ 12*Real.pi*v := by
  have hbase_pos : ∀ θ : ℝ, 0 < 1 + v^2 + 2*v*Real.cos θ := by
    intro θ
    have hc : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have h1 : 0 ≤ 1 + Real.cos θ := by linarith
    nlinarith [sq_nonneg (1-v), mul_nonneg (by linarith : (0:ℝ) ≤ 2*v) h1]
  have hkey : ∀ θ : ℝ, |(1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1| ≤ 6*v := by
    intro θ
    have hb := hbase_pos θ
    have hspos : 0 < Real.sqrt (1 + v^2 + 2*v*Real.cos θ) := Real.sqrt_pos.mpr hb
    have hq : Real.sqrt (1 + v^2 + 2*v*Real.cos θ) * Real.sqrt (1 + v^2 + 2*v*Real.cos θ)
        = 1 + v^2 + 2*v*Real.cos θ := by
      simpa [pow_two] using Real.sq_sqrt (le_of_lt hb)
    rw [show (-(1:ℝ)/2) = -(1/2) by ring, Real.rpow_neg (le_of_lt hb), ← Real.sqrt_eq_rpow]
    have hsge : (1:ℝ)/2 ≤ Real.sqrt (1 + v^2 + 2*v*Real.cos θ) := by
      rw [Real.le_sqrt (by norm_num) (le_of_lt hb)]
      nlinarith [sq_nonneg (1-v), Real.neg_one_le_cos θ,
        mul_nonneg (by linarith : (0:ℝ) ≤ 2*v) (by linarith [Real.neg_one_le_cos θ] : (0:ℝ) ≤ 1 + Real.cos θ)]
    have hfac : 1 - Real.sqrt (1 + v^2 + 2*v*Real.cos θ)
        = (1 - (1 + v^2 + 2*v*Real.cos θ)) / (1 + Real.sqrt (1 + v^2 + 2*v*Real.cos θ)) := by
      rw [eq_div_iff (by positivity : (1:ℝ) + Real.sqrt (1 + v^2 + 2*v*Real.cos θ) ≠ 0)]
      nlinarith [hq]
    have hbound : |1 - (1 + v^2 + 2*v*Real.cos θ)| ≤ 3*v := by
      have h1 : 1 - (1 + v^2 + 2*v*Real.cos θ) = -(v^2) - 2*v*Real.cos θ := by ring
      rw [h1]
      have h2 : |-(v^2) - 2*v*Real.cos θ| ≤ v^2 + 2*v*|Real.cos θ| := by
        calc |-(v^2) - 2*v*Real.cos θ| ≤ |-(v^2)| + |2*v*Real.cos θ| := abs_sub _ _
          _ = v^2 + 2*v*|Real.cos θ| := by
              rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ v^2),
                  abs_of_pos hv0, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have h3 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
      nlinarith [h2, h3, hv0, hv, sq_nonneg v]
    have hnum : |1 - Real.sqrt (1 + v^2 + 2*v*Real.cos θ)| ≤ 3*v := by
      rw [hfac, abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + Real.sqrt (1 + v^2 + 2*v*Real.cos θ))]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + Real.sqrt (1 + v^2 + 2*v*Real.cos θ))]
      nlinarith [hbound]
    have hcomp : (Real.sqrt (1 + v^2 + 2*v*Real.cos θ))⁻¹ - 1
        = (1 - Real.sqrt (1 + v^2 + 2*v*Real.cos θ)) / Real.sqrt (1 + v^2 + 2*v*Real.cos θ) := by
      rw [sub_div, div_self (ne_of_gt hspos), one_div]
    rw [hcomp]
    rw [abs_div, abs_of_pos hspos]
    rw [div_le_iff₀ hspos]
    nlinarith [hnum, hsge]
  have hcont : Continuous (fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1) := by
    refine (Continuous.rpow_const ?_ ?_).sub continuous_const
    · fun_prop
    · intro θ; left; exact ne_of_gt (hbase_pos θ)
  calc |∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)|
      ≤ ∫ θ in (0)..(2*Real.pi), |(1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1| := by
        have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)
          (by positivity : (0:ℝ) ≤ 2*Real.pi)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∫ θ in (0)..(2*Real.pi), (6*v:ℝ) := by
        apply intervalIntegral.integral_mono_on (by positivity : (0:ℝ) ≤ 2*Real.pi)
        · exact hcont.abs.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro θ _; exact hkey θ
    _ = 12 * Real.pi * v := by rw [intervalIntegral.integral_const]; simp; ring

private lemma abs_phiIntegral_le_large {v : ℝ} (hv : 2 ≤ v) :
    |∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)| ≤ 4*Real.pi := by
  have hv0 : (0:ℝ) < v := by linarith
  have hbase_pos : ∀ θ : ℝ, 0 < 1 + v^2 + 2*v*Real.cos θ := by
    intro θ
    have hc : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have h1 : 0 ≤ 1 + Real.cos θ := by linarith
    nlinarith [sq_nonneg (v-1), mul_nonneg (by linarith : (0:ℝ) ≤ 2*v) h1]
  have hbase_ge : ∀ θ : ℝ, 1 ≤ 1 + v^2 + 2*v*Real.cos θ := by
    intro θ
    have hc : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have h1 : 0 ≤ 1 + Real.cos θ := by linarith
    nlinarith [sq_nonneg (v-1), mul_nonneg (by linarith : (0:ℝ) ≤ 2*v) h1]
  have hbound : ∀ θ : ℝ, |(1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1| ≤ 2 := by
    intro θ
    have hle : (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) ≤ 1 := by
      rw [show (-(1:ℝ)/2) = -(1/2) by ring, Real.rpow_neg (le_of_lt (hbase_pos θ)), ← Real.sqrt_eq_rpow]
      rw [inv_le_one₀ (Real.sqrt_pos.mpr (hbase_pos θ))]
      exact Real.one_le_sqrt.mpr (hbase_ge θ)
    have hnn : 0 ≤ (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) := Real.rpow_nonneg (le_of_lt (hbase_pos θ)) _
    rw [abs_le]
    constructor <;> linarith
  have hcont : Continuous (fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1) := by
    refine (Continuous.rpow_const ?_ ?_).sub continuous_const
    · fun_prop
    · intro θ; left; exact ne_of_gt (hbase_pos θ)
  calc |∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)|
      ≤ ∫ θ in (0)..(2*Real.pi), |(1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1| := by
        have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)
          (by positivity : (0:ℝ) ≤ 2*Real.pi)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∫ θ in (0)..(2*Real.pi), (2:ℝ) := by
        apply intervalIntegral.integral_mono_on (by positivity : (0:ℝ) ≤ 2*Real.pi)
        · exact hcont.abs.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro θ _; exact hbound θ
    _ = 4 * Real.pi := by rw [intervalIntegral.integral_const]; simp; ring


private lemma abs_phiIntegral_le_mid {v : ℝ} (hv1 : (1:ℝ)/2 ≤ v) (hv2 : v ≤ 2) (hne : v ≠ 1) :
    |∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)|
      ≤ 100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi := by
  have hbpos : ∀ θ : ℝ, 0 < 1 + v^2 + 2*v*Real.cos θ := by
    intro θ
    have h1 : 1 + v^2 + 2*v*Real.cos θ = (v-1)^2 + 2*v*(1+Real.cos θ) := by ring
    rw [h1]
    have h2 : 0 ≤ 2*v*(1+Real.cos θ) :=
      mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos θ])
    have h3 : 0 < (v-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    linarith
  have hcontB : Continuous (fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2)) := by
    refine Continuous.rpow_const ?_ ?_
    · fun_prop
    · intro θ; left; exact ne_of_gt (hbpos θ)
  have hcont : Continuous (fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1) :=
    hcontB.sub continuous_const
  have hpt : ∀ θ : ℝ, |(1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1|
      ≤ (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) + 1 := by
    intro θ
    have hnn : 0 ≤ (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) :=
      Real.rpow_nonneg (hbpos θ).le _
    rw [abs_le]; constructor <;> linarith
  have hIntB : ∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) + 1)
      = (∫ θ in (0)..(2*Real.pi), (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2)) + 2*Real.pi := by
    rw [intervalIntegral.integral_add (hcontB.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const]; simp
  calc |∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)|
      ≤ ∫ θ in (0)..(2*Real.pi), |(1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1| := by
        have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun θ : ℝ => (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)
          (by positivity : (0:ℝ) ≤ 2*Real.pi)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∫ θ in (0)..(2*Real.pi), ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) + 1) := by
        apply intervalIntegral.integral_mono_on (by positivity : (0:ℝ) ≤ 2*Real.pi)
        · exact hcont.abs.intervalIntegrable _ _
        · exact (hcontB.add continuous_const).intervalIntegrable _ _
        · intro θ _; exact hpt θ
    _ = (∫ θ in (0)..(2*Real.pi), (1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2)) + 2*Real.pi := hIntB
    _ ≤ 100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi := by
        linarith [integral_rpow_inv_sqrt_cos_le hv1 hv2 hne]

theorem integrableOn_phiFun_mul_rpow :
    MeasureTheory.IntegrableOn
      (fun v : ℝ =>
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
            (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
          * v ^ (-(3 : ℝ) / 2))
      (Set.Ioi 0) MeasureTheory.volume := by
  set F : ℝ → ℝ := fun v => ∫ θ in (0)..(2*Real.pi),
      ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1) with hF
  set f : ℝ → ℝ := fun v => ((1 / (2 * Real.pi)) * F v) * v ^ (-(3:ℝ)/2) with hf
  have hFmeas : Measurable F := by rw [hF]; exact measurable_phiIntegral
  have hfmeas : Measurable f := by
    rw [hf]; exact (measurable_const.mul hFmeas).mul (by fun_prop)
  have hA : IntegrableOn f (Ioc 0 (1/2)) := by
    have hbase : IntegrableOn (fun v : ℝ => v ^ (-(1:ℝ)/2)) (Ioc 0 (1/2)) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1/2)).mpr (by norm_num)
    have hdom : IntegrableOn (fun v : ℝ => 6 * v ^ (-(1:ℝ)/2)) (Ioc 0 (1/2)) := hbase.const_mul 6
    refine Integrable.mono' hdom hfmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hv0 : 0 < v := hv.1
    have h1 : |F v| ≤ 12*Real.pi*v := by rw [hF]; exact abs_phiIntegral_le_small hv0 hv.2
    rw [hf]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi)),
        abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
    have h2 : v ^ (-(1:ℝ)/2) = v * v ^ (-(3:ℝ)/2) := by
      rw [show (-(1:ℝ)/2) = 1 + (-(3:ℝ)/2) by norm_num]
      rw [Real.rpow_add hv0, Real.rpow_one]
    calc 1 / (2 * Real.pi) * |F v| * v ^ (-(3:ℝ)/2)
        ≤ 1 / (2 * Real.pi) * (12 * Real.pi * v) * v ^ (-(3:ℝ)/2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv0.le _)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 6 * (v * v ^ (-(3:ℝ)/2)) := by field_simp; ring
      _ = 6 * v ^ (-(1:ℝ)/2) := by rw [← h2]
  have hB : IntegrableOn f (Icc (1/2) 2) := by
    have hbase : IntegrableOn (fun v : ℝ => |v - 1| ^ (-(1:ℝ)/2)) (Icc (1/2) 2) :=
      integrableOn_abs_sub_rpow_Icc (by norm_num) (by norm_num : (-1:ℝ) < (-(1:ℝ))/2)
    have hone : IntegrableOn (fun v : ℝ => (1:ℝ)) (Icc (1/2) 2) :=
      integrableOn_const (by simp)
    have hdom : IntegrableOn (fun v : ℝ => 200 * (|v - 1| ^ (-(1:ℝ)/2) + 1)) (Icc (1/2) 2) :=
      (hbase.add hone).const_mul 200
    refine Integrable.mono' hdom hfmeas.aestronglyMeasurable ?_
    have hne_ae : ∀ᵐ v ∂(volume.restrict (Icc (1/2:ℝ) 2)), v ≠ 1 :=
      ae_restrict_of_ae (by rw [MeasureTheory.ae_iff]; simp)
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne_ae] with v hv hvne
    have hv0 : 0 < v := by linarith [hv.1]
    have h1 : |F v| ≤ 100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi := by
      rw [hF]; exact abs_phiIntegral_le_mid hv.1 hv.2 hvne
    have hpowle : v ^ (-(3:ℝ)/2) ≤ 4 := by
      have hpos : 0 < v := hv0
      have h1' : (1/2:ℝ) ^ (3/2:ℝ) ≤ v ^ (3/2:ℝ) :=
        Real.rpow_le_rpow (by norm_num) hv.1 (by norm_num)
      have h2' : v ^ (-(3:ℝ)/2) = (v ^ ((3:ℝ)/2))⁻¹ := by
        rw [show (-(3:ℝ)/2) = -((3:ℝ)/2) by ring, Real.rpow_neg hpos.le]
      have h3' : (0:ℝ) < (1/2:ℝ) ^ (3/2:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have h4' : (v ^ ((3:ℝ)/2))⁻¹ ≤ ((1/2:ℝ) ^ (3/2:ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hpos _) h3').mpr h1'
      have h5' : ((1/2:ℝ) ^ (3/2:ℝ))⁻¹ = (2:ℝ) ^ (3/2:ℝ) := by
        rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2), inv_inv]
      have h6' : (2:ℝ) ^ (3/2:ℝ) ≤ 4 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (3:ℝ)/2 ≤ 2)
        rwa [show (2:ℝ)^(2:ℝ) = 4 by norm_num] at h
      calc v ^ (-(3:ℝ)/2) = (v ^ ((3:ℝ)/2))⁻¹ := h2'
        _ ≤ ((1/2:ℝ) ^ (3/2:ℝ))⁻¹ := h4'
        _ = (2:ℝ) ^ (3/2:ℝ) := h5'
        _ ≤ 4 := h6'
    rw [hf]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi)),
        abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
    have hXn : 0 ≤ v ^ (-(3:ℝ)/2) := Real.rpow_nonneg hv0.le _
    have hA' : 0 ≤ (100:ℝ) * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi := by positivity
    have step1 : 1 / (2 * Real.pi) * |F v| * v ^ (-(3:ℝ)/2)
        ≤ 1 / (2 * Real.pi) * (100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi) * 4 := by
      have h2π : (0:ℝ) ≤ 1/(2*Real.pi) := by positivity
      calc 1 / (2 * Real.pi) * |F v| * v ^ (-(3:ℝ)/2)
          = (1 / (2 * Real.pi)) * (|F v| * v ^ (-(3:ℝ)/2)) := by ring
        _ ≤ (1 / (2 * Real.pi)) * ((100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi) * 4) := by
            apply mul_le_mul_of_nonneg_left _ h2π
            exact mul_le_mul h1 hpowle hXn hA'
        _ = 1 / (2 * Real.pi) * (100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi) * 4 := by ring
    have step2 : 1 / (2 * Real.pi) * (100 * |v - 1| ^ (-(1:ℝ)/2) + 2*Real.pi) * 4
        = (200/Real.pi) * |v - 1| ^ (-(1:ℝ)/2) + 4 := by
      field_simp; ring
    have step3 : (200/Real.pi) * |v - 1| ^ (-(1:ℝ)/2) + 4
        ≤ 200 * (|v - 1| ^ (-(1:ℝ)/2) + 1) := by
      have hnn : 0 ≤ |v - 1| ^ (-(1:ℝ)/2) := Real.rpow_nonneg (abs_nonneg _) _
      have hpile : (200/Real.pi : ℝ) ≤ 200 := by
        rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
      nlinarith
    exact le_trans (le_trans step1 (le_of_eq step2)) step3
  have hC : IntegrableOn f (Ioi 2) := by
    have hbase : IntegrableOn (fun v : ℝ => v ^ (-(3:ℝ)/2)) (Ioi 2) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3:ℝ)/2) < -1) (by norm_num : (0:ℝ) < 2)
    have hdom : IntegrableOn (fun v : ℝ => 2 * v ^ (-(3:ℝ)/2)) (Ioi 2) := hbase.const_mul 2
    refine Integrable.mono' hdom hfmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [mem_Ioi] at hv
    have hv0 : 0 < v := by linarith
    have h1 : |F v| ≤ 4*Real.pi := by rw [hF]; exact abs_phiIntegral_le_large hv.le
    rw [hf]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi)),
        abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
    calc 1 / (2 * Real.pi) * |F v| * v ^ (-(3:ℝ)/2)
        ≤ 1 / (2 * Real.pi) * (4 * Real.pi) * v ^ (-(3:ℝ)/2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv0.le _)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * v ^ (-(3:ℝ)/2) := by field_simp; ring
  have hAB : IntegrableOn f (Ioc 0 (1/2) ∪ Icc (1/2) 2) := hA.union hB
  have hABC : IntegrableOn f ((Ioc 0 (1/2) ∪ Icc (1/2) 2) ∪ Ioi 2) := hAB.union hC
  have hset : (Ioc (0:ℝ) (1/2) ∪ Icc (1/2) 2) ∪ Ioi 2 = Ioi 0 := by
    ext x; simp only [mem_union, mem_Ioc, mem_Icc, mem_Ioi]
    constructor
    · rintro ((⟨h1,h2⟩ | ⟨h1,h2⟩) | h1) <;> linarith
    · intro h
      by_cases h' : x ≤ 1/2
      · exact Or.inl (Or.inl ⟨h, h'⟩)
      · simp only [not_le] at h'
        by_cases h'' : x ≤ 2
        · exact Or.inl (Or.inr ⟨h'.le, h''⟩)
        · simp only [not_le] at h''
          exact Or.inr h''
  rw [hset] at hABC
  exact hABC


end Commons.Analysis.Integral
