import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.Calculus.exists_holder_parametrisation

open MeasureTheory Set Real

namespace Commons.Analysis.Integral

set_option autoImplicit false

/-- `(√x)⁻¹ = x ^ (-1/2)` for `x ≥ 0`. -/
lemma inv_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx]

/-- `|sin t| = |sin (t - m·π)|` for `m : ℤ`. -/
lemma abs_sin_eq_abs_sin_sub_int_mul_pi (t : ℝ) (m : ℤ) :
    |Real.sin t| = |Real.sin (t - (m : ℝ) * Real.pi)| := by
  have h : Real.sin t = (-1 : ℝ) ^ m * Real.sin (t - (m : ℝ) * Real.pi) := by
    have h' := Real.sin_add_int_mul_pi (t - (m : ℝ) * Real.pi) m
    rwa [sub_add_cancel] at h'
  rw [h, abs_mul, abs_zpow]
  norm_num

/-- `(2/π)^(-1/2) = √(π/2)`. -/
lemma rpow_two_div_pi_neg_half : ((2 : ℝ) / Real.pi) ^ (-(1 / 2 : ℝ)) = Real.sqrt (π / 2) := by
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 / π), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
  congr 1
  field_simp

/-- Pointwise bound: for `t ∈ [-π, 3π]`, `1/√|sin t|` is controlled by the
sum of `|t - m π|^(-1/2)` over `m ∈ {-1,0,1,2,3}`. -/
lemma inv_sqrt_abs_sin_le_sum {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) (3 * Real.pi)) :
    (Real.sqrt |Real.sin t|)⁻¹
      ≤ Real.sqrt (Real.pi / 2)
        * ∑ m ∈ Finset.Icc (-1 : ℤ) 3, |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)) := by
  set m : ℤ := round (t / Real.pi) with hm
  have hround : |t / Real.pi - (m : ℝ)| ≤ 1 / 2 := by
    rw [hm]; exact abs_sub_round (t / Real.pi)
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have htc : t - (m : ℝ) * Real.pi = Real.pi * (t / Real.pi - (m : ℝ)) := by
    rw [mul_sub, mul_div_cancel₀ t hpi]; ring
  have htri : |t - (m : ℝ) * Real.pi| ≤ Real.pi / 2 := by
    rw [htc, abs_mul, abs_of_pos Real.pi_pos]
    have h2 : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
    have := mul_le_mul_of_nonneg_left hround Real.pi_pos.le
    linarith
  have hsinb : (2 / Real.pi) * |t - (m : ℝ) * Real.pi| ≤ |Real.sin t| := by
    rw [abs_sin_eq_abs_sin_sub_int_mul_pi t m]
    exact mul_abs_le_abs_sin htri
  have hm_mem : m ∈ Finset.Icc (-1 : ℤ) 3 := by
    rw [Finset.mem_Icc]
    have hu : t - (m : ℝ) * Real.pi ≤ Real.pi / 2 := (abs_le.mp htri).2
    have hl : -(Real.pi / 2) ≤ t - (m : ℝ) * Real.pi := (abs_le.mp htri).1
    constructor
    · by_contra h
      push Not at h
      have hm2 : m ≤ -2 := by omega
      have hm2' : (m : ℝ) ≤ -2 := by exact_mod_cast hm2
      have htup : t ≤ (m : ℝ) * Real.pi + Real.pi / 2 := by linarith
      nlinarith [ht.1, Real.pi_pos]
    · by_contra h
      push Not at h
      have hm4 : 4 ≤ m := by omega
      have hm4' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
      have htlo : (m : ℝ) * Real.pi - Real.pi / 2 ≤ t := by linarith
      nlinarith [ht.2, Real.pi_pos]
  have hterm : |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ))
      ≤ ∑ m ∈ Finset.Icc (-1 : ℤ) 3, |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)) :=
    Finset.single_le_sum (f := fun i : ℤ => |t - (i : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)))
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hm_mem
  rcases eq_or_lt_of_le (abs_nonneg (t - (m : ℝ) * Real.pi)) with hzero | hpos
  · have hsin0 : Real.sin t = 0 := by
      have ht' : t = (m : ℝ) * Real.pi := by
        have := abs_eq_zero.mp hzero.symm; linarith
      rw [ht', Real.sin_int_mul_pi]
    rw [hsin0, abs_zero, Real.sqrt_zero, inv_zero]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))
  · rw [inv_sqrt_eq_rpow_neg_half (abs_nonneg _)]
    have hxm : 0 < (2 / Real.pi) * |t - (m : ℝ) * Real.pi| :=
      mul_pos (by positivity) hpos
    have step1 : |Real.sin t| ^ (-(1 / 2 : ℝ))
        ≤ ((2 / Real.pi) * |t - (m : ℝ) * Real.pi|) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hxm hsinb (by norm_num)
    have step2 : ((2 / Real.pi) * |t - (m : ℝ) * Real.pi|) ^ (-(1 / 2 : ℝ))
        = Real.sqrt (Real.pi / 2) * |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2 / Real.pi) (abs_nonneg _),
        rpow_two_div_pi_neg_half]
    calc |Real.sin t| ^ (-(1 / 2 : ℝ))
        ≤ ((2 / Real.pi) * |t - (m : ℝ) * Real.pi|) ^ (-(1 / 2 : ℝ)) := step1
      _ = Real.sqrt (Real.pi / 2) * |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)) := step2
      _ ≤ Real.sqrt (Real.pi / 2)
            * ∑ m ∈ Finset.Icc (-1 : ℤ) 3, |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hterm (Real.sqrt_nonneg _)

/-- The function `t ↦ (√|sin t|)⁻¹` is integrable on any interval of the form
`(-φ, 2π - φ]` with `φ ∈ (-π, π]`. -/
lemma integrableOn_inv_sqrt_abs_sin_Ioc {φ : ℝ} (hφ : φ ∈ Set.Ioc (-Real.pi) Real.pi) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sqrt |Real.sin t|)⁻¹)
      (Set.uIoc (-φ) (2 * Real.pi - φ)) := by
  have hmeas : Measurable (fun t : ℝ => (Real.sqrt |Real.sin t|)⁻¹) :=
    ((Real.continuous_sqrt.measurable).comp (measurable_abs.comp Real.measurable_sin)).inv
  have hsum : ∀ m ∈ Finset.Icc (-1 : ℤ) 3,
      IntervalIntegrable (fun t : ℝ => |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)))
        volume (-φ) (2 * Real.pi - φ) :=
    fun m _ => Commons.Analysis.Calculus.intervalIntegrable_abs_sub_rpow
      (c := (m : ℝ) * Real.pi) (r := -(1 / 2 : ℝ)) (by norm_num) _ _
  have hD0 : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ Finset.Icc (-1 : ℤ) 3, |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)))
      volume (-φ) (2 * Real.pi - φ) :=
    (IntervalIntegrable.sum (Finset.Icc (-1 : ℤ) 3)
      (f := fun m t => |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ))) hsum).congr
      (fun t _ => by rw [Finset.sum_apply])
  have hD : MeasureTheory.IntegrableOn
      (fun t : ℝ => ∑ m ∈ Finset.Icc (-1 : ℤ) 3, |t - (m : ℝ) * Real.pi| ^ (-(1 / 2 : ℝ)))
      (Set.uIoc (-φ) (2 * Real.pi - φ)) := by
    rw [← intervalIntegrable_iff]; exact hD0
  refine Integrable.mono' (hD.const_mul (Real.sqrt (Real.pi / 2))) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have htI : t ∈ Set.Icc (-Real.pi) (3 * Real.pi) := by
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -φ ≤ 2 * Real.pi - φ)] at ht
    exact ⟨by linarith [ht.1, hφ.2], by linarith [ht.2, hφ.1]⟩
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_sqrt_abs_sin_le_sum htI

theorem integrableOn_inv_sqrt_abs_trig {p q z : ℝ} (hz : 0 < z) (hpq : p^2 + q^2 = z^2) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sqrt |p * Real.sin θ - q * Real.cos θ|)⁻¹)
      (Set.uIoc 0 (2 * Real.pi)) := by
  set w : ℂ := ⟨p, q⟩ with hwdef
  have hwnorm : ‖w‖ = z := by
    have h1 : ‖w‖ ^ 2 = p ^ 2 + q ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre : w.re = p := rfl
      have him : w.im = q := rfl
      rw [hre, him]; ring
    rw [hpq] at h1
    nlinarith [norm_nonneg w, hz]
  set φ : ℝ := w.arg with hφdef
  have hφmem : φ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hφdef]; exact Complex.arg_mem_Ioc w
  have hcos : z * Real.cos φ = p := by
    rw [← hwnorm, hφdef]; exact Complex.norm_mul_cos_arg w
  have hsin : z * Real.sin φ = q := by
    rw [← hwnorm, hφdef]; exact Complex.norm_mul_sin_arg w
  have hpt : ∀ θ : ℝ, p * Real.sin θ - q * Real.cos θ = z * Real.sin (θ - φ) := by
    intro θ
    rw [← hcos, ← hsin, Real.sin_sub]; ring
  have hfun : (fun θ : ℝ => (Real.sqrt |p * Real.sin θ - q * Real.cos θ|)⁻¹)
      = fun θ : ℝ => (Real.sqrt z)⁻¹ * (Real.sqrt |Real.sin (θ - φ)|)⁻¹ := by
    funext θ
    rw [hpt θ, abs_mul, abs_of_pos hz, Real.sqrt_mul hz.le, mul_inv]
  rw [← intervalIntegrable_iff, hfun]
  have hbase : IntervalIntegrable (fun t : ℝ => (Real.sqrt |Real.sin t|)⁻¹)
      volume (-φ) (2 * Real.pi - φ) := by
    rw [intervalIntegrable_iff]
    exact integrableOn_inv_sqrt_abs_sin_Ioc hφmem
  have hshift : IntervalIntegrable (fun θ : ℝ => (Real.sqrt |Real.sin (θ - φ)|)⁻¹)
      volume 0 (2 * Real.pi) := by
    have h := (IntervalIntegrable.comp_sub_right_iff
      (f := fun t : ℝ => (Real.sqrt |Real.sin t|)⁻¹)
      (a := -φ) (b := 2 * Real.pi - φ) (c := φ)).mpr hbase
    simpa using h
  exact hshift.const_mul (Real.sqrt z)⁻¹


end Commons.Analysis.Integral