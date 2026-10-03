import Mathlib.Analysis.Fourier.PoissonSummation
import Submission.Commons.Analysis.Fourier.fourier_scaled_translate

namespace Commons.Analysis.Fourier

open scoped FourierTransform
open MeasureTheory

/-- Fourier transform of a dilation by a positive factor on `ℝ`. -/
lemma fourier_comp_mul_of_pos (F : ℝ → ℂ) {d : ℝ} (hd : 0 < d) (ξ : ℝ) :
    𝓕 (fun x => F (d * x)) ξ = ((1 / d : ℝ) : ℂ) * 𝓕 F (ξ / d) := by
  have h := fourier_comp_inv_smul (V := ℝ) F (a := d⁻¹) (inv_pos.mpr hd) ξ
  rw [Module.finrank_self, pow_one, inv_inv] at h
  simp only [smul_eq_mul, Complex.real_smul] at h
  rw [h, one_div, div_eq_mul_inv, mul_comm d⁻¹ ξ]

open scoped FourierTransform in
theorem poisson_step_d (F : ℝ → ℂ) (hc : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : Asymptotics.IsBigO (Filter.cocompact ℝ) F (fun x : ℝ => |x| ^ (-b)))
    (hF' : Asymptotics.IsBigO (Filter.cocompact ℝ) (𝓕 F) (fun x : ℝ => |x| ^ (-b)))
    (d : ℝ) (hd : 0 < d) (a : ℝ) :
    ∑' m : ℤ, F (a + m * d)
      = (1 / d) * ∑' k : ℤ, (𝓕 F) (k / d) * Complex.exp (2 * Real.pi * Complex.I * a * k / d) := by
  have hdne : d ≠ 0 := hd.ne'
  have hgcont : Continuous (fun x : ℝ => F (d * x)) :=
    hc.comp (continuous_const.mul continuous_id)
  -- Big-O hypothesis for the dilated function.
  have hgBigO : (fun x : ℝ => F (d * x)) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) := by
    have hcomp : (fun x : ℝ => F (d * x)) =O[Filter.cocompact ℝ]
        (fun x : ℝ => |d * x| ^ (-b)) :=
      hF.comp_tendsto (Filter.tendsto_cocompact_mul_left₀ (K := ℝ) (a := d) hdne)
    refine hcomp.trans ?_
    refine Asymptotics.IsBigO.of_bound (d ^ (-b)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_mul, abs_of_pos hd,
      Real.mul_rpow hd.le (abs_nonneg x)]
  -- Big-O hypothesis for the Fourier transform of the dilated function.
  have hgBigO' : (𝓕 (fun x : ℝ => F (d * x))) =O[Filter.cocompact ℝ]
      (fun x : ℝ => |x| ^ (-b)) := by
    have hfun : (𝓕 (fun x : ℝ => F (d * x))) = fun ξ : ℝ => ((1 / d : ℝ) : ℂ) * 𝓕 F (ξ / d) := by
      funext ξ; exact fourier_comp_mul_of_pos F hd ξ
    rw [hfun]
    have hbase : (fun ξ : ℝ => 𝓕 F (ξ / d)) =O[Filter.cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-b)) := by
      have hcomp : (fun ξ : ℝ => 𝓕 F (ξ / d)) =O[Filter.cocompact ℝ]
          (fun ξ : ℝ => |ξ * d⁻¹| ^ (-b)) :=
        hF'.comp_tendsto (Filter.tendsto_cocompact_mul_right₀ (K := ℝ) (a := d⁻¹) (inv_ne_zero hdne))
      refine hcomp.trans ?_
      refine Asymptotics.IsBigO.of_bound (d ^ b) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hd),
        Real.mul_rpow (abs_nonneg x) (inv_nonneg.mpr hd.le),
        Real.inv_rpow hd.le, Real.rpow_neg hd.le, inv_inv]
      exact le_of_eq (mul_comm _ _)
    exact hbase.const_mul_left _
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hgcont hb hgBigO hgBigO' (a / d)
  -- Identification of the left-hand side.
  have hA : ∑' m : ℤ, F (a + m * d) = ∑' n : ℤ, (fun x : ℝ => F (d * x)) (a / d + (n : ℝ)) := by
    apply tsum_congr
    intro n
    show F (a + (n : ℝ) * d) = F (d * (a / d + (n : ℝ)))
    congr 1
    field_simp
  -- Identification of the right-hand side.
  have hexp : ∀ n : ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((a / d : ℝ) : ℂ) / ((1 : ℝ) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (n : ℂ) / (d : ℂ)) := by
    intro n
    congr 1
    push_cast
    ring
  have hC : ∑' n : ℤ, 𝓕 (fun x : ℝ => F (d * x)) (n : ℝ) * fourier n ((a / d : ℝ) : UnitAddCircle)
      = ((1 / d : ℝ) : ℂ) * ∑' k : ℤ,
          𝓕 F ((k : ℝ) / d) * Complex.exp (2 * Real.pi * Complex.I * a * (k : ℤ) / d) := by
    have hterm : ∀ n : ℤ,
        𝓕 (fun x : ℝ => F (d * x)) (n : ℝ) * fourier n ((a / d : ℝ) : UnitAddCircle)
        = ((1 / d : ℝ) : ℂ) * (𝓕 F ((n : ℝ) / d)
            * Complex.exp (2 * Real.pi * Complex.I * a * (n : ℤ) / d)) := by
      intro n
      rw [fourier_comp_mul_of_pos F hd, fourier_coe_apply, hexp n]
      ring
    calc ∑' n : ℤ, 𝓕 (fun x : ℝ => F (d * x)) (n : ℝ) * fourier n ((a / d : ℝ) : UnitAddCircle)
        = ∑' n : ℤ, ((1 / d : ℝ) : ℂ) * (𝓕 F ((n : ℝ) / d)
            * Complex.exp (2 * Real.pi * Complex.I * a * (n : ℤ) / d)) := tsum_congr hterm
      _ = ((1 / d : ℝ) : ℂ) * ∑' n : ℤ, (𝓕 F ((n : ℝ) / d)
            * Complex.exp (2 * Real.pi * Complex.I * a * (n : ℤ) / d)) := tsum_mul_left
  have hcoef : ((1 / d : ℝ) : ℂ) = (1 / d : ℂ) := by
    rw [one_div, one_div, Complex.ofReal_inv]
  rw [hA, hP, hC, hcoef]

end Commons.Analysis.Fourier