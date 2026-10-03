import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Fourier.poisson_step_d
import Submission.Commons.Analysis.Fourier.fourier_isBigO_rpow_neg_two
import Submission.Commons.Analysis.Fourier.fourier_ofReal_eq_two_mul_integral_Ici_cos
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow
import Submission.Commons.Analysis.InfiniteSum.tsum_int_eq_zero_of_odd

set_option maxHeartbeats 2000000
namespace Commons.Analysis.Fourier

open scoped FourierTransform
open MeasureTheory Filter Asymptotics

open scoped FourierTransform in
theorem poisson_cos_residue (f : ℝ → ℝ) (b : ℝ) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + b ^ 2))
    (d : ℕ) (hd : 0 < d) (α : ℝ) :
    ∑' m : ℤ, f ((α + m * (d : ℝ)) ^ 2 + b ^ 2)
      = (2 / (d : ℝ)) * ∑' k : ℤ,
          (∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + b ^ 2) * Real.cos (2 * Real.pi * (k : ℝ) * t / (d : ℝ)))
            * Real.cos (2 * Real.pi * α * (k : ℝ) / (d : ℝ)) := by
  set g : ℝ → ℝ := fun t => f (t ^ 2 + b ^ 2) with hg_def
  set dR : ℝ := (d : ℝ) with hdR_def
  have hdR_pos : 0 < dR := by rw [hdR_def]; exact_mod_cast hd
  -- work with `g` and `dR`
  change ∑' m : ℤ, g (α + m * dR)
      = (2 / dR) * ∑' k : ℤ,
          (∫ t in Set.Ici (0 : ℝ), g t * Real.cos (2 * Real.pi * (k : ℝ) * t / dR))
            * Real.cos (2 * Real.pi * α * (k : ℝ) / dR)
  have hg_cont : Continuous g := by
    rw [hg_def]
    exact hf.continuous.comp (by fun_prop)
  have hg_even : ∀ t, g (-t) = g t := by
    intro t; rw [hg_def]; simp only; congr 1; ring
  have hg_cs : HasCompactSupport g := by rw [hg_def]; exact hcs
  have hg_cd : ContDiff ℝ 2 g := by rw [hg_def]; exact hf.comp (by fun_prop)
  -- complexification of g
  have hF_cont : Continuous (fun t : ℝ => (g t : ℂ)) :=
    Complex.continuous_ofReal.comp hg_cont
  have hF_cs : HasCompactSupport (fun t : ℝ => (g t : ℂ)) :=
    hg_cs.comp_left Complex.ofReal_zero
  have hF_bigO : (fun t : ℝ => (g t : ℂ)) =O[Filter.cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2:ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    have hev : (fun t : ℝ => (g t : ℂ)) =ᶠ[Filter.cocompact ℝ] 0 := by
      rw [← Filter.coclosedCompact_eq_cocompact, ← hasCompactSupport_iff_eventuallyEq]
      exact hF_cs
    filter_upwards [hev] with x hx
    have hx' : (g x : ℂ) = 0 := hx
    rw [hx', norm_zero]
    positivity
  have hFf_bigO : (𝓕 (fun t : ℝ => (g t : ℂ))) =O[Filter.cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2:ℝ))) := by
    have hF_cd : ContDiff ℝ 2 (fun t : ℝ => (g t : ℂ)) := by
      have := Complex.ofRealCLM.contDiff.comp hg_cd
      simpa [Function.comp_def] using this
    exact fourier_isBigO_rpow_neg_two hF_cd hF_cs
  -- Poisson summation
  have hpois := poisson_step_d (fun t : ℝ => (g t : ℂ)) hF_cont one_lt_two hF_bigO hFf_bigO
    dR hdR_pos α
  -- abbreviations
  set Iv : ℤ → ℝ := fun k => ∫ t in Set.Ici (0:ℝ), g t * Real.cos (2 * Real.pi * (k:ℝ) * t / dR)
    with hIv_def
  set Ck : ℤ → ℝ := fun k => Real.cos (2 * Real.pi * α * (k:ℝ) / dR) with hCk_def
  set Sk : ℤ → ℝ := fun k => Real.sin (2 * Real.pi * α * (k:ℝ) / dR) with hSk_def
  -- the Fourier transform identity
  have hft : ∀ ξ : ℝ, (𝓕 (fun t : ℝ => (g t : ℂ))) ξ
      = ((2 * ∫ t in Set.Ici (0:ℝ), g t * Real.cos (2 * Real.pi * ξ * t)) : ℂ) :=
    fun ξ => fourier_ofReal_eq_two_mul_integral_Ici_cos g hg_cont hg_cs hg_even ξ
  have hInt : ∀ k : ℤ,
      (∫ t in Set.Ici (0:ℝ), g t * Real.cos (2 * Real.pi * ((k:ℝ)/dR) * t)) = Iv k := by
    intro k
    simp only [hIv_def]
    apply setIntegral_congr_ae measurableSet_Ici
    filter_upwards with t ht
    have harg : 2 * Real.pi * ((k:ℝ)/dR) * t = 2 * Real.pi * (k:ℝ) * t / dR := by ring
    rw [harg]
  have hftk : ∀ k : ℤ, (𝓕 (fun t : ℝ => (g t : ℂ))) ((k:ℝ)/dR) = ((2 * Iv k : ℝ) : ℂ) := by
    intro k
    rw [hft, hInt k]
    push_cast
    ring
  -- summability
  have hSumF : Summable (fun k : ℤ => (𝓕 (fun t : ℝ => (g t : ℂ))) ((k:ℝ)/dR)) :=
    summable_of_isBigO_cocompact_rpow one_lt_two hFf_bigO hdR_pos
  have hSum2Iv : Summable (fun k : ℤ => ((2 * Iv k : ℝ) : ℂ)) :=
    hSumF.congr (fun k => hftk k)
  have hSumIv : Summable (fun k : ℤ => Iv k) := by
    have h1 : Summable (fun k : ℤ => (2 * Iv k : ℝ)) := Complex.summable_ofReal.mp hSum2Iv
    exact (summable_mul_left_iff (show (2:ℝ) ≠ 0 by norm_num)).mp h1
  have hSumIvnorm : Summable (fun k : ℤ => ‖Iv k‖) := hSumIv.norm
  have hSum2Ivnorm : Summable (fun k : ℤ => 2 * ‖Iv k‖) := hSumIvnorm.mul_left 2
  -- evenness / oddness of the pieces
  have hEvenIv : ∀ n : ℤ, Iv (-n) = Iv n := by
    intro n
    simp only [hIv_def]
    apply setIntegral_congr_ae measurableSet_Ici
    filter_upwards with t ht
    have harg : 2 * Real.pi * ((-n:ℤ):ℝ) * t / dR = -(2 * Real.pi * (n:ℝ) * t / dR) := by
      push_cast; ring
    rw [harg, Real.cos_neg]
  have hOddSk : ∀ n : ℤ, Sk (-n) = -Sk n := by
    intro n
    simp only [hSk_def]
    have harg : 2 * Real.pi * α * ((-n:ℤ):ℝ) / dR = -(2 * Real.pi * α * (n:ℝ) / dR) := by
      push_cast; ring
    rw [harg, Real.sin_neg]
  have hSk_sum : Summable (fun k : ℤ => 2 * Iv k * Sk k) := by
    refine Summable.of_norm_bounded hSum2Ivnorm (fun k => ?_)
    simp only [Real.norm_eq_abs, hSk_def]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [Real.abs_sin_le_one (2 * Real.pi * α * (k:ℝ) / dR), abs_nonneg (Iv k)]
  have hA : Summable (fun k : ℤ => (((2 * Iv k * Ck k : ℝ)) : ℂ)) := by
    refine Summable.of_norm_bounded hSum2Ivnorm (fun k => ?_)
    rw [Complex.norm_real]
    simp only [Real.norm_eq_abs, hCk_def]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [Real.abs_cos_le_one (2 * Real.pi * α * (k:ℝ) / dR), abs_nonneg (Iv k)]
  have hB : Summable (fun k : ℤ => (((2 * Iv k * Sk k : ℝ)) : ℂ) * Complex.I) :=
    (Complex.summable_ofReal.mpr hSk_sum).mul_right Complex.I
  -- exponential in real form
  have hE : ∀ k : ℤ, Complex.exp (2 * Real.pi * Complex.I * α * (k:ℤ) / dR)
      = ((Ck k : ℂ) + (Sk k : ℂ) * Complex.I) := by
    intro k
    simp only [hCk_def, hSk_def]
    have hexp : (2 * Real.pi * Complex.I * α * (k:ℤ) / dR)
        = ((2 * Real.pi * α * (k:ℝ) / dR : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hexp, Complex.exp_ofReal_mul_I]
  have hBzero : ∑' k : ℤ, (((2 * Iv k * Sk k : ℝ)) : ℂ) * Complex.I = 0 := by
    rw [tsum_mul_right, ← Complex.ofReal_tsum]
    rw [Commons.Analysis.InfiniteSum.tsum_int_eq_zero_of_odd (q := fun k : ℤ => 2 * Iv k * Sk k) ?_ hSk_sum]
    simp
    intro n
    rw [hEvenIv n, hOddSk n]
    ring
  have hCcsum : ∑' k : ℤ, (((2 * Iv k * Ck k : ℝ)) : ℂ)
      = ((2 * ∑' k : ℤ, Iv k * Ck k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
    congr 1
    rw [show (∑' k : ℤ, 2 * Iv k * Ck k) = ∑' k : ℤ, 2 * (Iv k * Ck k) from
      tsum_congr (fun k => by ring), tsum_mul_left]
  have hstep1 : ∑' k : ℤ, (𝓕 (fun t : ℝ => (g t : ℂ))) ((k:ℝ)/dR)
        * Complex.exp (2 * Real.pi * Complex.I * α * (k:ℤ) / dR)
      = ∑' k : ℤ, (((2 * Iv k : ℝ)) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * α * (k:ℤ) / dR) :=
    tsum_congr (fun k => by rw [hftk k])
  have hstep2 : ∑' k : ℤ, (((2 * Iv k : ℝ)) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * α * (k:ℤ) / dR)
      = ∑' k : ℤ, (((2 * Iv k : ℝ)) : ℂ) * ((Ck k : ℂ) + (Sk k : ℂ) * Complex.I) :=
    tsum_congr (fun k => by rw [hE k])
  have hstep3 : ∑' k : ℤ, (((2 * Iv k : ℝ)) : ℂ) * ((Ck k : ℂ) + (Sk k : ℂ) * Complex.I)
      = ∑' k : ℤ, ((((2 * Iv k * Ck k : ℝ)) : ℂ)
          + (((2 * Iv k * Sk k : ℝ)) : ℂ) * Complex.I) := by
    apply tsum_congr; intro k; push_cast; ring
  have hstep4 : ∑' k : ℤ, ((((2 * Iv k * Ck k : ℝ)) : ℂ)
          + (((2 * Iv k * Sk k : ℝ)) : ℂ) * Complex.I)
      = (∑' k : ℤ, (((2 * Iv k * Ck k : ℝ)) : ℂ))
          + ∑' k : ℤ, (((2 * Iv k * Sk k : ℝ)) : ℂ) * Complex.I :=
    Summable.tsum_add hA hB
  have key : ∑' k : ℤ, (𝓕 (fun t : ℝ => (g t : ℂ))) ((k:ℝ)/dR)
        * Complex.exp (2 * Real.pi * Complex.I * α * (k:ℤ) / dR)
      = 2 * ∑' k : ℤ, (((Iv k * Ck k : ℝ)) : ℂ) := by
    rw [hstep1, hstep2, hstep3, hstep4, hBzero, add_zero, hCcsum,
      Complex.ofReal_mul, Complex.ofReal_tsum]
    rw [show ((2:ℝ) : ℂ) = 2 by norm_num, mul_comm]
  -- final assembly
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_tsum]
  rw [hpois, key, ← mul_assoc]
  congr 1
  push_cast
  ring

end Commons.Analysis.Fourier