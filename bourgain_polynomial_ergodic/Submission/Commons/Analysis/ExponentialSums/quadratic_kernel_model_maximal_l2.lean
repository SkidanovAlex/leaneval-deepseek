import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_major_arc_model
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_dyadic_of_model
import Submission.Commons.Analysis.ExponentialSums.quadratic_gauss_sum_bound
import Submission.Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial
import Submission.Commons.Analysis.Oscillatory.van_der_corput_bound
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.ExponentialSums.tsum_min_inv_sq_le
import Submission.Commons.Analysis.Fourier.l2_multiplier_sum_square_function
import Submission.Commons.Analysis.Fourier.multiplier_square_function_l2
import Submission.Commons.Analysis.Fresnel.fresnel_integral_decay
import Submission.Commons.Analysis.Fresnel.fresnel_replace_sharp_tsum_le
import Submission.Commons.Analysis.Fresnel.fresnel_integral_one_sub_le
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.memLp_convolution_one_two
import Submission.Commons.Analysis.Fourier.max_finset_exponential_sum_l2
import Submission.Commons.Analysis.Fourier.separated_exponentials_near_orthogonal
import Submission.Commons.Analysis.Fourier.exists_dyadic_chain_decomposition
import Submission.Commons.Analysis.Fourier.lintegral_sq_sum_le_of_class_bounds
import Submission.Commons.Analysis.Fourier.lintegral_iSup_band_sum_dilation_le
import Submission.Commons.Analysis.Fourier.bandSum_windowed
import Submission.Commons.Analysis.Fourier.convolution_kernel_fubini
import Submission.Commons.Analysis.Fourier.periodic_neighborhood_of_real_line_bandpass
import Submission.Commons.Analysis.Fourier.separated_maximal_of_smooth_window
import Submission.Commons.Analysis.Fourier.neighborhood_maximal_arbitrary_of_separated
import Submission.Commons.Analysis.Fourier.bandOp_l2_multiplier_bound
import Submission.Commons.Analysis.Fourier.aestronglyMeasurable_conv
import Submission.Commons.Analysis.Fourier.sharp_of_smooth_window_maximal_l2
import Submission.Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed
import Submission.Commons.Analysis.Fourier.card_filter_le_two
import Submission.Commons.Analysis.Fourier.chain_exp_sum_le_entropy
import Submission.Commons.Analysis.Fourier.dilation_variation_l2_sup
import Submission.Commons.Analysis.Fourier.dilation_variation_scalar_l2
import Submission.Commons.Analysis.Fourier.entropy_integral_le_of_sup_bound
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
import Submission.Commons.Analysis.Fourier.lintegral_translate_sub_sq_le_of_fourier_support
import Submission.Commons.Analysis.Fourier.maximal_dilation_convolution_l2
import Submission.Commons.Analysis.Fourier.sum_sq_le_two_of_separated
import Submission.Commons.Analysis.Metric.coveringNumber_le_of_variation
import Submission.Commons.Analysis.Real.ofReal_sum_dyadic_le_lintegral_entropy_Ioc
import Submission.Commons.MeasureTheory.Integral.lintegral_Ioi_rpow_eq


namespace Commons.Analysis.ExponentialSums

open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology FourierTransform Convolution
open Commons.Analysis.Fourier

set_option maxHeartbeats 2000000







/-- **Inverse Fourier transform of an `L¹ ∩ L²` function, a.e.** -/
private theorem kq_fourierInv_fourier_ae_eq {h : ℝ → ℂ}
    (h1 : MemLp h 1 (volume : Measure ℝ)) (h2 : MemLp h 2 (volume : Measure ℝ))
    (hF1 : MemLp (fun ξ => 𝓕 h ξ) 1 (volume : Measure ℝ))
    (hF2 : MemLp (fun ξ => 𝓕 h ξ) 2 (volume : Measure ℝ)) :
    (fun x => 𝓕⁻ (𝓕 h) x) =ᵐ[volume] h := by
  have hfwd : ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun ξ => 𝓕 h ξ :=
    fourier_toLp_ae_eq_fourier_of_memLp h1 h2
  have hLp : (𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) = hF2.toLp (fun ξ => 𝓕 h ξ) := by
    rw [Lp.ext_iff]
    exact hfwd.trans (MemLp.coeFn_toLp hF2).symm
  have hinv := fourierInv_toLp_ae_eq_fourierInv (h := fun ξ => 𝓕 h ξ) hF1 hF2
  have hchain : ((𝓕⁻ (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun x => 𝓕⁻ (𝓕 h) x) := by
    have hEq : (𝓕⁻ (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ))
        = 𝓕⁻ (hF2.toLp (fun ξ => 𝓕 h ξ)) := by rw [hLp]
    rw [hEq]
    exact hinv
  have hco : ((𝓕⁻ (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (h2.toLp h : ℝ → ℂ) := by
    rw [FourierPair.fourierInv_fourier_eq]
  exact hchain.symm.trans (hco.trans (MemLp.coeFn_toLp h2))

/-- `𝓕` of an `L¹ ∩ L²` function is `L²`. -/
private theorem kq_memLp_fourier_two {h : ℝ → ℂ} (h1 : MemLp h 1 (volume : Measure ℝ))
    (h2 : MemLp h 2 (volume : Measure ℝ)) :
    MemLp (fun ξ => 𝓕 h ξ) 2 (volume : Measure ℝ) := by
  have hcoe : ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 h ξ := fourier_toLp_ae_eq_fourier_of_memLp h1 h2
  exact (Lp.memLp (𝓕 (h2.toLp h))).ae_eq hcoe

/-- **Plancherel for the convolution**, `L¹ ∩ L²` case. -/
theorem kq_lintegral_convolution_sq_eq_of_memLp_one (g k : ℝ → ℂ)
    (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hk1 : MemLp k 1 (volume : Measure ℝ)) (hk2 : MemLp k 2 (volume : Measure ℝ)) :
    ∫⁻ x, ENNReal.ofReal ‖∫ y : ℝ, g y * k (x - y)‖ ^ (2:ℝ)
      = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ * ‖𝓕 k ξ‖) ^ (2:ℝ) := by
  set h : ℝ → ℂ := fun x => ∫ y : ℝ, g y * k (x - y) with hh
  have hgI : Integrable g := memLp_one_iff_integrable.mp hg1
  have hkI : Integrable k := memLp_one_iff_integrable.mp hk1
  have hI : Integrable h := by
    have hconv : h = (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) := by
      funext x; rw [hh, MeasureTheory.convolution_mul]
    rw [hconv]
    exact Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgI hkI
  have h1 : MemLp h 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hI
  have h2 : MemLp h 2 (volume : Measure ℝ) := (memLp_convolution_one_two hg1 hk2).1
  have hF : ∀ ξ : ℝ, 𝓕 h ξ = 𝓕 g ξ * 𝓕 k ξ := by
    intro ξ
    have hconv : h = (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) := by
      funext x; rw [hh, MeasureTheory.convolution_mul]
    rw [hconv]
    exact Real.fourier_mul_convolution_eq hgI hkI ξ
  have hFg2 : MemLp (fun ξ => 𝓕 g ξ) 2 (volume : Measure ℝ) := kq_memLp_fourier_two hg1 hg2
  have hFk2 : MemLp (fun ξ => 𝓕 k ξ) 2 (volume : Measure ℝ) := kq_memLp_fourier_two hk1 hk2
  have hprod1 : MemLp (fun ξ => 𝓕 g ξ * 𝓕 k ξ) 1 (volume : Measure ℝ) := by
    have := hFg2.mul (r := 1) hFk2
    refine this.ae_eq (Filter.Eventually.of_forall (fun ξ => ?_))
    simp [mul_comm]
  have hF2 : MemLp (fun ξ => 𝓕 h ξ) 2 (volume : Measure ℝ) := kq_memLp_fourier_two h1 h2
  have hF1 : MemLp (fun ξ => 𝓕 h ξ) 1 (volume : Measure ℝ) :=
    hprod1.ae_eq (Filter.Eventually.of_forall (fun ξ => (hF ξ).symm))
  have hinv : h =ᵐ[volume] fun x => 𝓕⁻ (𝓕 h) x :=
    (kq_fourierInv_fourier_ae_eq h1 h2 hF1 hF2).symm
  calc ∫⁻ x, ENNReal.ofReal ‖h x‖ ^ (2:ℝ)
      = ∫⁻ x, ENNReal.ofReal ‖𝓕⁻ (𝓕 h) x‖ ^ (2:ℝ) := by
        apply lintegral_congr_ae
        filter_upwards [hinv] with x hx
        rw [hx]
    _ = ∫⁻ ξ, ENNReal.ofReal ‖𝓕 h ξ‖ ^ (2:ℝ) :=
        Commons.Analysis.Fourier.lintegral_fourierInv_eq hF1 hF2
    _ = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ * ‖𝓕 k ξ‖) ^ (2:ℝ) := by
        apply lintegral_congr
        intro ξ
        rw [hF ξ, norm_mul]



/-! ### Auxiliary lemmas proved while working on this file

The two blocks below were proved, sorry-free, in this session and live (with their proofs) in
`Submission/Work/Analysis/Fourier/fourier_le_abs_mul_of_integral_zero.lean` and
`Submission/Work/Analysis/ExponentialSums/tsum_int_min_pow_sq_le.lean`; they are independent
contributions to the project's (reduction of the) wall — the *dyadic square function of the dilates
of a mean-zero kernel* (Bourgain 1989, (3.14)) — and are stored here as well so that they are
published together with this file.  They are NOT used by the target below. -/

open scoped RealInnerProductSpace in


private lemma kq_fourierChar_norm_sub_one_le (x : ℝ) :
    ‖(Real.fourierChar x : ℂ) - 1‖ ≤ 2 * Real.pi * |x| := by
  rw [Real.fourierChar_apply]
  have harg : (↑(2 * Real.pi * x) : ℂ) * Complex.I
      = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by ring
  rw [harg]
  have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * x)
  refine le_trans h2 ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos Real.pi_pos]

private lemma kq_fourier_eq_int (K : ℝ → ℂ) (u : ℝ) :
    𝓕 K u = ∫ v : ℝ, ((Real.fourierChar (-(v * u)) : ℂ)) * K v := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def]
  congr 1
  simp [mul_comm]

theorem kq_fourier_le_abs_mul_of_integral_zero (K : ℝ → ℂ)
    (hK : Integrable K (volume : Measure ℝ))
    (hxK : Integrable (fun x : ℝ => x • K x) (volume : Measure ℝ))
    (h0 : ∫ x : ℝ, K x = 0) (u : ℝ) :
    ‖𝓕 K u‖ ≤ 2 * Real.pi * |u| * ∫ x : ℝ, ‖x • K x‖ := by
  have hφK : Integrable (fun v : ℝ => ((Real.fourierChar (-(v * u)) : ℂ)) * K v) := by
    have h := (Real.fourierIntegral_convergent_iff (μ := volume) (f := K) u).2 hK
    refine h.congr ?_
    filter_upwards with v
    rw [Circle.smul_def]
    congr 1
    simp [mul_comm]
  have hmain : 𝓕 K u = ∫ v : ℝ, (((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v := by
    rw [kq_fourier_eq_int K u]
    have hsub : ∫ v : ℝ, (((Real.fourierChar (-(v * u)) : ℂ)) * K v - K v)
        = (∫ v : ℝ, ((Real.fourierChar (-(v * u)) : ℂ)) * K v) - ∫ v : ℝ, K v :=
      MeasureTheory.integral_sub hφK hK
    have heq : (∫ v : ℝ, ((Real.fourierChar (-(v * u)) : ℂ)) * K v)
        = ∫ v : ℝ, (((Real.fourierChar (-(v * u)) : ℂ)) * K v - K v) := by
      rw [hsub, h0, sub_zero]
    rw [heq]
    apply integral_congr_ae
    filter_upwards with v
    ring
  rw [hmain]
  have hbd : ∀ v : ℝ, ‖(((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v‖
      ≤ (2 * Real.pi * |u|) * ‖v • K v‖ := by
    intro v
    have h1 := kq_fourierChar_norm_sub_one_le (-(v * u))
    have h2 : 2 * Real.pi * |(-(v * u))| = (2 * Real.pi * |u|) * ‖v‖ := by
      rw [abs_neg, abs_mul, Real.norm_eq_abs]
      ring
    calc ‖(((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v‖
        = ‖((Real.fourierChar (-(v * u)) : ℂ)) - 1‖ * ‖K v‖ := norm_mul _ _
      _ ≤ (2 * Real.pi * |(-(v * u))|) * ‖K v‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (2 * Real.pi * |u|) * (‖v‖ * ‖K v‖) := by rw [h2]; ring
      _ = (2 * Real.pi * |u|) * ‖v • K v‖ := by rw [norm_smul]
  have hint1 : Integrable (fun v : ℝ => ‖(((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v‖) := by
    refine ((hφK.sub hK).norm).congr ?_
    filter_upwards with v
    simp only [Pi.sub_apply]
    have hring : ((Real.fourierChar (-(v * u)) : ℂ)) * K v - K v
        = (((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v := by ring
    rw [hring]
  have hint2 : Integrable (fun v : ℝ => (2 * Real.pi * |u|) * ‖v • K v‖) :=
    hxK.norm.const_mul _
  calc ‖∫ v : ℝ, (((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v‖
      ≤ ∫ v : ℝ, ‖(((Real.fourierChar (-(v * u)) : ℂ)) - 1) * K v‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, (2 * Real.pi * |u|) * ‖v • K v‖ := integral_mono hint1 hint2 hbd
    _ = 2 * Real.pi * |u| * ∫ v : ℝ, ‖v • K v‖ := by
        rw [MeasureTheory.integral_const_mul]





private lemma kq_rpow_neg_sq {x N : ℝ} (hx : 0 < x) : (x ^ (-N)) ^ 2 = x ^ (-2 * N) := by
  have h1 : (x ^ (-N)) ^ (2:ℕ) = x ^ ((-N) * (2:ℕ)) := by
    rw [← Real.rpow_natCast (x ^ (-N)) 2, ← Real.rpow_mul hx.le]
  rw [h1]
  congr 1
  ring

-- zpow bookkeeping helpers
private lemma kq_two_zpow_inv (l : ℤ) : ((2:ℝ)^l)⁻¹ = (2:ℝ)^(-l) :=
  (zpow_neg (2:ℝ) l).symm

private lemma kq_two_zpow_succ_nat (n : ℕ) : (2:ℝ)^((n:ℤ)+1) = (2:ℝ)^(n+1) := by
  rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0), zpow_natCast, pow_succ]

private lemma kq_two_zpow_neg_nat (n : ℕ) : (2:ℝ)^(-((n:ℤ)+1)) = ((2:ℝ)^(n+1))⁻¹ := by
  rw [zpow_neg, kq_two_zpow_succ_nat]

/-- Scaled core estimate: for `1 ≤ a ≤ 2` and `N > 0`,
`∑_l min(x_l, x_l^(-N))² ≤ 1 + 4/3 + 1/(1 - 2^(-2N))` where `x_l = a·2^{-l}`. -/
private lemma kq_scaled_bound (N : ℝ) (hN : 0 < N) {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    (∑' l : ℤ, (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2)
      ≤ 1 + (4/3 : ℝ) + (1 - (2:ℝ) ^ (-2 * N))⁻¹ := by
  have hzz : ∀ l : ℤ, (2:ℝ)^(-l) = ((2:ℝ)^l)⁻¹ := fun l => zpow_neg (2:ℝ) l
  simp only [hzz]
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
  set F : ℤ → ℝ := fun l => (min (a * ((2:ℝ)^l)⁻¹) ((a * ((2:ℝ)^l)⁻¹) ^ (-N))) ^ 2 with hFdef
  have hFnn : ∀ l : ℤ, 0 ≤ F l := fun l => sq_nonneg _
  -- upper bound on the positive half-line
  have hpos : ∀ n : ℕ, F ((n:ℤ)+1) ≤ a^2 * ((4:ℝ)^(n+1))⁻¹ := by
    intro n
    have hx : 0 < a * ((2:ℝ)^((n:ℤ)+1))⁻¹ :=
      mul_pos ha0 (inv_pos.mpr (zpow_pos (by norm_num) _))
    have h1 : F ((n:ℤ)+1) ≤ (a * ((2:ℝ)^((n:ℤ)+1))⁻¹)^2 :=
      pow_le_pow_left₀ (le_min hx.le (Real.rpow_nonneg hx.le _)) (min_le_left _ _) 2
    refine le_trans h1 ?_
    rw [kq_two_zpow_succ_nat]
    rw [mul_pow, inv_pow]
    have h3 : ((2:ℝ)^(n+1))^2 = (4:ℝ)^(n+1) := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h3]
  -- upper bound on the negative half-line
  have hneg : ∀ n : ℕ, F (-((n:ℤ)+1)) ≤ ((2:ℝ) ^ (-2*N)) ^ (n+1) := by
    intro n
    have harg : a * ((2:ℝ)^(-((n:ℤ)+1)))⁻¹ = a * (2:ℝ)^(n+1) := by
      rw [kq_two_zpow_neg_nat, inv_inv]
    have hy : 0 < a * (2:ℝ)^(n+1) := by positivity
    have h1 : F (-((n:ℤ)+1))
        ≤ ((a * (2:ℝ)^(n+1)) ^ (-N))^2 := by
      rw [hFdef]
      simp only [harg]
      exact pow_le_pow_left₀ (le_min hy.le (Real.rpow_nonneg hy.le _)) (min_le_right _ _) 2
    refine le_trans h1 ?_
    rw [kq_rpow_neg_sq hy]
    have h2 : (a * (2:ℝ)^(n+1)) ^ (-2*N) ≤ ((2:ℝ)^(n+1)) ^ (-2*N) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith : -2*N ≤ 0)
      nlinarith [ha1, pow_pos (by norm_num : (0:ℝ) < 2) (n+1)]
    refine le_trans h2 ?_
    have hR : ((2:ℝ) ^ (-2*N)) ^ (n+1) = (2:ℝ) ^ ((-2*N) * ((n+1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast ((2:ℝ)^(-2*N)) (n+1),
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hL : ((2:ℝ)^(n+1)) ^ (-2*N) = (2:ℝ) ^ (((n+1 : ℕ) : ℝ) * (-2*N)) := by
      rw [← Real.rpow_natCast (2:ℝ) (n+1),
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [hL, hR]
    rw [show (((n+1 : ℕ) : ℝ) * (-2*N)) = ((-2*N) * ((n+1 : ℕ) : ℝ)) by ring]
  -- summability of the two half-lines
  have hsump : Summable (fun n : ℕ => F ((n:ℤ)+1)) := by
    refine Summable.of_nonneg_of_le (fun n => hFnn _) hpos ?_
    have hg : Summable (fun n : ℕ => a^2 * ((4:ℝ)⁻¹)^(n+1)) :=
      ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_left _
    refine hg.congr (fun n => ?_)
    rw [inv_pow]
  have hsumn : Summable (fun n : ℕ => F (-((n:ℤ)+1))) := by
    refine Summable.of_nonneg_of_le (fun n => hFnn _) hneg ?_
    exact (summable_nat_add_iff 1).2
      (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))
  -- split and bound
  have hsplit := tsum_of_add_one_of_neg_add_one hsump hsumn
  have hvalp : (∑' n : ℕ, F ((n:ℤ)+1)) ≤ 4/3 := by
    have hgeom : (∑' n : ℕ, ((4:ℝ)⁻¹)^(n+1)) = (1:ℝ)/3 := by
      have hs : Summable (fun k : ℕ => ((4:ℝ)⁻¹)^k) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have h1 : (∑' n : ℕ, ((4:ℝ)⁻¹)^(n+1)) = ((4:ℝ)⁻¹) * ∑' k : ℕ, ((4:ℝ)⁻¹)^k := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [pow_succ']
      rw [h1, tsum_geometric_of_lt_one (by norm_num) (by norm_num : ((4:ℝ)⁻¹) < 1)]
      norm_num
    have hsv : Summable (fun n : ℕ => ((4:ℝ)⁻¹)^(n+1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    have hmaj : Summable (fun n : ℕ => a^2 * ((4:ℝ)⁻¹)^(n+1)) := hsv.mul_left _
    have h1 : (∑' n : ℕ, F ((n:ℤ)+1)) ≤ ∑' n : ℕ, a^2 * ((4:ℝ)⁻¹)^(n+1) := by
      apply Summable.tsum_le_tsum _ hsump hmaj
      intro n
      refine le_trans (hpos n) (le_of_eq ?_)
      rw [inv_pow]
    refine le_trans h1 ?_
    rw [tsum_mul_left, hgeom]
    have h4 : a^2 ≤ 4 := by nlinarith
    nlinarith
  have hvaln : (∑' n : ℕ, F (-((n:ℤ)+1))) ≤ (1 - (2:ℝ)^(-2*N))⁻¹ := by
    have hr0 : 0 ≤ (2:ℝ)^(-2*N) := Real.rpow_nonneg (by norm_num) _
    have hr1 : (2:ℝ)^(-2*N) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hgeom : (∑' n : ℕ, ((2:ℝ)^(-2*N))^(n+1))
        = ((2:ℝ)^(-2*N)) * (1 - (2:ℝ)^(-2*N))⁻¹ := by
      have hs : Summable (fun k : ℕ => ((2:ℝ)^(-2*N))^k) :=
        summable_geometric_of_lt_one hr0 hr1
      have h1 : (∑' n : ℕ, ((2:ℝ)^(-2*N))^(n+1))
          = ((2:ℝ)^(-2*N)) * ∑' k : ℕ, ((2:ℝ)^(-2*N))^k := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [pow_succ']
      rw [h1, tsum_geometric_of_lt_one hr0 hr1]
    have hmaj : Summable (fun n : ℕ => ((2:ℝ)^(-2*N))^(n+1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hr0 hr1)
    have h1 : (∑' n : ℕ, F (-((n:ℤ)+1))) ≤ ∑' n : ℕ, ((2:ℝ)^(-2*N))^(n+1) :=
      Summable.tsum_le_tsum hneg hsumn hmaj
    refine le_trans h1 ?_
    rw [hgeom]
    have h2 : 0 < 1 - (2:ℝ)^(-2*N) := by linarith
    have h3 : 0 ≤ (1 - (2:ℝ)^(-2*N))⁻¹ := (inv_pos.mpr h2).le
    exact mul_le_of_le_one_left h3 hr1.le
  have hF0 : F 0 ≤ 1 := by
    rw [hFdef]
    simp only [zpow_zero, inv_one, mul_one]
    have h1 : min a (a ^ (-N)) ≤ a ^ (-N) := min_le_right _ _
    have h2 : (a ^ (-N))^2 = a ^ (-2*N) := kq_rpow_neg_sq ha0
    calc (min a (a ^ (-N)))^2 ≤ (a^(-N))^2 := pow_le_pow_left₀ (le_min ha0.le (Real.rpow_nonneg ha0.le _)) h1 2
      _ = a ^ (-2*N) := h2
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
  rw [hsplit]
  linarith


/-- There is a dyadic rescaling putting `a` into `[1,2]`. -/
private lemma kq_exists_zpow_between (a : ℝ) (ha : 0 < a) :
    ∃ n : ℤ, 1 ≤ a * (2:ℝ)^n ∧ a * (2:ℝ)^n ≤ 2 := by
  rcases le_or_gt 1 a with ha1 | ha1
  · have hex : ∃ i : ℕ, a * (2:ℝ)^(-(i:ℤ)) ≤ 1 := by
      obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt a (by norm_num : (1:ℝ) < 2)
      refine ⟨i, ?_⟩
      rw [zpow_neg, zpow_natCast]
      calc a * ((2:ℝ)^i)⁻¹ ≤ (2:ℝ)^i * ((2:ℝ)^i)⁻¹ := by
            gcongr
          _ = 1 := by rw [mul_inv_cancel₀ (by positivity)]
    set i := Nat.find hex with hidef
    have hi1 : a * (2:ℝ)^(-(i:ℤ)) ≤ 1 := Nat.find_spec hex
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hai1 : a ≤ 1 := by
        have h := hi1
        rw [hi0] at h
        simpa using h
      refine ⟨0, ?_, ?_⟩ <;> simp only [zpow_zero, mul_one] <;> linarith
    · have hprev : ¬ (a * (2:ℝ)^(-(((i-1:ℕ)):ℤ)) ≤ 1) :=
        Nat.find_min hex (by omega)
      have hlt : 1 < a * (2:ℝ)^(-(((i-1:ℕ)):ℤ)) := not_le.mp hprev
      have hz : a * (2:ℝ)^(-(((i-1:ℕ)):ℤ)) = 2 * (a * (2:ℝ)^(-(i:ℤ))) := by
        have h2 : (2:ℝ)^(-(((i-1:ℕ)):ℤ)) = 2 * (2:ℝ)^(-(i:ℤ)) := by
          have h1 : ((i:ℤ)) = ((i-1:ℕ):ℤ) + 1 := by omega
          rw [h1, neg_add_rev, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_neg_one]
          field_simp
        rw [h2]; ring
      refine ⟨-(((i-1:ℕ)):ℤ), by linarith, ?_⟩
      rw [hz]
      nlinarith [hi1]
  · have hex : ∃ j : ℕ, 1 ≤ a * (2:ℝ)^(j:ℤ) := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1/a) (by norm_num : (1:ℝ) < 2)
      refine ⟨j, ?_⟩
      rw [zpow_natCast]
      have h2 : 1 ≤ a * (2:ℝ)^j := by
        have h3 := mul_le_mul_of_nonneg_left hj.le ha.le
        rw [one_div] at h3
        rw [mul_inv_cancel₀ (ne_of_gt ha)] at h3
        simpa [mul_comm] using h3
      exact h2
    set j := Nat.find hex with hjdef
    have hj1 : 1 ≤ a * (2:ℝ)^(j:ℤ) := Nat.find_spec hex
    have hjpos : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hp
      · rw [hj0] at hj1; simp at hj1; linarith
      · exact hp
    have hprev : ¬ (1 ≤ a * (2:ℝ)^((((j-1:ℕ)):ℤ))) := Nat.find_min hex (by omega)
    have hlt : a * (2:ℝ)^((((j-1:ℕ)):ℤ)) < 1 := not_le.mp hprev
    have hz : a * (2:ℝ)^(j:ℤ) = 2 * (a * (2:ℝ)^((((j-1:ℕ)):ℤ))) := by
      have h1 : ((j:ℤ)) = ((j-1:ℕ):ℤ) + 1 := by omega
      rw [h1, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0), zpow_natCast]
      ring
    refine ⟨(j:ℤ), hj1, ?_⟩
    rw [hz]; linarith

/-- The dyadic sum is invariant under dyadic rescaling of the parameter. -/
private lemma kq_scale_inv (N : ℝ) (a : ℝ) (n : ℤ) :
    (∑' l : ℤ, (min ((a * (2:ℝ)^n) * (2:ℝ)^(-l))
        (((a * (2:ℝ)^n) * (2:ℝ)^(-l)) ^ (-N))) ^ 2)
      = (∑' l : ℤ, (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) := by
  have hpt : ∀ l : ℤ, (a * (2:ℝ)^n) * (2:ℝ)^(-l) = a * (2:ℝ)^(-(l - n)) := by
    intro l
    rw [mul_assoc a ((2:ℝ)^n) ((2:ℝ)^(-l)), ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    congr 2
    ring
  simp only [hpt]
  have hre : (∑' l : ℤ, (min (a * (2:ℝ)^(-(l - n))) ((a * (2:ℝ)^(-(l - n))) ^ (-N))) ^ 2)
      = (∑' l : ℤ, (min (a * (2:ℝ)^(-(l + (-n)))) ((a * (2:ℝ)^(-(l + (-n)))) ^ (-N))) ^ 2) := by
    apply tsum_congr
    intro l
    rw [show l - n = l + (-n) by ring]
  rw [hre]
  convert (Equiv.addRight (-n)).tsum_eq
    (fun l : ℤ => (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) using 2
  rw [Equiv.coe_addRight]


/-- The tail sums appearing in the dyadic min-sum are summable (needed to interchange
`ENNReal.ofReal` with the `ℤ`-indexed `tsum` in applications). -/
theorem kq_summable_min_pow_sq (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 < a) :
    Summable (fun l : ℤ => (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) := by
  set F : ℤ → ℝ := fun l => (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2 with hFdef
  have hFnn : ∀ l : ℤ, 0 ≤ F l := fun l => sq_nonneg _
  have hpos : ∀ n : ℕ, F ((n:ℤ)+1) ≤ a^2 * ((4:ℝ)^(n+1))⁻¹ := by
    intro n
    have hzz : (2:ℝ)^(-(((n:ℤ)+1))) = ((2:ℝ)^(n+1))⁻¹ := by
      rw [kq_two_zpow_neg_nat]
    have hx : 0 < a * (2:ℝ)^(-(((n:ℤ)+1))) := mul_pos ha (zpow_pos (by norm_num) _)
    have h1 : F ((n:ℤ)+1) ≤ (a * (2:ℝ)^(-(((n:ℤ)+1))))^2 := by
      simp only [hFdef]
      exact pow_le_pow_left₀ (le_min hx.le (Real.rpow_nonneg hx.le _)) (min_le_left _ _) 2
    refine le_trans h1 ?_
    rw [hzz, mul_pow, inv_pow]
    have h3 : ((2:ℝ)^(n+1))^2 = (4:ℝ)^(n+1) := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h3]
  have hneg : ∀ n : ℕ, F (-((n:ℤ)+1)) ≤ (a^(-N))^2 * ((2:ℝ)^(-2*N))^(n+1) := by
    intro n
    have hzz : (2:ℝ)^(-(((n:ℤ)+1))) = ((2:ℝ)^(n+1))⁻¹ := by rw [kq_two_zpow_neg_nat]
    have hy : 0 < a * ((2:ℝ)^(-(((n:ℤ)+1))))⁻¹ := mul_pos ha (inv_pos.mpr (zpow_pos (by norm_num) _))
    have h1 : F (-((n:ℤ)+1)) ≤ ((a * ((2:ℝ)^(-(((n:ℤ)+1))))⁻¹) ^ (-N))^2 := by
      simp only [hFdef]
      have heq : a * (2:ℝ)^(-(-((n:ℤ)+1))) = a * ((2:ℝ)^(-(((n:ℤ)+1))))⁻¹ := by
        rw [zpow_neg]
      rw [heq]
      exact pow_le_pow_left₀ (le_min hy.le (Real.rpow_nonneg hy.le _)) (min_le_right _ _) 2
    have hxx : a * ((2:ℝ)^(-(((n:ℤ)+1))))⁻¹ = a * (2:ℝ)^(n+1) := by
      rw [hzz, inv_inv]
    rw [hxx] at h1
    refine le_trans h1 ?_
    have hsq : ((a * (2:ℝ)^(n+1)) ^ (-N))^2 = (a * (2:ℝ)^(n+1)) ^ (-2*N) := by
      rw [← Real.rpow_natCast ((a * (2:ℝ)^(n+1)) ^ (-N)) 2, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [hsq]
    have h2 : (a * (2:ℝ)^(n+1)) ^ (-2*N) ≤ (a^(-N))^2 * ((2:ℝ)^(-2*N))^(n+1) := by
      have hsplit : (a * (2:ℝ)^(n+1)) ^ (-2*N)
          = a ^ (-2*N) * ((2:ℝ)^(n+1)) ^ (-2*N) := by
        rw [Real.mul_rpow (le_of_lt ha) (by positivity : (0:ℝ) ≤ (2:ℝ)^(n+1))]
      rw [hsplit]
      have haN : a ^ (-2*N) = (a^(-N))^2 := by
        rw [← Real.rpow_natCast (a ^ (-N)) 2, ← Real.rpow_mul (le_of_lt ha)]
        congr 1
        ring
      rw [haN]
      have h2N : ((2:ℝ)^(n+1)) ^ (-2*N) = ((2:ℝ)^(-2*N))^(n+1) := by
        rw [← Real.rpow_natCast (2:ℝ) (n+1), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
          ← Real.rpow_natCast ((2:ℝ)^(-2*N)) (n+1), ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      rw [h2N]
    exact h2
  have hsump : Summable (fun n : ℕ => F ((n:ℤ)+1)) := by
    refine Summable.of_nonneg_of_le (fun n => hFnn _) hpos ?_
    have hg : Summable (fun n : ℕ => a^2 * ((4:ℝ)⁻¹)^(n+1)) :=
      ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_left _
    refine hg.congr (fun n => ?_)
    rw [inv_pow]
  have hsumn : Summable (fun n : ℕ => F (-((n:ℤ)+1))) := by
    refine Summable.of_nonneg_of_le (fun n => hFnn _) hneg ?_
    have hr0 : 0 ≤ (2:ℝ)^(-2*N) := Real.rpow_nonneg (by norm_num) _
    have hr1 : (2:ℝ)^(-2*N) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have h0 : Summable (fun n : ℕ => ((2:ℝ)^(-2*N))^(n+1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hr0 hr1)
    exact h0.mul_left _
  exact Summable.of_add_one_of_neg_add_one hsump hsumn

/-- Explicit form of `tsum_min_pow_sq_le`. -/
theorem kq_tsum_min_pow_sq_le_explicit (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 < a) :
    (∑' l : ℤ, (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2)
      ≤ 1 + (4/3 : ℝ) + (1 - (2:ℝ)^(-2 * N))⁻¹ := by
  obtain ⟨n, hn1, hn2⟩ := kq_exists_zpow_between a ha
  rw [← kq_scale_inv N a n]
  exact kq_scaled_bound N hN hn1 hn2

/-- **`ENNReal` form.**  For every `N > 0` and `a > 0` the `ENNReal`-valued dyadic sum is bounded
by an explicit constant — the exact form needed to feed the dyadic square function of the dilates of
a mean-zero kernel into `l2_multiplier_sum_square_function`. -/
theorem kq_ofReal_tsum_min_pow_sq_le (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 < a) :
    (∑' l : ℤ, ENNReal.ofReal
        ((min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2))
      ≤ ENNReal.ofReal (1 + (4/3 : ℝ) + (1 - (2:ℝ)^(-2 * N))⁻¹) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) (kq_summable_min_pow_sq N hN a ha)]
  exact ENNReal.ofReal_le_ofReal (kq_tsum_min_pow_sq_le_explicit N hN a ha)

/-- **Numerical companion of Bourgain (1989), (3.14), with a general decay exponent.**

For every `N > 0` and every `a > 0`, the two-sided dyadic sum of `min(x, x^(-N))^2` along the
geometric progression `x_l = a * 2^(-l)` is bounded independently of `a`.  This is the
general-exponent companion of `Commons.Analysis.ExponentialSums.tsum_min_inv_sq_le`, and the
numerical input of `dyadic_square_function_l2` (the dyadic square function of the dilates of a
mean-zero kernel). -/
theorem kq_tsum_int_min_pow_sq_le (N : ℝ) (hN : 0 < N) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a : ℝ), 0 < a →
      (∑' l : ℤ, (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) ≤ B := by
  have hr1 : (2:ℝ)^(-2*N) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : 0 < 1 + (4/3 : ℝ) + (1 - (2:ℝ)^(-2*N))⁻¹ := by
    have : 0 < 1 - (2:ℝ)^(-2*N) := by linarith
    positivity
  refine ⟨1 + (4/3 : ℝ) + (1 - (2:ℝ)^(-2*N))⁻¹, hpos, ?_⟩
  intro a ha
  obtain ⟨n, hn1, hn2⟩ := kq_exists_zpow_between a ha
  rw [← kq_scale_inv N a n]
  exact kq_scaled_bound N hN hn1 hn2






private lemma kq_enorm_pow_two_eq (z : ℂ) : ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  have h1 : ‖z‖ₑ = ENNReal.ofReal ‖z‖ :=
    Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm z
  rw [h1, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  exact (ENNReal.ofReal_pow (norm_nonneg z) 2).symm

theorem tsum_dilate_fourier_sq_le (K : ℝ → ℂ)
    (hK : Integrable K (volume : Measure ℝ))
    (hxK : Integrable (fun x : ℝ => x • K x) (volume : Measure ℝ))
    (h0 : ∫ x : ℝ, K x = 0)
    {C N : ℝ} (hC : 0 < C) (hN : 0 < N)
    (hdec : ∀ ξ : ℝ, ‖𝓕 K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℝ,
      (∑' l : ℤ, ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal (A ^ 2) := by
  set c : ℝ := 2 * Real.pi * ∫ x : ℝ, ‖x • K x‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set B : ℝ := 1 + (4/3 : ℝ) + (1 - (2:ℝ)^(-2*N))⁻¹ with hB
  have hB0 : 0 < B := by
    rw [hB]
    have hr1 : (2:ℝ)^(-2*N) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 < 1 - (2:ℝ)^(-2*N) := by linarith
    positivity
  refine ⟨Real.sqrt ((max c C) ^ 2 * B) + 1, by positivity, ?_⟩
  intro ξ
  rcases eq_or_lt_of_le (abs_nonneg ξ) with hξ | hξ
  · have hξ0 : ξ = 0 := abs_eq_zero.mp hξ.symm
    subst hξ0
    have hz : 𝓕 K 0 = 0 := by
      rw [Real.fourier_eq]
      simpa using h0
    simp [hz]
  · set a : ℝ := |ξ| with ha
    have ha0 : 0 < a := hξ
    have hpt : ∀ l : ℤ, ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖
        ≤ max c C * (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) := by
      intro l
      have h2l : 0 < (2:ℝ)^(-l) := zpow_pos (by norm_num) _
      have habs : |(2:ℝ)^(-l) * ξ| = a * (2:ℝ)^(-l) := by
        rw [ha, abs_mul, abs_of_pos h2l, mul_comm]
      have h1 : ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ≤ c * (a * (2:ℝ)^(-l)) := by
        have h := kq_fourier_le_abs_mul_of_integral_zero K hK hxK h0
          ((2:ℝ)^(-l) * ξ)
        rw [habs] at h
        rw [hc]
        convert h using 1
        ring
      have h2 : ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ≤ C * ((a * (2:ℝ)^(-l)) ^ (-N)) := by
        have h3 := hdec ((2:ℝ)^(-l) * ξ)
        have h4 : (1 + |(2:ℝ)^(-l) * ξ|) ^ (-N) ≤ ((a * (2:ℝ)^(-l)) ^ (-N)) := by
          apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith : -N ≤ 0)
          rw [habs]; linarith
        exact le_trans h3 (mul_le_mul_of_nonneg_left h4 hC.le)
      have hA0 : 0 ≤ a * (2:ℝ)^(-l) := by positivity
      have hB0' : 0 ≤ (a * (2:ℝ)^(-l)) ^ (-N) := Real.rpow_nonneg hA0 _
      rcases le_total (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N)) with hAB | hAB
      · rw [min_eq_left hAB]
        exact le_trans (le_min h1 h2)
          (le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right (le_max_left c C) hA0))
      · rw [min_eq_right hAB]
        exact le_trans (le_min h1 h2)
          (le_trans (min_le_right _ _) (mul_le_mul_of_nonneg_right (le_max_right c C) hB0'))
    -- pointwise `ENNReal` bound
    have hstep : ∀ l : ℤ, ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal ((max c C) ^ 2 * (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) := by
      intro l
      rw [kq_enorm_pow_two_eq]
      apply ENNReal.ofReal_le_ofReal
      have h1 : ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ^ 2
          ≤ (max c C * (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N)))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hpt l) 2
      calc ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ^ 2
          ≤ (max c C * min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2 := h1
        _ = (max c C) ^ 2 * (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2 := by ring
    -- sum up
    have hfin : (∑' l : ℤ, ENNReal.ofReal
        ((min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2))
        ≤ ENNReal.ofReal B := by
      rw [hB]
      exact kq_ofReal_tsum_min_pow_sq_le N hN a ha0
    calc (∑' l : ℤ, ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ₑ ^ (2:ℝ))
        ≤ ∑' l : ℤ, ENNReal.ofReal ((max c C) ^ 2
            * (min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) :=
          ENNReal.tsum_le_tsum hstep
      _ = ENNReal.ofReal ((max c C) ^ 2) * ∑' l : ℤ, ENNReal.ofReal
            ((min (a * (2:ℝ)^(-l)) ((a * (2:ℝ)^(-l)) ^ (-N))) ^ 2) := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro l
          rw [ENNReal.ofReal_mul (sq_nonneg (max c C))]
      _ ≤ ENNReal.ofReal ((max c C) ^ 2) * ENNReal.ofReal B := by
          exact mul_le_mul' le_rfl hfin
      _ = ENNReal.ofReal ((max c C) ^ 2 * B) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg (max c C))]
      _ ≤ ENNReal.ofReal ((Real.sqrt ((max c C) ^ 2 * B) + 1) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (max c C)^2 * B),
            Real.sqrt_nonneg ((max c C)^2 * B)]


/-! ### The dyadic `q`-block decomposition of the major-arc model -/

/-- The `q`-layer of the `m`-th dyadic block of `majorArcModel (1/4) N`: it is the `q`-th
`majorArcBlock` when `2^m ≤ q < 2^(m+1)`, and `0` otherwise. -/
noncomputable def majorArcModelBlock (m N : ℕ) (α : ℝ) (q : ℕ) : ℂ :=
  if 2 ^ m ≤ q ∧ q < 2 ^ (m + 1) then majorArcBlock ((1 : ℝ) / 4) N α q else 0

lemma log2_le_floor_pow_quarter {N q : ℕ} (hq1 : 1 ≤ q)
    (hq2 : q ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))) :
    Nat.log 2 q ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) := by
  by_contra hlt
  push Not at hlt
  have hqne : q ≠ 0 := by omega
  have hle : Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1 ≤ Nat.log 2 q := Nat.succ_le_of_lt hlt
  have h2 : 2 ^ (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1) ≤ q := by
    have := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hqne).mp hle
    simpa using this
  have h3 : Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) < 2 ^ (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self (n := Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
  omega

lemma sum_block_eq_block (N : ℕ) (α : ℝ) (q : ℕ) (hq1 : 1 ≤ q)
    (hq2 : q ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))) :
    (∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1),
        majorArcModelBlock m N α q)
      = majorArcBlock ((1 : ℝ) / 4) N α q := by
  have hmem : Nat.log 2 q ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (log2_le_floor_pow_quarter hq1 hq2))
  have hlog : 2 ^ (Nat.log 2 q) ≤ q ∧ q < 2 ^ (Nat.log 2 q + 1) :=
    ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) q⟩
  have hblk : majorArcModelBlock (Nat.log 2 q) N α q = majorArcBlock ((1 : ℝ) / 4) N α q := by
    rw [majorArcModelBlock, if_pos hlog]
  rw [← hblk]
  refine Finset.sum_eq_single (f := fun m => majorArcModelBlock m N α q) (Nat.log 2 q) ?_ ?_
  · intro m hm hmne
    show majorArcModelBlock m N α q = 0
    rw [majorArcModelBlock, if_neg]
    rintro ⟨h1, h2⟩
    exact hmne (Nat.log_eq_of_pow_le_of_lt_pow h1 h2).symm
  · intro hnot; exact absurd hmem hnot

/-- **Exact dyadic-block decomposition of the major-arc model.** -/
theorem majorArcModel_eq_sum_block (N : ℕ) (α : ℝ) :
    majorArcModel ((1 : ℝ) / 4) N α
      = ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1),
          ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))), majorArcModelBlock m N α q := by
  rw [majorArcModel]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
  exact (sum_block_eq_block N α q hq1 hq2).symm

/-- **Gauss-sum bound for the model weight.**  For reduced `a/q` with `q ≥ 2^m`, the weight
`w = q⁻¹ ∑_{r<q} e(a r²/q)` of a single major-arc term is `≤ A · 2^{-m/2}` in modulus for an
absolute constant `A`. -/
lemma norm_modelWeight_le :
    ∃ A : ℝ, 0 < A ∧ ∀ (q m : ℕ) (a : ℤ), 1 ≤ q → 2 ^ m ≤ q → Int.gcd a (q : ℤ) = 1 →
      ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ 2 / (q : ℂ)))‖
        ≤ A * (2 : ℝ) ^ (-(m : ℝ) / 2) := by
  obtain ⟨C, hCpos, hC⟩ := quadratic_gauss_sum_bound
  refine ⟨C, hCpos, ?_⟩
  intro q m a hq1 hq hgcd
  have hqpos : 0 < q := hq1
  have hgsq : ‖∑ r ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ 2 / (q : ℂ)))‖
      ≤ C * Real.sqrt (q : ℝ) := hC q a hqpos hgcd
  have h1 : ‖((q : ℂ))⁻¹‖ = (q : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hqm : (2 : ℝ) ^ m ≤ (q : ℝ) := by exact_mod_cast hq
  have hsqrt2m : Real.sqrt ((2 : ℝ) ^ m) = (2 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, show ((2 : ℝ) ^ m : ℝ) = (2 : ℝ) ^ ((m : ℝ)) by
        rw [Real.rpow_natCast], ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; ring
  have hsqrtq : (2 : ℝ) ^ ((m : ℝ) / 2) ≤ Real.sqrt (q : ℝ) := by
    rw [← hsqrt2m]; exact Real.sqrt_le_sqrt hqm
  have hexp : (2 : ℝ) ^ (-(m : ℝ) / 2) = ((2 : ℝ) ^ ((m : ℝ) / 2))⁻¹ := by
    rw [show (-(m:ℝ)/2) = -((m:ℝ)/2) by ring, Real.rpow_neg (by norm_num)]
  rw [norm_mul, h1]
  have hsqrtpos : (0 : ℝ) < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqposR
  have hkey : (q : ℝ)⁻¹ * (C * Real.sqrt (q : ℝ)) = C * (1 / Real.sqrt (q : ℝ)) := by
    have hsq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := by
      rw [← sq, Real.sq_sqrt (le_of_lt hqposR)]
    field_simp
    nlinarith [hsq]
  have hle : (1 : ℝ) / Real.sqrt (q : ℝ) ≤ (2 : ℝ) ^ (-(m : ℝ) / 2) := by
    rw [hexp, one_div, inv_le_inv₀ hsqrtpos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact hsqrtq
  calc (q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ 2 / (q : ℂ)))‖
      ≤ (q : ℝ)⁻¹ * (C * Real.sqrt (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hgsq (by positivity)
    _ = C * (1 / Real.sqrt (q : ℝ)) := hkey
    _ ≤ C * (2 : ℝ) ^ (-(m : ℝ) / 2) := mul_le_mul_of_nonneg_left hle (le_of_lt hCpos)



/-! ### The model is a single major-arc term (hence bounded by `1`) -/

/-- **The major-arc model takes at most one term.**  Since the major arcs
`|α - a/q - l| ≤ N^{-5/4}` of `majorArcModel (1/4) N` (`q ≤ N^{1/4}`, `l ∈ [-2,2]`)
are pairwise `≥ 1/(q q') ≥ N^{-1/2} > 2 N^{-5/4}` apart, at every frequency `α ∈ [0,1]`
at most one term of the model is switched on.  Consequently, for `N ≥ 3`,

  `‖majorArcModel (1/4) N α‖ ≤ 1`,

the bound being the Gauss-sum bound `|q⁻¹ ∑_{r<q} e(a r²/q)| ≤ 1` for the single
contributing term (the Fresnel factor `∫_0^1 e(β N² s²) ds` being bounded by `1`). -/
theorem majorArcModel_norm_le_one {N : ℕ} (hN : 3 ≤ N) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ‖majorArcModel ((1 : ℝ) / 4) N α‖ ≤ 1 := by
  by_cases h : ∃ x : ℕ × ℕ × ℤ,
      1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) ∧ x.2.1 < x.1 ∧
      Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
      |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ ((N : ℝ) ^ (1 + (1 : ℝ) / 4))⁻¹
  · rw [majorArcModel_eq_single (by norm_num) (by norm_num) hN h0 h1 h]
    exact norm_modelTerm_le_one N h.choose.1 h.choose.2.1 h.choose.2.2 α
  · rw [majorArcModel_eq_zero h]
    simp

/-! ### The `q`-block (`Nat.log 2`-graded) decomposition of the model

These connect `majorArcModel` to the `m`-th block used by
`Commons.Analysis.ExponentialSums.majorArcModel_block_maximal_l2`. -/


noncomputable def modelQBlock (m N : ℕ) (θ : ℝ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter (fun q => Nat.log 2 q = m),
    majorArcBlock ((1:ℝ)/4) N θ q

lemma filter_log_eq_filter_pow (E m : ℕ) :
    (Finset.Icc 1 E).filter (fun q => Nat.log 2 q = m)
      = (Finset.Icc 1 E).filter (fun q => 2 ^ m ≤ q ∧ q < 2 ^ (m + 1)) := by
  apply Finset.filter_congr
  intro q hq
  obtain ⟨hq1, _⟩ := Finset.mem_Icc.mp hq
  constructor
  · intro h
    rw [← h]
    exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) q⟩
  · intro ⟨h1, h2⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

lemma sum_modelQBlock_eq (m N : ℕ) (θ : ℝ) :
    (∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
        if 2 ^ m ≤ q ∧ q < 2 ^ (m + 1) then majorArcBlock ((1:ℝ)/4) N θ q else 0)
      = modelQBlock m N θ := by
  rw [modelQBlock, filter_log_eq_filter_pow, Finset.sum_filter]

lemma majorArcModel_eq_sum_modelQBlock (N : ℕ) (θ : ℝ) :
    majorArcModel ((1:ℝ)/4) N θ
      = ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) + 1), modelQBlock m N θ := by
  rw [majorArcModel_eq_sum_block]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show (∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
      majorArcModelBlock m N θ q)
      = (∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
          if 2 ^ m ≤ q ∧ q < 2 ^ (m + 1) then majorArcBlock ((1:ℝ)/4) N θ q else 0) from by
    apply Finset.sum_congr rfl
    intro q hq
    rw [majorArcModelBlock]]
  exact sum_modelQBlock_eq m N θ


/-! ### The maximal operators of the model and of its `q`-blocks -/

lemma conj_model_eq_sum_block (k : ℕ) (θ : ℝ) :
    (starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ))
      = ∑ m ∈ Finset.range (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1),
          (starRingEnd ℂ (modelQBlock m (2^k) θ)) := by
  rw [majorArcModel_eq_sum_modelQBlock]
  simp only [map_sum]


/-! ### The target theorem -/

/-- **Bourgain's `ℓ²` maximal estimate for the major-arc model multipliers** (discrete form of
Bourgain 1989, Lemma 4.1).  The maximal operator over the dyadic scales `2^k` of the multipliers
`conj (majorArcModel (1/4) (2^k) ·)` is bounded on `ℓ²(ℤ)`.

The proof (see `Submission/Work/Analysis/ExponentialSums/quadratic_kernel_model_STATUS.md`)
reduces this, via the dyadic-block decomposition `majorArcModel_eq_sum_block` and the exact dyadic
decomposition of the Fresnel factor, to the deep windowed maximal estimate
`Commons.Analysis.Fourier.smooth_window_neighborhood_maximal_l2_scaled` (Bourgain's Lemma
4.13 / 4.26). -/

lemma measurable_majorArcBlock (δ : ℝ) (N q : ℕ) :
    Measurable (fun α : ℝ => majorArcBlock δ N α q) := by
  unfold majorArcBlock
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.ite (by measurability) ?_ measurable_const
  refine Finset.measurable_sum _ (fun l _ => ?_)
  exact Measurable.ite (by measurability) (measurable_modelTerm N q a l) measurable_const

lemma measurable_modelQBlock (m N : ℕ) :
    Measurable (fun θ : ℝ => modelQBlock m N θ) := by
  unfold modelQBlock
  exact Finset.measurable_sum _ (fun q _ => measurable_majorArcBlock ((1:ℝ)/4) N q)

lemma norm_majorArcBlock_le (δ : ℝ) (N q : ℕ) (α : ℝ) :
    ‖majorArcBlock δ N α q‖ ≤ 5 * (q : ℝ) := by
  rw [majorArcBlock]
  have h1 : ‖∑ a ∈ Finset.range q,
      (if Nat.gcd a q = 1 then
        ∑ l ∈ Finset.Icc (-2 : ℤ) 2,
          (if |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹
            then modelTerm N q a l α else 0)
        else 0 : ℂ)‖ ≤ ∑ _a ∈ Finset.range q, (5 : ℝ) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a _ => ?_))
    by_cases hg : Nat.gcd a q = 1
    · rw [if_pos hg]
      have h2 : ‖∑ l ∈ Finset.Icc (-2 : ℤ) 2,
          (if |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹
            then modelTerm N q a l α else 0 : ℂ)‖
          ≤ ∑ _l ∈ Finset.Icc (-2 : ℤ) 2, (1 : ℝ) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l _ => ?_))
        by_cases hl : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹
        · rw [if_pos hl]; exact norm_modelTerm_le_one N q a l α
        · rw [if_neg hl]; simp
      refine le_trans h2 (le_of_eq ?_)
      simp
    · rw [if_neg hg]
      simp
  refine le_trans h1 (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma norm_modelQBlock_le (m N : ℕ) (θ : ℝ) :
    ‖modelQBlock m N θ‖
      ≤ 5 * ((Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) : ℝ))^2 := by
  set Q := Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) with hQ
  have hQnn : (0:ℝ) ≤ (Q : ℝ) := by positivity
  calc ‖∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m),
        majorArcBlock ((1:ℝ)/4) N θ q‖
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m),
          ‖majorArcBlock ((1:ℝ)/4) N θ q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m), 5 * (q : ℝ) :=
        Finset.sum_le_sum (fun q _ => norm_majorArcBlock_le ((1:ℝ)/4) N q θ)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, 5 * (q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun q _ _ => by positivity)
    _ = 5 * ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 5 * (Q : ℝ)^2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) :=
              Finset.sum_le_sum (fun q hq => by
                exact_mod_cast (Finset.mem_Icc.mp hq).2)
          _ = (Q : ℝ) * Q := by
              rw [Finset.sum_const, nsmul_eq_mul]
              simp
          _ = (Q : ℝ)^2 := by ring

/-! ### The maximal operators and the block split -/

noncomputable def TkMax (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)) *
    (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
    Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))

noncomputable def TkBlockMax (g : ℤ → ℂ) (s : Finset ℤ) (m k : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (modelQBlock m (2^k) θ)) *
    (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
    Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))

lemma norm_exp_pure_imag (x : ℤ) (θ : ℝ) :
    ‖Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ = 1 := by
  have h : -(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))
      = ((-(2*Real.pi*(x:ℝ)*(θ:ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_modelP_le (g : ℤ → ℂ) (s : Finset ℤ) (θ : ℝ) :
    ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ ≤ ∑ j ∈ s, ‖g j‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul]
  have h : ‖Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ = 1 := by
    have h2 : 2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ)
        = (((2*Real.pi*(j:ℝ)*(θ:ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h2, Complex.norm_exp_ofReal_mul_I]
  rw [h, mul_one]

lemma intervalIntegrable_block (g : ℤ → ℂ) (s : Finset ℤ) (m k : ℕ) (x : ℤ) :
    IntervalIntegrable (fun θ : ℝ => (starRingEnd ℂ (modelQBlock m (2^k) θ)) *
      (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
      Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))) volume 0 1 := by
  rw [intervalIntegrable_iff]
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
        Real.volume_Ioc]; norm_num⟩
  refine MeasureTheory.Integrable.of_bound ?_ (5 * ((Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) : ℝ))^2
      * (∑ j ∈ s, ‖g j‖)) ?_
  · exact (((Complex.continuous_conj.measurable.comp (measurable_modelQBlock m (2^k))).mul
      (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with θ
    rw [norm_mul, norm_mul, norm_exp_pure_imag x θ]
    have hP := norm_modelP_le g s θ
    have hb := norm_modelQBlock_le m (2^k) θ
    calc ‖(starRingEnd ℂ (modelQBlock m (2^k) θ))‖ *
            ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ * 1
        = ‖modelQBlock m (2^k) θ‖ *
            ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ := by
          rw [Complex.norm_conj, mul_one]
      _ ≤ (5 * ((Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) : ℝ))^2) * (∑ j ∈ s, ‖g j‖) := by
          apply mul_le_mul hb hP (by positivity) (by positivity)

lemma TkMax_eq_sum_block (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) :
    TkMax g s k x
      = ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
          TkBlockMax g s m k x := by
  rw [TkMax]
  simp only [TkBlockMax]
  rw [show (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)) *
        (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))))
      = ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
          ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (modelQBlock m (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
            Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))) from ?_]
  · -- integrand : conj(model) = sum of conj(blocks)
    rw [show (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)) *
        (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))))
        = ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (modelQBlock m (2^k) θ))) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))) from by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [conj_model_eq_sum_block]]
    rw [show (∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (modelQBlock m (2^k) θ))) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))))
        = ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (modelQBlock m (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
            Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))) from by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [Finset.sum_mul, Finset.sum_mul]]
    rw [intervalIntegral.integral_finsetSum]
    intro m hm
    exact intervalIntegrable_block g s m k x

lemma Tsup_le_tsum (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    (⨆ k : ℕ, ‖TkMax g s k x‖ₑ)
      ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ := by
  refine iSup_le (fun k => ?_)
  calc ‖TkMax g s k x‖ₑ
      = ‖∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            TkBlockMax g s m k x‖ₑ := by rw [TkMax_eq_sum_block]
    _ ≤ ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            ‖TkBlockMax g s m k x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ := by
        calc ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
              ‖TkBlockMax g s m k x‖ₑ
            ≤ ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
              ⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ :=
              Finset.sum_le_sum (fun m _ => le_iSup (fun k => ‖TkBlockMax g s m k x‖ₑ) k)
          _ ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ := ENNReal.sum_le_tsum _

/-- Pointwise weighted Cauchy--Schwarz for the blocks (via Hölder on `Measure.count`). -/
lemma block_cauchy (d : ℕ → ℝ≥0∞) :
    (∑' m : ℕ, d m)^(2:ℝ) ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
      (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4)) * d m)^(2:ℝ)) := by
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count (p := 2) (q := 2)
    (f := fun m : ℕ => (2:ℝ≥0∞)^(-(m:ℝ)/4)) (g := fun m : ℕ => (2:ℝ≥0∞)^((m:ℝ)/4) * d m)
    (by rw [Real.holderConjugate_iff]; norm_num)
    (Measurable.aemeasurable (measurable_of_countable _))
    (Measurable.aemeasurable (measurable_of_countable _))
  rw [lintegral_count, lintegral_count, lintegral_count] at hhold
  simp only [Pi.mul_apply] at hhold
  have h2 : (∑' m : ℕ, (2:ℝ≥0∞)^(-(m:ℝ)/4) * ((2:ℝ≥0∞)^((m:ℝ)/4) * d m))
      = ∑' m : ℕ, d m := by
    apply tsum_congr; intro m
    rw [← mul_assoc, ← ENNReal.rpow_add (-(m:ℝ)/4) ((m:ℝ)/4) (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞), show (-(m:ℝ)/4 + (m:ℝ)/4) = 0 by ring,
      ENNReal.rpow_zero, one_mul]
  rw [h2] at hhold
  calc (∑' m : ℕ, d m)^(2:ℝ)
      ≤ (((∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ))^(1/(2:ℝ))) *
          ((∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4)) * d m)^(2:ℝ))^(1/(2:ℝ))))^(2:ℝ) :=
        ENNReal.rpow_le_rpow hhold (by norm_num)
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
        (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4)) * d m)^(2:ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

lemma tsum_block_weight_lt_top :
    (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) < ∞ := by
  have hW : (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ))
      = ∑' m : ℕ, ENNReal.ofReal ((2:ℝ)^(-(m:ℝ)/2)) := by
    apply tsum_congr; intro m
    have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
    rw [h2, ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_pos (x := 2) (show (0:ℝ) < 2 by norm_num)]
    congr 1
    ring
  have hsum : Summable (fun m : ℕ => (2:ℝ)^(-(m:ℝ)/2)) := by
    have heq : (fun m : ℕ => (2:ℝ)^(-(m:ℝ)/2))
        = fun m : ℕ => ((2:ℝ)^(-(1:ℝ)/2))^m := by
      funext m
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; push_cast; ring
    rw [heq]
    exact summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  rw [hW, ← ENNReal.ofReal_tsum_of_nonneg (fun m => Real.rpow_nonneg (by norm_num) _) hsum]
  exact ENNReal.ofReal_lt_top

/-- **The block maximal bound implies the model maximal bound.**  For each `m` assume the dyadic
maximal of the `m`-th `q`-block of the model is bounded by `K m · G`; then the dyadic maximal of
the whole model is bounded by `(Σ' 2^{-m/2})·(Σ' 2^{m/2} K m)·G`. -/
lemma lintegral_Tsup_sq_le (g : ℤ → ℂ) (s : Finset ℤ) (K : ℕ → ℝ≥0∞) (G : ℝ≥0∞)
    (hblk : ∀ m : ℕ,
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        ≤ K m * G) :
    ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkMax g s k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
        (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m)) * G := by
  have h1 : ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkMax g s k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ)
          ∂MeasureTheory.Measure.count := by
    apply lintegral_mono; intro x
    exact ENNReal.rpow_le_rpow (Tsup_le_tsum g s x) (by norm_num)
  have hinner : ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)/4) *
        (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count
      ≤ (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m)) * G := by
    calc ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)/4) *
          (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count
        = ∑' m : ℕ, ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)/4) *
            (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_tsum (fun m => AEMeasurable.pow_const
            (Measurable.aemeasurable (measurable_of_countable _)) 2)
      _ ≤ ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m) * G :=
          ENNReal.tsum_le_tsum (fun m => ?_)
      _ = (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m)) * G := by
          rw [ENNReal.tsum_mul_right]
    calc ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)/4) *
          (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ) ∂MeasureTheory.Measure.count
        = ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) *
            (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_congr (fun x => by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)])
      _ = ((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) *
            ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ)
              ∂MeasureTheory.Measure.count :=
          lintegral_const_mul _ (Measurable.pow_const (measurable_of_countable _) 2)
      _ ≤ ((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * (K m * G) := by
          gcongr
          exact hblk m
      _ = (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m) * G := by rw [mul_assoc]
  refine le_trans h1 ?_
  calc ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
          (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)/4) *
            (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => block_cauchy (fun m => ⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
          ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)/4) *
            (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_const_mul _ (measurable_of_countable _)
    _ ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
          ((∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m)) * G) := by
        gcongr
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ)) *
          (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) * K m)) * G := by rw [mul_assoc]

/-- `∑_m 2^{-m/2} (m+2)^4` converges (the bookkeeping constant of the assembly). -/
lemma summable_half_rpow_mul_quartic :
    Summable (fun m : ℕ => (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^4) := by
  have hr : ‖(2:ℝ)^(-(1:ℝ)/2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpoly : ∀ m : ℕ, ((m:ℝ)+2)^4 ≤ 81 * ((m:ℝ)^4 + 1) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · have h1 : ((m:ℝ)+2) ≤ 3*(m:ℝ) := by
        have h2 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
        linarith
      have h2 : (0:ℝ) ≤ (m:ℝ)+2 := by positivity
      calc ((m:ℝ)+2)^4 ≤ (3*(m:ℝ))^4 := pow_le_pow_left₀ h2 h1 4
        _ = 81*(m:ℝ)^4 := by ring
        _ ≤ 81*((m:ℝ)^4+1) := by nlinarith [pow_nonneg (show (0:ℝ) ≤ (m:ℝ) by positivity) 4]
  have hgen : Summable (fun m : ℕ =>
      ((m:ℝ)+2)^4 * ((2:ℝ)^(-(1:ℝ)/2))^m) := by
    have h1 : Summable (fun m : ℕ => (m:ℝ)^4 * ((2:ℝ)^(-(1:ℝ)/2))^m) :=
      summable_pow_mul_geometric_of_norm_lt_one 4 hr
    have h2 : Summable (fun m : ℕ => ((2:ℝ)^(-(1:ℝ)/2))^m) :=
      summable_geometric_of_norm_lt_one hr
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((h1.mul_left 81).add (h2.mul_left 81))
    have h4 := mul_le_mul_of_nonneg_right (hpoly m)
      (by positivity : (0:ℝ) ≤ ((2:ℝ)^(-(1:ℝ)/2))^m)
    calc (((m:ℝ)+2)^4) * ((2:ℝ)^(-(1:ℝ)/2))^m
        ≤ (81 * ((m:ℝ)^4 + 1)) * ((2:ℝ)^(-(1:ℝ)/2))^m := h4
      _ = 81 * (((m:ℝ)^4) * ((2:ℝ)^(-(1:ℝ)/2))^m)
            + 81 * (((2:ℝ)^(-(1:ℝ)/2))^m) := by ring
  refine hgen.congr (fun m => ?_)
  rw [mul_comm]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast; ring

/-- Elementary `rpow` algebra: the scaled block weight is the geometric weight times `(m+2)^4`. -/
lemma two_rpow_sq_C (C : ℝ) (m : ℕ) :
    (2:ℝ)^((m:ℝ)/2) * (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2
      = C^2 * ((2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^4) := by
  have h1 : ((2:ℝ)^(-(m:ℝ)/2))^2 = (2:ℝ)^(-(m:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; push_cast; ring
  rw [mul_pow, mul_pow, h1]
  rw [show (((m:ℝ)+2)^2)^2 = ((m:ℝ)+2)^4 by ring]
  rw [show (2:ℝ)^((m:ℝ)/2) * (C^2 * (2:ℝ)^(-(m:ℝ)) * ((m:ℝ)+2)^4)
      = C^2 * ((2:ℝ)^((m:ℝ)/2) * (2:ℝ)^(-(m:ℝ))) * ((m:ℝ)+2)^4 by ring]
  rw [show (2:ℝ)^((m:ℝ)/2) * (2:ℝ)^(-(m:ℝ)) = (2:ℝ)^(-(m:ℝ)/2) by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1; ring]
  ring

/-- The scaled block constant `∑_m 2^{m/2} K m` is finite. -/
lemma tsum_scaled_K_lt_top (C : ℝ) (hC : 0 ≤ C) :
    (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) *
      ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2) < ∞ := by
  have h1 : ∀ m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ)
      = ENNReal.ofReal ((2:ℝ)^((m:ℝ)/2)) := by
    intro m
    have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
    rw [h2, ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_pos (x := 2) (show (0:ℝ) < 2 by norm_num)]
    congr 1
    ring
  simp only [h1]
  rw [show (fun m : ℕ => ENNReal.ofReal ((2:ℝ)^((m:ℝ)/2)) *
      ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2)
      = fun m : ℕ => ENNReal.ofReal (C^2 * ((2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^4)) from by
    funext m
    rw [← ENNReal.ofReal_pow (by
        have h : (0:ℝ) ≤ (2:ℝ)^(-(m:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
        positivity) 2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    congr 1
    exact two_rpow_sq_C C m]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by
    have h : (0:ℝ) ≤ (2:ℝ)^(-(m:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
    positivity) (summable_half_rpow_mul_quartic.mul_left (C^2))]
  exact ENNReal.ofReal_lt_top

/-- **Assembly of the target from the per-`q`-block maximal estimate** (Bourgain's Lemma 4.1 for
each dyadic `q`-block, i.e. `majorArcModel_block_maximal_l2`). -/
theorem quadratic_kernel_model_maximal_l2_of_block
    (hm : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (∑ q ∈ (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ)^((1:ℝ)/4)))).filter
                (fun q => Nat.log 2 q = m),
                majorArcBlock ((1:ℝ)/4) (2^k) θ q)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (x:ℂ) * (θ:ℂ)))‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2 *
          ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hblk⟩ := hm
  set W : ℝ≥0∞ := ∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)/4))^(2:ℝ) with hW
  set D : ℝ≥0∞ := ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)/4))^(2:ℝ) *
    ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2) with hD
  have hWfin : W < ∞ := by rw [hW]; exact tsum_block_weight_lt_top
  have hDfin : D < ∞ := by rw [hD]; exact tsum_scaled_K_lt_top C hCpos.le
  have hWD : W * D ≠ ∞ := ne_top_of_lt (ENNReal.mul_lt_top hWfin hDfin)
  refine ⟨Real.sqrt ((W * D).toReal) + 1, by positivity, ?_⟩
  intro g s hgs
  have hA : W * D ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := by
    have h5 : (W * D).toReal ≤ (Real.sqrt ((W * D).toReal) + 1)^2 := by
      rw [add_sq, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (W * D).toReal)]
      linarith [Real.sqrt_nonneg ((W * D).toReal)]
    calc W * D = ENNReal.ofReal ((W * D).toReal) := (ENNReal.ofReal_toReal hWD).symm
      _ ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := ENNReal.ofReal_le_ofReal h5
  have key : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖TkMax g s k m‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ W * D * (∫⁻ m : ℤ, ‖g m‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
    have hK : ∀ m : ℕ,
        ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
          ≤ (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2)
              * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
      intro m
      show ∫⁻ x : ℤ, (⨆ k : ℕ, ‖(∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (∑ q ∈ (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ)^((1:ℝ)/4)))).filter
                (fun q => Nat.log 2 q = m),
                majorArcBlock ((1:ℝ)/4) (2^k) θ q)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (x:ℂ) * (θ:ℂ))))‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count ≤ _
      exact hblk m g s hgs
    simpa only [hW, hD] using lintegral_Tsup_sq_le g s
      (fun m => ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2)
      (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) hK
  refine le_trans key ?_
  exact mul_le_mul_of_nonneg_right hA (by positivity)

/-! ### Fixed-multiplier absorption of a maximal estimate (Bourgain §6, disjoint summands)

The mechanism by which the Gauss-sum weights of the major-arc model are absorbed.
Bourgain (1989), §6 writes the multiplier as a *fixed* multiplier times the indicator of the
`2^{-s}`-neighbourhood of the frequency set `{a/q}`: the summands of the fixed multiplier are
disjointly supported, so its sup-norm is the largest of the Gauss-sum weights `|S(ϑ)|` (bounded
by `C·2^{-m/2}`, cf. `norm_modelWeight_le` above), and `𝓕⁻¹[Ψ*_N f] = (Ψ_k f) * χ̌_{R_s}`, so the
*unweighted* sharp-indicator maximal estimate (Bourgain's Lemma 4.1) applies to `Ψ_k f`.
The lemma below is exactly that fixed-multiplier step.  Note that
`maximal_l2_of_summable_multiplier_family` does *not* apply here: the pointwise bounds for the
model's dyadic blocks do not decay along the scale.

-/

/-- The trigonometric polynomial of finitely supported coefficients never exceeds the `ℓ¹`-norm
of the coefficients. -/
private lemma enorm_eq_ofReal_norm_c (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]; rfl

lemma norm_trigPoly_le (g : ℤ → ℂ) (s : Finset ℤ) (θ : ℝ) :
    ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ ≤ ∑ j ∈ s, ‖g j‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul]
  have h : ‖Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ = 1 := by
    have h2 : 2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ)
        = (((2*Real.pi*(j:ℝ)*(θ:ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h2, Complex.norm_exp_ofReal_mul_I]
  rw [h, mul_one]

/-- **Fixed-multiplier transfer of a maximal estimate.** -/
theorem maximal_l2_of_fixed_multiplier
    (χ : ℕ → ℝ → ℂ) (Ψ : ℝ → ℂ) (B cap : ℝ) (hB : 0 ≤ B) (hcap : 0 ≤ cap)
    (hmax : ∀ (Q : ℝ → ℂ), MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, χ k θ * Q θ *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ))
    (hΨm : Measurable Ψ) (hΨbd : ∀ θ, ‖Ψ θ‖ ≤ cap) :
    ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, (Ψ θ * χ k θ) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (B ^ 2 * cap ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by
  intro g s hg
  set P : ℝ → ℂ := fun θ => ∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ)) with hPdef
  set Q : ℝ → ℂ := fun θ => Ψ θ * P θ with hQdef
  have hPmeas : Measurable P := by
    rw [hPdef]; fun_prop
  have hQle' : ∀ θ, ‖Q θ‖ ≤ cap * ‖P θ‖ := by
    intro θ
    rw [hQdef]; simp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hΨbd θ) (norm_nonneg _)
  have hQle : ∀ θ, ‖Q θ‖ ≤ cap * (∑ j ∈ s, ‖g j‖) := fun θ =>
    le_trans (hQle' θ) (mul_le_mul_of_nonneg_left (norm_trigPoly_le g s θ) hcap)
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩
  have hQmem : MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound ((hΨm.mul hPmeas).aestronglyMeasurable) _ (Eventually.of_forall hQle)
  -- (i) rewrite the family through `Q`
  have hpt : ∀ (k : ℕ) (θ : ℝ) (e : ℂ), (Ψ θ * χ k θ) * P θ * e = χ k θ * Q θ * e := by
    intro k θ e; rw [hQdef]; simp only; ring
  have hstep : (∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, (Ψ θ * χ k θ) * P θ *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ) ∂Measure.count)
      = ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, χ k θ * Q θ *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ) ∂Measure.count := by
    refine lintegral_congr (fun m => ?_)
    congr 1
    refine iSup_congr (fun k => ?_)
    rw [intervalIntegral.integral_congr (fun θ _ => hpt k θ _)]
  rw [hstep]
  refine le_trans (hmax Q hQmem) ?_
  -- (ii) the `Q`-norm bound
  have hQb : ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (cap^2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖ₑ ^ (2:ℝ) := by
    have hpt2 : ∀ θ, ‖Q θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (cap^2) * ‖P θ‖ₑ ^ (2:ℝ) := by
      intro θ
      have h1 : ‖Q θ‖ₑ ≤ ENNReal.ofReal cap * ‖P θ‖ₑ := by
        rw [enorm_eq_ofReal_norm_c, enorm_eq_ofReal_norm_c, ← ENNReal.ofReal_mul hcap]
        exact ENNReal.ofReal_le_ofReal (hQle' θ)
      have h2 := ENNReal.rpow_le_rpow h1 (by norm_num : (0:ℝ) ≤ 2)
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at h2
      refine le_trans h2 (le_of_eq ?_)
      rw [ENNReal.rpow_two, ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul hcap]
      ring_nf
    calc ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (cap^2) * ‖P θ‖ₑ ^ (2:ℝ) :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal (cap^2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖ₑ ^ (2:ℝ) := by
          rw [lintegral_const_mul _ (hPmeas.enorm.pow_const 2)]
  -- (iii) the `P`-norm is the `ℓ²`-norm of `g`
  have hint2 : (∫ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖^2) = ∑ j ∈ s, ‖g j‖^2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [show (fun θ : ℝ => ‖P θ‖^2)
        = (fun θ : ℝ => ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖^2) from by
      funext θ; rw [hPdef]]
    rw [Commons.Analysis.Fourier.plancherel_trig_polynomial s g]
  have hPnorm : ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal (∑ j ∈ s, ‖g j‖^2) := by
    have hpt3 : ∀ θ, ‖P θ‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖P θ‖^2) := by
      intro θ
      rw [enorm_eq_ofReal_norm_c]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num) |>.trans
        (by rw [Real.rpow_two])
    have hint : Integrable (fun θ : ℝ => ‖P θ‖^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      Integrable.of_bound ((hPmeas.norm.pow_const 2).aestronglyMeasurable) _
        (Eventually.of_forall (fun θ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (by positivity) (norm_trigPoly_le g s θ) 2))
    calc ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖ₑ ^ (2:ℝ)
        = ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (‖P θ‖^2) := lintegral_congr hpt3
      _ = ENNReal.ofReal (∫ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖^2) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun θ => by positivity))).symm
      _ = ENNReal.ofReal (∑ j ∈ s, ‖g j‖^2) := by
          rw [hint2]
  -- (iv) the `ℓ²`-norm of `g` against the counting measure
  have hgl : ENNReal.ofReal (∑ j ∈ s, ‖g j‖^2) ≤ ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by
    rw [lintegral_count]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum s)
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [enorm_eq_ofReal_norm_c, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
  calc ENNReal.ofReal (B ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (B ^ 2) *
          (ENNReal.ofReal (cap^2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖P θ‖ₑ ^ (2:ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (B ^ 2) *
          (ENNReal.ofReal (cap^2) * ENNReal.ofReal (∑ j ∈ s, ‖g j‖^2)) := by rw [hPnorm]
    _ ≤ ENNReal.ofReal (B ^ 2) *
          (ENNReal.ofReal (cap^2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count) := by
        gcongr
    _ = ENNReal.ofReal (B ^ 2 * cap ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ B^2)]

lemma ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b)^2 ≤ 4 * a^2 + 4 * b^2 := by
  have h1 : a + b ≤ 2 * (a ⊔ b) := by rw [two_mul]; exact add_le_add le_sup_left le_sup_right
  have h2 : (a + b)^2 ≤ (2 * (a ⊔ b))^2 := pow_le_pow_left' h1 2
  rw [mul_pow] at h2
  have h3 : (2:ℝ≥0∞)^2 = 4 := by norm_num
  rw [h3] at h2
  have h4 : (a ⊔ b)^2 ≤ a^2 + b^2 := by
    rcases le_total a b with h | h
    · rw [sup_eq_right.mpr h]; exact le_add_self
    · rw [sup_eq_left.mpr h]; exact le_self_add
  calc (a+b)^2 ≤ 4 * (a⊔b)^2 := h2
    _ ≤ 4 * (a^2 + b^2) := by gcongr
    _ = 4*a^2 + 4*b^2 := by rw [mul_add]

/-- `(a+b)² ≤ 4a²+4b²` for `ℝ≥0∞` (`rpow` form). -/
lemma ennreal_add_rpow_two_le (a b : ℝ≥0∞) :
    (a + b) ^ (2:ℝ) ≤ 4 * a ^ (2:ℝ) + 4 * b ^ (2:ℝ) := by
  simpa only [ENNReal.rpow_two] using ennreal_add_sq_le a b

/-- A measurable function on `ℝ` bounded by a constant is interval-integrable on `[0,1]`. -/
lemma intervalIntegrable_of_measurable_bound {f : ℝ → ℂ} (hm : Measurable f) (C : ℝ)
    (hb : ∀ θ, ‖f θ‖ ≤ C) : IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?hfin hm.aestronglyMeasurable C (Eventually.of_forall hb)
  rw [Real.volume_uIoc]
  simp

private lemma norm_quadraticKernel_le_one (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) :
    ‖quadraticKernel N θ‖ ≤ 1 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  unfold quadraticKernel
  rw [norm_mul]
  have h1 : ‖(((N:ℝ))⁻¹ : ℂ)‖ = (N:ℝ)⁻¹ := by
    rw [show ((((N:ℝ))⁻¹ : ℂ)) = ((N:ℝ)⁻¹ : ℝ) by norm_cast,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h2 : ‖∑ n ∈ Finset.range N,
      Complex.exp (2*Real.pi*Complex.I*((θ * (n:ℝ)^2 : ℝ) : ℂ))‖ ≤ (N:ℝ) := by
    calc ‖∑ n ∈ Finset.range N,
        Complex.exp (2*Real.pi*Complex.I*((θ * (n:ℝ)^2 : ℝ) : ℂ))‖
        ≤ ∑ n ∈ Finset.range N, (1:ℝ) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun n _ => ?_))
          rw [show (2*Real.pi*Complex.I*((θ * (n:ℝ)^2 : ℝ) : ℂ))
              = (((2*Real.pi*θ*(n:ℝ)^2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
      _ = (N:ℝ) := by simp
  rw [h1]
  calc (N:ℝ)⁻¹ * _ ≤ (N:ℝ)⁻¹ * (N:ℝ) := by gcongr
    _ = 1 := by field_simp

/-- Crude bound on the major-arc model for `N ≤ 2`. -/
private lemma norm_majorArcModel_le_five (N : ℕ) (hN : N ≤ 2) (α : ℝ) :
    ‖majorArcModel ((1:ℝ)/4) N α‖ ≤ 5 := by
  have hlt : (N:ℝ) ^ ((1:ℝ)/4) < (2:ℝ) := by
    have h1 : (N:ℝ) ^ ((1:ℝ)/4) ≤ (2:ℝ) ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by norm_num)
    have h3 : (2:ℝ) ^ ((1:ℝ)/4) < (2:ℝ) := by
      have := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num)
        (by norm_num : (1:ℝ)/4 < 1)
      simpa using this
    linarith
  have hfl : Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ≤ 1 := by
    have h := (Nat.floor_lt' (a := (N:ℝ) ^ ((1:ℝ)/4)) (n := 2) (by norm_num)).mpr hlt
    omega
  rw [majorArcModel]
  have hsub : Finset.Icc (1:ℕ) (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))) ⊆ Finset.Icc (1:ℕ) 1 := by
    intro q hq
    rw [Finset.mem_Icc] at hq ⊢
    exact ⟨hq.1, by omega⟩
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ q ∈ Finset.Icc (1:ℕ) (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
        ‖majorArcBlock ((1:ℝ)/4) N α q‖
      ≤ ∑ q ∈ Finset.Icc (1:ℕ) (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))), 5 * (q:ℝ) :=
        Finset.sum_le_sum (fun q _ => norm_majorArcBlock_le ((1:ℝ)/4) N q α)
    _ ≤ ∑ q ∈ Finset.Icc (1:ℕ) 1, 5 * (q:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = 5 := by norm_num

/-- **Pointwise split of the model maximal against the true quadratic Weyl kernel.** -/
lemma TkMax_le_kernel_add_error (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (m : ℤ) :
    ‖TkMax g s k m‖ₑ ≤
      ‖∫ θ in (0:ℝ)..1, (starRingEnd ℂ (quadraticKernel (2^k) θ)) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ
    + ‖∫ θ in (0:ℝ)..1,
          (starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ)) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ := by
  set P : ℝ → ℂ := fun θ => ∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ)) with hP
  set E : ℝ → ℂ := fun θ => Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ))) with hE
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hKc : Continuous (fun θ : ℝ => starRingEnd ℂ (quadraticKernel (2^k) θ)) :=
    Complex.continuous_conj.comp (continuous_quadraticKernel _)
  have hKm : Measurable (fun θ : ℝ => starRingEnd ℂ (quadraticKernel (2^k) θ)) := hKc.measurable
  have hMm : Measurable (fun θ : ℝ => starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)) :=
    Complex.continuous_conj.measurable.comp (measurable_majorArcModel _ _)
  have hid : ∀ θ, (starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)) * P θ * E θ
      = (starRingEnd ℂ (quadraticKernel (2^k) θ)) * P θ * E θ
        - (starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ)) * P θ * E θ := by
    intro θ
    have hconj : starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)
        = starRingEnd ℂ (quadraticKernel (2^k) θ)
          - starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ) := by
      rw [map_sub]; ring
    rw [hconj]; ring
  have hint1 : IntervalIntegrable
      (fun θ => (starRingEnd ℂ (quadraticKernel (2^k) θ)) * P θ * E θ) volume 0 1 :=
    ((hKc.mul hPc).mul hEc).intervalIntegrable _ _
  have hbound : ∀ θ, ‖(starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ)) * P θ * E θ‖
      ≤ (1 + 5 * (∑ q ∈ Finset.Icc (1:ℕ) (Nat.floor (((2^k:ℕ):ℝ) ^ ((1:ℝ)/4))), (q:ℝ))) * (∑ j ∈ s, ‖g j‖) := by
    intro θ
    have h1 : ‖starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ)‖
        ≤ 1 + 5 * (∑ q ∈ Finset.Icc (1:ℕ) (Nat.floor (((2^k:ℕ):ℝ) ^ ((1:ℝ)/4))), (q:ℝ)) := by
      rw [Complex.norm_conj]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
      · exact norm_quadraticKernel_le_one _ (Nat.one_le_two_pow (n := k)) θ
      · exact norm_majorArcModel_le ((1:ℝ)/4) (2^k) θ
    have hPbd : ‖P θ‖ ≤ ∑ j ∈ s, ‖g j‖ := by rw [hP]; exact norm_trigPoly_le g s θ
    have hE1 : ‖E θ‖ = 1 := by rw [hE, norm_exp_pure_imag]
    rw [norm_mul, norm_mul, hE1, mul_one]
    exact mul_le_mul h1 hPbd (norm_nonneg _) (by positivity)
  have hint2 : IntervalIntegrable
      (fun θ => (starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ)) * P θ * E θ)
      volume 0 1 := by
    refine intervalIntegrable_of_measurable_bound ?_ _ hbound
    exact ((Complex.continuous_conj.measurable.comp ((measurable_quadraticKernel _).sub
      (measurable_majorArcModel _ _))).mul hPc.measurable).mul hEc.measurable
  rw [TkMax]
  conv_lhs => rw [show (fun θ : ℝ => (starRingEnd ℂ (majorArcModel ((1:ℝ)/4) (2^k) θ)) * P θ * E θ)
      = fun θ : ℝ => (starRingEnd ℂ (quadraticKernel (2^k) θ)) * P θ * E θ
        - (starRingEnd ℂ (quadraticKernel (2^k) θ - majorArcModel ((1:ℝ)/4) (2^k) θ)) * P θ * E θ
      from by funext θ; exact hid θ]
  rw [intervalIntegral.integral_sub hint1 hint2]
  exact enorm_sub_le




/-- **The model maximal follows from the maximal estimate for the true quadratic Weyl kernel.**
Bourgain's §6: the model `majorArcModel (1/4) (2^k)` differs from the true kernel `quadraticKernel
(2^k)` by a sup-norm error `O(2^{-ck})` (commons: `quadratic_kernel_major_arc_model`), hence the
dyadic maximal of the model is dominated by that of the kernel plus a summable error family. -/
theorem quadratic_kernel_model_maximal_l2_of_kernel
    (hK : ∃ B : ℝ, 0 < B ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, (starRingEnd ℂ (quadraticKernel (2^k) θ)) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨B, hBpos, hKb⟩ := hK
  obtain ⟨cm, Cm, hcm, hCm, hErr⟩ := quadratic_kernel_major_arc_model
  set Cm' : ℝ := max Cm (6 * (2:ℝ) ^ cm) with hCm'def
  have hCm'pos : 0 < Cm' := lt_of_lt_of_le (by positivity) (le_max_right Cm (6 * (2:ℝ) ^ cm))
  set err : ℕ → ℝ := fun k => Cm' * ((((2:ℝ) ^ cm)⁻¹) ^ k) with herrdef
  have herrnn : ∀ k, 0 ≤ err k := fun k => by
    rw [herrdef]
    exact mul_nonneg hCm'pos.le
      (pow_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) cm)) _)
  have hpoweq : ∀ k : ℕ, (((2:ℝ) ^ k) ^ cm)⁻¹ = (((2:ℝ) ^ cm)⁻¹) ^ k := by
    intro k
    rw [inv_pow, ← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_natCast ((2:ℝ)^cm) k,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; ring
  have herrsum : Summable err := by
    have h1 : (1:ℝ) < (2:ℝ) ^ cm := Real.one_lt_rpow (by norm_num) hcm
    have hr : ‖((2:ℝ) ^ cm)⁻¹‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) cm))]
      exact inv_lt_one_of_one_lt₀ h1
    simpa only [herrdef] using (summable_geometric_of_norm_lt_one hr).mul_left Cm'
  have herr_ge6 : ∀ k : ℕ, k ≤ 1 → (6:ℝ) ≤ err k := by
    intro k hk
    rw [herrdef]
    change (6:ℝ) ≤ Cm' * (((2:ℝ) ^ cm)⁻¹) ^ k
    interval_cases k
    · rw [pow_zero, mul_one]
      calc (6:ℝ) ≤ 6 * (2:ℝ) ^ cm := by
            have := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) hcm.le
            nlinarith
        _ ≤ Cm' := le_max_right _ _
    · rw [pow_one]
      calc (6:ℝ) = 6 * (2:ℝ) ^ cm * ((2:ℝ) ^ cm)⁻¹ := by field_simp
        _ ≤ Cm' * ((2:ℝ) ^ cm)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hψbound : ∀ (k : ℕ) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      ‖starRingEnd ℂ (quadraticKernel (2 ^ k) θ - majorArcModel ((1:ℝ)/4) (2 ^ k) θ)‖ ≤ err k := by
    intro k θ h0 h1
    rw [Complex.norm_conj]
    rcases lt_or_ge k 2 with hk | hk
    · have hq : ‖quadraticKernel (2 ^ k) θ‖ ≤ 1 :=
        norm_quadraticKernel_le_one _ (Nat.one_le_two_pow (n := k)) θ
      have hm : ‖majorArcModel ((1:ℝ)/4) (2 ^ k) θ‖ ≤ 5 := by
        refine norm_majorArcModel_le_five (2 ^ k) ?_ θ
        interval_cases k <;> norm_num
      have h6 : (6:ℝ) ≤ err k := herr_ge6 k (by omega)
      have htri := norm_sub_le (quadraticKernel (2 ^ k) θ) (majorArcModel ((1:ℝ)/4) (2 ^ k) θ)
      linarith
    · have hN3 : 3 ≤ 2 ^ k :=
        le_trans (by norm_num : (3:ℕ) ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hk)
      refine le_trans (hErr (2 ^ k) hN3 θ h0 h1) ?_
      rw [herrdef, Nat.cast_pow, Nat.cast_ofNat, hpoweq k]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (pow_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) cm)) k)
  set S : ℝ := ∑' k : ℕ, err k with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg herrnn
  refine ⟨2 * B + 2 * S, by positivity, ?_⟩
  intro g s hg
  set G : ℝ≥0∞ := ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hGdef
  -- the indicator extension of the error multiplier, bounded globally by `err`
  set Ψ : ℕ → ℝ → ℂ := fun k θ => if θ ∈ Set.Icc (0:ℝ) 1 then
      starRingEnd ℂ (quadraticKernel (2 ^ k) θ - majorArcModel ((1:ℝ)/4) (2 ^ k) θ) else 0 with hΨdef
  have hconjm : Measurable (fun z : ℂ => starRingEnd ℂ z) := Complex.continuous_conj.measurable
  have hΨmeas : ∀ k, Measurable (Ψ k) := by
    intro k
    rw [hΨdef]
    exact Measurable.ite measurableSet_Icc
      (hconjm.comp ((measurable_quadraticKernel _).sub (measurable_majorArcModel _ _)))
      measurable_const
  have hΨbd : ∀ k θ, ‖Ψ k θ‖ ≤ err k := by
    intro k θ
    rw [hΨdef]
    change ‖(if θ ∈ Set.Icc (0:ℝ) 1 then
      starRingEnd ℂ (quadraticKernel (2 ^ k) θ - majorArcModel ((1:ℝ)/4) (2 ^ k) θ) else 0)‖ ≤ err k
    by_cases hθ : θ ∈ Set.Icc (0:ℝ) 1
    · rw [if_pos hθ]; exact hψbound k θ hθ.1 hθ.2
    · rw [if_neg hθ, norm_zero]; exact herrnn k
  have herr2 := Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family
    Ψ err herrnn hΨmeas hΨbd herrsum g s hg
  set FA : ℤ → ℝ≥0∞ := fun m => (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
      (starRingEnd ℂ (quadraticKernel (2 ^ k) θ)) *
      (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
      Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) with hFAdef
  set FB : ℤ → ℝ≥0∞ := fun m => (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1, Ψ k θ *
      (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
      Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) with hFBdef
  have hquadA : ∫⁻ m : ℤ, (FA m) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B ^ 2) * G := by
    rw [hFAdef, hGdef]; exact hKb g s hg
  have herrA : ∫⁻ m : ℤ, (FB m) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (S ^ 2) * G := by
    rw [hFBdef, hGdef, hSdef]
    exact herr2
  -- pointwise split, using the `Icc`-extension to transfer the error integral
  have key : ∀ m : ℤ, (⨆ k : ℕ, ‖TkMax g s k m‖ₑ) ≤ FA m + FB m := by
    intro m
    rw [hFAdef, hFBdef]
    refine iSup_le (fun k => le_trans (TkMax_le_kernel_add_error g s k m) (add_le_add ?_ ?_))
    · exact le_iSup (fun k : ℕ => ‖∫ θ in (0:ℝ)..1,
          (starRingEnd ℂ (quadraticKernel (2 ^ k) θ)) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) k
    · refine le_trans (le_of_eq ?_) (le_iSup (fun k : ℕ => ‖∫ θ in (0:ℝ)..1, Ψ k θ *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) k)
      congr 1
      refine intervalIntegral.integral_congr (fun θ hθ => ?_)
      simp only [hΨdef]
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
      rw [if_pos hθ]
  have h4B : 4 * ENNReal.ofReal (B ^ 2) = ENNReal.ofReal (4 * B ^ 2) := by
    rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num]
    exact (ENNReal.ofReal_mul (p := 4) (q := B ^ 2) (by norm_num : (0:ℝ) ≤ 4)).symm
  have h4S : 4 * ENNReal.ofReal (S ^ 2) = ENNReal.ofReal (4 * S ^ 2) := by
    rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num]
    exact (ENNReal.ofReal_mul (p := 4) (q := S ^ 2) (by norm_num : (0:ℝ) ≤ 4)).symm
  have hfin : 4 * ENNReal.ofReal (B ^ 2) + 4 * ENNReal.ofReal (S ^ 2)
      ≤ ENNReal.ofReal ((2 * B + 2 * S) ^ 2) := by
    rw [h4B, h4S,
      ← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 4 * B ^ 2)
        (by positivity : (0:ℝ) ≤ 4 * S ^ 2)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [hBpos, hSnn]
  have hfinal : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖TkMax g s k m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((2 * B + 2 * S) ^ 2) * G := by
    calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖TkMax g s k m‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
        ≤ ∫⁻ m : ℤ, (FA m + FB m) ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_mono (fun m => ENNReal.rpow_le_rpow (key m) (by norm_num))
      _ ≤ ∫⁻ m : ℤ, (4 * (FA m) ^ (2:ℝ) + 4 * (FB m) ^ (2:ℝ)) ∂MeasureTheory.Measure.count :=
          lintegral_mono (fun m => ennreal_add_rpow_two_le (FA m) (FB m))
      _ = 4 * ∫⁻ m : ℤ, (FA m) ^ (2:ℝ) ∂MeasureTheory.Measure.count
          + 4 * ∫⁻ m : ℤ, (FB m) ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
          rw [lintegral_add_left (measurable_of_countable _),
            lintegral_const_mul _ (measurable_of_countable _),
            lintegral_const_mul _ (measurable_of_countable _)]
      _ ≤ 4 * (ENNReal.ofReal (B ^ 2) * G) + 4 * (ENNReal.ofReal (S ^ 2) * G) :=
          add_le_add (mul_le_mul_of_nonneg_left hquadA (by norm_num))
            (mul_le_mul_of_nonneg_left herrA (by norm_num))
      _ = (4 * ENNReal.ofReal (B ^ 2) + 4 * ENNReal.ofReal (S ^ 2)) * G := by
          rw [add_mul, mul_assoc 4 (ENNReal.ofReal (B ^ 2)) G,
            mul_assoc 4 (ENNReal.ofReal (S ^ 2)) G]
      _ ≤ ENNReal.ofReal ((2 * B + 2 * S) ^ 2) * G :=
          mul_le_mul_of_nonneg_right hfin zero_le
  simpa only [hGdef, TkMax] using hfinal

lemma norm_exp_mul_I_sub_one_le (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I) - 1‖ ≤ 2 * |y| := by
  by_cases h : |y| ≤ 1
  · have hy : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by
      simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using h
    simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      using Complex.norm_exp_sub_one_le hy
  · have h2 : ‖Complex.exp ((y : ℂ) * Complex.I) - 1‖ ≤ 2 := by
      calc ‖Complex.exp ((y : ℂ) * Complex.I) - 1‖
          ≤ ‖Complex.exp ((y : ℂ) * Complex.I)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
    linarith [abs_nonneg y]

/-- Bourgain (5.18) for the quadratic phase: the Fresnel factor differs from `1` by at most
`2π N²|β|` in the variable `x = N²β`.  (Informative only when `N²|β| ≲ 1`.) -/
theorem fresnel_integral_one_sub_le (x : ℝ) :
    ‖(∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ))) - 1‖
      ≤ 2 * Real.pi * |x| := by
  have hpt : ∀ s : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1‖
      ≤ 4 * Real.pi * |x| * s^2 := by
    intro s
    have hrw : 2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)
        = ((2 * Real.pi * x * s^2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have h := norm_exp_mul_I_sub_one_le (2 * Real.pi * x * s^2)
    rw [hrw]
    refine le_trans h (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2),
      abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (sq_nonneg s)]
    ring
  have h1 : (∫ s in (0:ℝ)..1, (1:ℂ)) = 1 := by
    rw [intervalIntegral.integral_const]; norm_num
  have hInt : IntervalIntegrable
      (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1) volume 0 1 :=
    ((Continuous.intervalIntegrable (by fun_prop : Continuous (fun s : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)))) _ _).sub
      (Continuous.intervalIntegrable continuous_const _ _))
  rw [← h1, ← intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop : Continuous (fun s : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)))) _ _)
    (Continuous.intervalIntegrable continuous_const _ _)]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)) ?_
  have hmono : (∫ s in (0:ℝ)..1, ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1‖)
      ≤ ∫ s in (0:ℝ)..1, 4 * Real.pi * |x| * s^2 :=
    intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by fun_prop : Continuous (fun s : ℝ =>
        ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1‖)) _ _)
      (Continuous.intervalIntegrable (by fun_prop : Continuous (fun s : ℝ =>
        4 * Real.pi * |x| * s^2)) _ _)
      (fun s _ => hpt s)
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const_mul]
  have hpow : (∫ s in (0:ℝ)..1, s^2) = 1/3 := by
    rw [integral_pow]; norm_num
  rw [hpow]
  nlinarith [abs_nonneg x, Real.pi_pos]



end Commons.Analysis.ExponentialSums


/-! ## Numerical bounds for the Fresnel profile along dyadic dilations

Proved in `Submission/Work/Analysis/Fresnel/fresnel_profile_dilate_bounds.lean` and stored here as
well so that they are published together with this file: the numerical heart of Bourgain (6.23). -/

open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

namespace Commons.Analysis.Fresnel

/-- The **Fresnel profile** `Φ(x) = ∫₀¹ e^{2πixs²} ds`, i.e. the profile of Bourgain's major-arc
model (`Commons.Analysis.ExponentialSums.modelTerm`). -/
noncomputable def fresnelProfile (x : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ 2 : ℝ) : ℂ))

lemma fresnelProfile_apply (x : ℝ) :
    fresnelProfile x
      = ∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ 2 : ℝ) : ℂ)) := rfl

/-- `‖Φ(x)‖ ≤ 1`, since `Φ` is an average of complex numbers of modulus `1`. -/
theorem norm_fresnelProfile_le_one (x : ℝ) : ‖fresnelProfile x‖ ≤ 1 := by
  rw [fresnelProfile]
  have hnorm : ∀ s : ℝ,
      ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ 2 : ℝ) : ℂ))‖ = 1 := by
    intro s
    have hcast : 2 * Real.pi * Complex.I * ((x * s ^ 2 : ℝ) : ℂ)
        = ((2 * Real.pi * (x * s ^ 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (show (0:ℝ) ≤ 1 by norm_num)
    (f := fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ 2 : ℝ) : ℂ)))
  refine le_trans h ?_
  simp only [hnorm]
  simp

/-- The van der Corput bound (`fresnel_integral_decay`) transported to `fresnelProfile`. -/
theorem fresnelProfile_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ |x| → ‖fresnelProfile x‖ ≤ C / Real.sqrt |x| := by
  obtain ⟨C, hC, h⟩ := Commons.Analysis.Fresnel.fresnel_integral_decay
  exact ⟨C, hC, fun x hx => by simpa only [fresnelProfile] using h x hx⟩

/-- The plateau bound (`fresnel_integral_one_sub_le`) transported to `fresnelProfile`. -/
theorem fresnelProfile_sub_one_le (x : ℝ) : ‖fresnelProfile x - 1‖ ≤ 2 * Real.pi * |x| := by
  have h := Commons.Analysis.Fresnel.fresnel_integral_one_sub_le x
  simpa only [fresnelProfile] using h

/-- **Key pointwise bound.**  There is a constant `B > 0` (with `10π` for the first alternative)
such that `‖Φ(u) - Φ(4u)‖ ≤ min (10π|u|) (B |u|^{-1/2})` for every `u`.  The first alternative is
the plateau bound applied to `u` and to `4u`; the second is the van der Corput decay
`fresnel_integral_decay`, together with the trivial bound `‖Φ‖ ≤ 1` when `|v| ≤ 1`. -/
theorem exists_norm_fresnelProfile_sub_dilate_le :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ,
      ‖fresnelProfile u - fresnelProfile (4 * u)‖
        ≤ min (10 * Real.pi * |u|) (B * (Real.sqrt |u|)⁻¹) := by
  obtain ⟨C, hC, hCd⟩ := fresnelProfile_decay
  refine ⟨max 2 (1 + 2 * C), lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun u => ?_⟩
  have hB2 : (2:ℝ) ≤ max 2 (1 + 2 * C) := le_max_left _ _
  have hBC : (1 + 2 * C) ≤ max 2 (1 + 2 * C) := le_max_right _ _
  have h10 : ‖fresnelProfile u - fresnelProfile (4 * u)‖ ≤ 10 * Real.pi * |u| := by
    have h1 : ‖fresnelProfile u - 1‖ ≤ 2 * Real.pi * |u| := fresnelProfile_sub_one_le u
    have h2 : ‖fresnelProfile (4 * u) - 1‖ ≤ 2 * Real.pi * |(4:ℝ) * u| :=
      fresnelProfile_sub_one_le (4 * u)
    have h3 : |(4:ℝ) * u| = 4 * |u| := by rw [abs_mul]; norm_num
    rw [h3] at h2
    calc ‖fresnelProfile u - fresnelProfile (4 * u)‖
        = ‖(fresnelProfile u - 1) - (fresnelProfile (4 * u) - 1)‖ := by ring_nf
      _ ≤ ‖fresnelProfile u - 1‖ + ‖fresnelProfile (4 * u) - 1‖ := norm_sub_le _ _
      _ ≤ 2 * Real.pi * |u| + 2 * Real.pi * (4 * |u|) := add_le_add h1 h2
      _ = 10 * Real.pi * |u| := by ring
  have hdecay : ∀ v : ℝ, 1 ≤ |v| → ‖fresnelProfile v‖ ≤ C * (Real.sqrt |v|)⁻¹ := by
    intro v hv
    have h := hCd v hv
    rwa [div_eq_mul_inv] at h
  have hB : ‖fresnelProfile u - fresnelProfile (4 * u)‖
      ≤ (max 2 (1 + 2 * C)) * (Real.sqrt |u|)⁻¹ := by
    have h4u : |(4:ℝ) * u| = 4 * |u| := by rw [abs_mul]; norm_num
    have hs4 : Real.sqrt |(4:ℝ) * u| = 2 * Real.sqrt |u| := by
      rw [h4u, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
        show Real.sqrt (4:ℝ) = 2 by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rcases lt_or_ge (1:ℝ) |u| with hu | hu
    · -- `1 < |u|`: both arguments are `≥ 1`
      have hu0 : 0 < |u| := by linarith
      have hsu : 0 < Real.sqrt |u| := Real.sqrt_pos.mpr hu0
      have h1 : ‖fresnelProfile u‖ ≤ C * (Real.sqrt |u|)⁻¹ := hdecay u hu.le
      have h2 : ‖fresnelProfile (4 * u)‖ ≤ C * (2 * Real.sqrt |u|)⁻¹ := by
        have h4u1 : 1 ≤ |(4:ℝ) * u| := by rw [h4u]; linarith
        have h := hdecay (4 * u) h4u1
        rwa [hs4] at h
      calc ‖fresnelProfile u - fresnelProfile (4 * u)‖
          ≤ ‖fresnelProfile u‖ + ‖fresnelProfile (4 * u)‖ := norm_sub_le _ _
        _ ≤ C * (Real.sqrt |u|)⁻¹ + C * (2 * Real.sqrt |u|)⁻¹ := add_le_add h1 h2
        _ = (3 * C / 2) * (Real.sqrt |u|)⁻¹ := by rw [mul_inv]; ring
        _ ≤ (max 2 (1 + 2 * C)) * (Real.sqrt |u|)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith [hC, hBC]) (by positivity)
    · -- `|u| ≤ 1`
      rcases eq_or_lt_of_le (abs_nonneg u) with hzero | hpos
      · -- `|u| = 0`
        have hu0 : u = 0 := abs_eq_zero.mp hzero.symm
        subst hu0
        simp [fresnelProfile]
      · -- `0 < |u| ≤ 1`
        have hsu : 0 < Real.sqrt |u| := Real.sqrt_pos.mpr hpos
        have hsu1 : Real.sqrt |u| ≤ 1 := Real.sqrt_le_one.mpr hu
        have hinv1 : (1:ℝ) ≤ (Real.sqrt |u|)⁻¹ := (one_le_inv₀ hsu).mpr hsu1
        have hnn : 0 < (Real.sqrt |u|)⁻¹ := by positivity
        rcases lt_or_ge (1:ℝ) (4 * |u|) with h4 | h4
        · have h4u1 : 1 ≤ |(4:ℝ) * u| := by rw [h4u]; linarith
          have h1 : ‖fresnelProfile u‖ ≤ 1 := norm_fresnelProfile_le_one u
          have h2 : ‖fresnelProfile (4 * u)‖ ≤ C * (2 * Real.sqrt |u|)⁻¹ := by
            have h := hdecay (4 * u) h4u1
            rwa [hs4] at h
          calc ‖fresnelProfile u - fresnelProfile (4 * u)‖
              ≤ ‖fresnelProfile u‖ + ‖fresnelProfile (4 * u)‖ := norm_sub_le _ _
            _ ≤ 1 + C * (2 * Real.sqrt |u|)⁻¹ := add_le_add h1 h2
            _ ≤ (Real.sqrt |u|)⁻¹ + (C / 2) * (Real.sqrt |u|)⁻¹ := by
                  have hCM : C * (2 * Real.sqrt |u|)⁻¹ = (C / 2) * (Real.sqrt |u|)⁻¹ := by
                    rw [mul_inv]; ring
                  rw [hCM]; linarith
            _ = (1 + C / 2) * (Real.sqrt |u|)⁻¹ := by ring
            _ ≤ (max 2 (1 + 2 * C)) * (Real.sqrt |u|)⁻¹ :=
                mul_le_mul_of_nonneg_right (by linarith [hC, hBC]) (by positivity)
        · have h1 : ‖fresnelProfile u‖ ≤ 1 := norm_fresnelProfile_le_one u
          have h2 : ‖fresnelProfile (4 * u)‖ ≤ 1 := norm_fresnelProfile_le_one (4 * u)
          calc ‖fresnelProfile u - fresnelProfile (4 * u)‖
              ≤ ‖fresnelProfile u‖ + ‖fresnelProfile (4 * u)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add h1 h2
            _ ≤ (max 2 (1 + 2 * C)) * (Real.sqrt |u|)⁻¹ := by
                have h2le : (2:ℝ) ≤ (max 2 (1 + 2 * C)) * (Real.sqrt |u|)⁻¹ := by
                  calc (2:ℝ) = 2 * 1 := by ring
                    _ ≤ (max 2 (1 + 2 * C)) * (Real.sqrt |u|)⁻¹ :=
                        mul_le_mul hB2 hinv1 (by norm_num) (by positivity)
                linarith
  exact le_min h10 hB

/-- `√(4^k · y) = 2^k √y`. -/
lemma sqrt_four_pow_mul (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt ((4:ℝ)^k * y) = 2^k * Real.sqrt y := by
  have h4 : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow, sq]
  rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- `√(4^(i+K) · y) = 2^i √(4^K · y)`. -/
lemma sqrt_four_pow_add_mul (i K : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt ((4:ℝ)^(i+K) * y) = 2^i * Real.sqrt ((4:ℝ)^K * y) := by
  rw [pow_add, mul_assoc, Real.sqrt_mul (by positivity)]
  congr 1
  have h4 : (4:ℝ)^i = ((2:ℝ)^i)^2 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow, sq]
  rw [h4, Real.sqrt_sq (by positivity)]

/-- **Summability of the geometric `min` series.**  For `A, B ≥ 0` and `y > 0`, the sequence
`k ↦ min (A·4^k y) (B·(4^k y)^{-1/2})` is summable: it is bounded by `A·4^k y` for the finitely
many `k` with `4^k y ≤ 1` and by `B·2^{-k} y^{-1/2}` afterwards. -/
lemma summable_nat_min_geometric {A B y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hy : 0 < y) :
    Summable (fun k : ℕ => min (A * ((4:ℝ)^k * y)) (B * (Real.sqrt ((4:ℝ)^k * y))⁻¹)) := by
  set f : ℕ → ℝ := fun k => min (A * ((4:ℝ)^k * y)) (B * (Real.sqrt ((4:ℝ)^k * y))⁻¹) with hf
  have hnonneg : ∀ k : ℕ, 0 ≤ f k := by
    intro k; rw [hf]; exact le_min (by positivity) (by positivity)
  have hex : ∃ k : ℕ, 1 < (4:ℝ)^k * y := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hy (show (1/4:ℝ) < 1 by norm_num)
    refine ⟨k, ?_⟩
    have hk' : ((4:ℝ)^k)⁻¹ < y := by simpa only [one_div, inv_pow] using hk
    have h4k : (0:ℝ) < (4:ℝ)^k := by positivity
    calc (1:ℝ) = (4:ℝ)^k * ((4:ℝ)^k)⁻¹ := by field_simp
      _ < (4:ℝ)^k * y := mul_lt_mul_of_pos_left hk' h4k
  set K : ℕ := Nat.find hex with hKdef
  have hKmin : ∀ k : ℕ, k < K → (4:ℝ)^k * y ≤ 1 := by
    intro k hk
    have := Nat.find_min hex (by rwa [hKdef] at hk)
    exact not_lt.mp this
  have hfg : ∀ k, f k ≤ (if k < K then A * ((4:ℝ)^k * y) else 0)
      + B * (Real.sqrt y)⁻¹ * (1/2)^k := by
    intro k
    rw [hf]
    rcases lt_or_ge k K with hk | hk
    · rw [if_pos hk]
      refine le_trans (min_le_left _ _) ?_
      have h2 : 0 ≤ B * (Real.sqrt y)⁻¹ * (1/2:ℝ)^k := by positivity
      linarith
    · rw [if_neg (not_lt.mpr hk)]
      refine le_trans (min_le_right _ _) ?_
      rw [sqrt_four_pow_mul k hy.le]
      have hEq : B * ((2:ℝ)^k * Real.sqrt y)⁻¹ = B * (Real.sqrt y)⁻¹ * (1/2:ℝ)^k := by
        rw [mul_inv]
        have h2 : ((2:ℝ)^k)⁻¹ = (1/2:ℝ)^k := by
          rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num, inv_pow]
        rw [h2]; ring
      rw [hEq]; linarith [mul_nonneg hB (inv_nonneg.mpr (Real.sqrt_nonneg y)),
        pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k]
  have hsumg : Summable (fun k : ℕ => (if k < K then A * ((4:ℝ)^k * y) else 0)
      + B * (Real.sqrt y)⁻¹ * (1/2)^k) := by
    refine Summable.add ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range K) ?_
      intro k hk
      rw [Finset.mem_range] at hk
      exact if_neg (not_lt.mpr (not_lt.mp (fun h => hk h)))
    · exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le hnonneg hfg hsumg

/-- **The geometric `min` series.**  For `A, B ≥ 0` and `y > 0`,
`∑_{k∈ℕ} min (A·4^k y) (B·(4^k y)^{-1/2}) ≤ 2A + 3B`. -/
lemma tsum_nat_min_geometric_le {A B y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hy : 0 < y) :
    (∑' k : ℕ, min (A * ((4:ℝ)^k * y)) (B * (Real.sqrt ((4:ℝ)^k * y))⁻¹))
      ≤ 2 * A + 3 * B := by
  set f : ℕ → ℝ := fun k => min (A * ((4:ℝ)^k * y)) (B * (Real.sqrt ((4:ℝ)^k * y))⁻¹) with hf
  have hsumf : Summable f := by rw [hf]; exact summable_nat_min_geometric hA hB hy
  have hnonneg : ∀ k : ℕ, 0 ≤ f k := by
    intro k; rw [hf]; exact le_min (by positivity) (by positivity)
  rcases le_or_gt 1 y with hy1 | hy1
  · -- `1 ≤ y`
    have hle : ∀ k : ℕ, f k ≤ B * (1/2)^k := by
      intro k
      rw [hf]
      refine le_trans (min_le_right _ _) ?_
      rw [sqrt_four_pow_mul k hy.le]
      have hsy : (1:ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy1
      have h2k : (0:ℝ) < (2:ℝ)^k := pow_pos (by norm_num) k
      have h1 : (2:ℝ)^k ≤ 2^k * Real.sqrt y := by nlinarith
      have hinv : ((2:ℝ)^k * Real.sqrt y)⁻¹ ≤ ((2:ℝ)^k)⁻¹ :=
        (inv_le_inv₀ (mul_pos h2k (Real.sqrt_pos.mpr hy)) h2k).mpr h1
      have h2 : ((2:ℝ)^k)⁻¹ = (1/2:ℝ)^k := by
        rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num, inv_pow]
      calc B * ((2:ℝ)^k * Real.sqrt y)⁻¹ ≤ B * ((2:ℝ)^k)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv hB
        _ = B * (1/2)^k := by rw [h2]
    have hsumg : Summable (fun k : ℕ => B * (1/2:ℝ)^k) :=
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left B
    have hcmp := Summable.tsum_le_tsum hle hsumf hsumg
    have hval : (∑' k : ℕ, B * (1/2:ℝ)^k) = 2 * B := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    rw [hval] at hcmp
    linarith
  · -- `y < 1`
    have hex : ∃ k : ℕ, 1 < (4:ℝ)^k * y := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hy (show (1/4:ℝ) < 1 by norm_num)
      refine ⟨k, ?_⟩
      have hk' : ((4:ℝ)^k)⁻¹ < y := by simpa only [one_div, inv_pow] using hk
      have h4k : (0:ℝ) < (4:ℝ)^k := by positivity
      calc (1:ℝ) = (4:ℝ)^k * ((4:ℝ)^k)⁻¹ := by field_simp
        _ < (4:ℝ)^k * y := mul_lt_mul_of_pos_left hk' h4k
    set K : ℕ := Nat.find hex with hKdef
    have hKspec : 1 < (4:ℝ)^K * y := Nat.find_spec hex
    have hKmin : ∀ k : ℕ, k < K → (4:ℝ)^k * y ≤ 1 := by
      intro k hk
      have := Nat.find_min hex (by rwa [hKdef] at hk)
      exact not_lt.mp this
    have hleK : (4:ℝ)^K * y ≤ 4 := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0] at hKspec ⊢; push_cast at hKspec ⊢; linarith
      · have h := hKmin (K - 1) (Nat.sub_lt hpos (by norm_num))
        have hpow : (4:ℝ)^K = 4 * (4:ℝ)^(K-1) := by
          conv_lhs => rw [show K = (K - 1) + 1 by omega]
          rw [pow_add]; ring
        rw [hpow]; nlinarith
    rw [← Summable.sum_add_tsum_nat_add K hsumf]
    have hfin : ∑ i ∈ Finset.range K, f i ≤ 2 * A := by
      have h1 : ∑ i ∈ Finset.range K, f i ≤ ∑ i ∈ Finset.range K, A * ((4:ℝ)^i * y) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [hf]; exact min_le_left _ _
      refine le_trans h1 ?_
      have h2 : ∑ i ∈ Finset.range K, A * ((4:ℝ)^i * y)
          = A * y * ∑ i ∈ Finset.range K, (4:ℝ)^i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h2, geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]
      have h3 : ((4:ℝ)^K - 1) / (4 - 1) ≤ (4:ℝ)^K / 3 := by
        rw [show (4:ℝ) - 1 = 3 by norm_num]
        exact div_le_div_of_nonneg_right (by linarith [pow_pos (by norm_num : (0:ℝ) < 4) K])
          (by norm_num)
      calc A * y * (((4:ℝ)^K - 1) / (4-1)) ≤ A * y * ((4:ℝ)^K / 3) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = A * ((4:ℝ)^K * y) / 3 := by ring
        _ ≤ A * 4 / 3 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hleK hA
        _ ≤ 2 * A := by linarith [hA]
    have htail : ∑' i : ℕ, f (i + K) ≤ 3 * B := by
      have hle : ∀ i : ℕ, f (i + K) ≤ B * (Real.sqrt ((4:ℝ)^K * y))⁻¹ * (1/2)^i := by
        intro i
        rw [hf]
        refine le_trans (min_le_right _ _) ?_
        rw [sqrt_four_pow_add_mul i K hy.le]
        have hEq : B * (2^i * Real.sqrt ((4:ℝ)^K * y))⁻¹
            = B * (Real.sqrt ((4:ℝ)^K * y))⁻¹ * (1/2:ℝ)^i := by
          rw [mul_inv]
          have h2 : ((2:ℝ)^i)⁻¹ = (1/2:ℝ)^i := by
            rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num, inv_pow]
          rw [h2]; ring
        rw [hEq]
      have hsumg : Summable (fun i : ℕ => B * (Real.sqrt ((4:ℝ)^K * y))⁻¹ * (1/2:ℝ)^i) :=
        (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
      have hsumf' : Summable (fun i : ℕ => f (i + K)) :=
        hsumf.comp_injective (fun a b h => Nat.add_right_cancel h)
      have hcmp := Summable.tsum_le_tsum hle hsumf' hsumg
      have hval : (∑' i : ℕ, B * (Real.sqrt ((4:ℝ)^K * y))⁻¹ * (1/2:ℝ)^i)
          = 2 * (B * (Real.sqrt ((4:ℝ)^K * y))⁻¹) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        ring
      rw [hval] at hcmp
      have h4K : (1:ℝ) < Real.sqrt ((4:ℝ)^K * y) := by
        have h3 := Real.sq_sqrt (show (0:ℝ) ≤ (4:ℝ)^K * y by positivity)
        nlinarith [Real.sqrt_nonneg ((4:ℝ)^K * y), hKspec]
      have hinv : (Real.sqrt ((4:ℝ)^K * y))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h4K
      nlinarith [hcmp, hB]
    linarith [hfin, htail]

/-- **Replacement of the profile by a sharp core.**  For `x ≠ 0`,
`∑_{k∈ℕ} ‖Φ(4^k x) − 1_{|4^k x| ≤ 1}‖ ≤ C`: the terms with `|4^k x| ≤ 1` are dominated by the
plateau bound `‖Φ(u)−1‖ ≤ 2π|u|`, and those with `|4^k x| > 1` by the van der Corput decay.  This is
the numerical content of Bourgain (6.23): the `Σ` over the dyadic scales of the difference between
the (profile) model and its sharp replacement is bounded uniformly in the point. -/
theorem exists_fresnelProfile_dilate_increment_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ≠ 0 →
      (∑' k : ℕ, ‖fresnelProfile ((4:ℝ)^k * x) - fresnelProfile ((4:ℝ)^(k+1) * x)‖) ≤ C := by
  obtain ⟨B, hBpos, hB⟩ := exists_norm_fresnelProfile_sub_dilate_le
  refine ⟨4 * (10 * Real.pi) + 3 * B + 1, by positivity, fun x hx => ?_⟩
  have hxy : (0:ℝ) < |x| := abs_pos.mpr hx
  have hpt : ∀ k : ℕ, ‖fresnelProfile ((4:ℝ)^k * x) - fresnelProfile ((4:ℝ)^(k+1) * x)‖
      ≤ min (10 * Real.pi * ((4:ℝ)^k * |x|)) (B * (Real.sqrt ((4:ℝ)^k * |x|))⁻¹) := by
    intro k
    have h := hB ((4:ℝ)^k * x)
    have h4 : (4:ℝ) * ((4:ℝ)^k * x) = (4:ℝ)^(k+1) * x := by rw [pow_succ]; ring
    rw [h4] at h
    rwa [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (4:ℝ)^k)] at h
  have hsum_min : Summable (fun k : ℕ =>
      min (10 * Real.pi * ((4:ℝ)^k * |x|)) (B * (Real.sqrt ((4:ℝ)^k * |x|))⁻¹)) :=
    summable_nat_min_geometric (by positivity) hBpos.le hxy
  have hsum_lhs : Summable (fun k : ℕ =>
      ‖fresnelProfile ((4:ℝ)^k * x) - fresnelProfile ((4:ℝ)^(k+1) * x)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hpt hsum_min
  refine le_trans (Summable.tsum_le_tsum hpt hsum_lhs hsum_min) ?_
  have hnum := tsum_nat_min_geometric_le (A := 10 * Real.pi) (B := B) (y := |x|)
    (by positivity) hBpos.le hxy
  linarith [Real.pi_pos]

/-- The majorant `K (√(|x|+1))⁻¹` for `‖Φ(x)‖`, valid for all `x` (with `K = √2 max 1 C`). -/
lemma exists_norm_fresnelProfile_le_inv_sqrt :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, ‖fresnelProfile x‖ ≤ K * (Real.sqrt (|x| + 1))⁻¹ := by
  obtain ⟨C, hC, hCd⟩ := fresnelProfile_decay
  refine ⟨Real.sqrt 2 * max 1 C, by positivity, fun x => ?_⟩
  have hK1 : (1:ℝ) ≤ max 1 C := le_max_left _ _
  have hKC : C ≤ max 1 C := le_max_right _ _
  have hKnn : (0:ℝ) < max 1 C := lt_of_lt_of_le one_pos hK1
  -- `√(|x|+1) ≤ √2 √(max |x| 1)`
  have hstep : Real.sqrt (|x| + 1) ≤ Real.sqrt 2 * Real.sqrt (max |x| 1) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    rcases le_or_gt |x| 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; nlinarith [abs_nonneg x, h]
  have hmaxpos : (0:ℝ) < max |x| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsqrtpos : (0:ℝ) < Real.sqrt (max |x| 1) := Real.sqrt_pos.mpr hmaxpos
  have hpt : ‖fresnelProfile x‖ ≤ max 1 C * (Real.sqrt (max |x| 1))⁻¹ := by
    rcases le_or_gt 1 |x| with h | h
    · have hdec := hCd x h
      rw [div_eq_mul_inv] at hdec
      rw [max_eq_left h]
      exact le_trans hdec (mul_le_mul_of_nonneg_right hKC (by positivity))
    · rw [max_eq_right h.le]
      calc ‖fresnelProfile x‖ ≤ 1 := norm_fresnelProfile_le_one x
        _ ≤ max 1 C * (Real.sqrt 1)⁻¹ := by
            rw [Real.sqrt_one, inv_one, mul_one]; exact hK1
  have hinv : (Real.sqrt (max |x| 1))⁻¹ ≤ Real.sqrt 2 * (Real.sqrt (|x| + 1))⁻¹ := by
    have h2 : (0:ℝ) < Real.sqrt (|x| + 1) := Real.sqrt_pos.mpr (by linarith [abs_nonneg x])
    have h1 : (Real.sqrt 2 * Real.sqrt (max |x| 1))⁻¹ ≤ (Real.sqrt (|x| + 1))⁻¹ :=
      (inv_le_inv₀ (by positivity) h2).mpr hstep
    have h1' : (Real.sqrt 2)⁻¹ * (Real.sqrt (max |x| 1))⁻¹ ≤ (Real.sqrt (|x| + 1))⁻¹ := by
      rwa [mul_inv] at h1
    calc (Real.sqrt (max |x| 1))⁻¹
        = Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt (max |x| 1))⁻¹) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))),
            one_mul]
      _ ≤ Real.sqrt 2 * (Real.sqrt (|x| + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left h1' (Real.sqrt_nonneg 2)
  calc ‖fresnelProfile x‖ ≤ max 1 C * (Real.sqrt (max |x| 1))⁻¹ := hpt
    _ ≤ max 1 C * (Real.sqrt 2 * (Real.sqrt (|x| + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hinv hKnn.le
    _ = (Real.sqrt 2 * max 1 C) * (Real.sqrt (|x| + 1))⁻¹ := by ring

/-- `Φ` is continuous (it is a parametric interval integral of a continuous integrand). -/
lemma continuous_fresnelProfile : Continuous fresnelProfile :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : ℝ) (s : ℝ) => Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ 2 : ℝ) : ℂ)))
    (by fun_prop) 0 1

/-- **`L¹` bound for the Fresnel profile.**  `∫_0^S ‖Φ(x)‖ dx ≤ C √(S+1)`: by
`exists_norm_fresnelProfile_le_inv_sqrt` it suffices to integrate `K (√(x+1))⁻¹`, whose
antiderivative is `2√(x+1)`.  This bounds the contribution of the major arc of radius `N^{-5/4}`
to the Fourier coefficient of the model (`N^{-2} · O(N^{3/8})`). -/
theorem exists_fresnelProfile_integral_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 ≤ S →
      ∫ x in (0:ℝ)..S, ‖fresnelProfile x‖ ≤ C * Real.sqrt (S + 1) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_fresnelProfile_le_inv_sqrt
  refine ⟨2 * K + 1, by positivity, fun S hS => ?_⟩
  have hS1 : (0:ℝ) < S + 1 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => (Real.sqrt (x + 1))⁻¹) (Set.uIcc 0 S) := by
    refine ContinuousOn.inv₀ ?_ ?_
    · exact (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le hS] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hmono : ∫ x in (0:ℝ)..S, ‖fresnelProfile x‖
      ≤ ∫ x in (0:ℝ)..S, K * (Real.sqrt (x + 1))⁻¹ := by
    refine intervalIntegral.integral_mono_on hS ?_ ?_ ?_
    · exact (continuous_fresnelProfile.norm).intervalIntegrable _ _
    · exact (hcont.const_mul K).intervalIntegrable
    · intro x hx
      have := hKb x
      rw [abs_of_nonneg hx.1] at this
      exact this
  refine le_trans hmono ?_
  have hFTC : ∫ x in (0:ℝ)..S, (Real.sqrt (x + 1))⁻¹
      = 2 * Real.sqrt (S + 1) - 2 * Real.sqrt (0 + 1) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => 2 * Real.sqrt (y + 1))
      (f' := fun x : ℝ => (Real.sqrt (x + 1))⁻¹) ?_ hcont.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hS] at hx
    have hx0 : (0:ℝ) < x + 1 := by linarith [hx.1]
    have hne : (fun y : ℝ => y + 1) x ≠ 0 := by
      simp only; linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
      simpa [add_comm] using (hasDerivAt_id x).const_add 1
    have h2 := h1.sqrt hne
    have h3 : HasDerivAt (fun y : ℝ => 2 * Real.sqrt (y + 1))
        (2 * (1 / (2 * Real.sqrt (x + 1)))) x := h2.const_mul 2
    have hgoal : 2 * (1 / (2 * Real.sqrt (x + 1))) = (Real.sqrt (x + 1))⁻¹ := by
      have hsp : Real.sqrt (x + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
      field_simp
    rw [hgoal] at h3
    exact h3
  rw [intervalIntegral.integral_const_mul, hFTC]
  simp only [zero_add, Real.sqrt_one]
  have hSq : (0:ℝ) ≤ Real.sqrt (S + 1) := Real.sqrt_nonneg _
  nlinarith [hK, hSq]


/-- **Replacement of the profile by a sharp core.**  For `x ≠ 0`,
`∑_{k∈ℕ} ‖Φ(4^k x) − 1_{|4^k x| ≤ 1}‖ ≤ C`: the terms with `|4^k x| ≤ 1` are dominated by the
plateau bound `‖Φ(u)−1‖ ≤ 2π|u|`, and those with `|4^k x| > 1` by the van der Corput decay.  This is
the numerical content of Bourgain (6.23): the `Σ` over the dyadic scales of the difference between
the (profile) model and its sharp replacement is bounded uniformly in the point. -/
theorem exists_fresnelProfile_replace_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ≠ 0 →
      (∑' k : ℕ, ‖fresnelProfile ((4:ℝ)^k * x)
        - (if |(4:ℝ)^k * x| ≤ 1 then (1:ℂ) else 0)‖) ≤ C := by
  obtain ⟨C0, hC0, hCd⟩ := fresnelProfile_decay
  refine ⟨8 * Real.pi / 3 + 2 * C0 + 1, by positivity, fun x hx => ?_⟩
  have hxy : (0:ℝ) < |x| := abs_pos.mpr hx
  have hex : ∃ k : ℕ, 1 < (4:ℝ)^k * |x| := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hxy (show (1/4:ℝ) < 1 by norm_num)
    refine ⟨k, ?_⟩
    have hk' : ((4:ℝ)^k)⁻¹ < |x| := by simpa only [one_div, inv_pow] using hk
    calc (1:ℝ) = (4:ℝ)^k * ((4:ℝ)^k)⁻¹ := by field_simp
      _ < (4:ℝ)^k * |x| := mul_lt_mul_of_pos_left hk' (pow_pos (by norm_num) k)
  set K : ℕ := Nat.find hex with hKdef
  have hKmin : ∀ k : ℕ, k < K → (4:ℝ)^k * |x| ≤ 1 := by
    intro k hk
    exact not_lt.mp (Nat.find_min hex (by rwa [hKdef] at hk))
  have hKspec : 1 < (4:ℝ)^K * |x| := by rw [hKdef]; exact Nat.find_spec hex
  have hleK : ∀ hpos : 0 < K, (4:ℝ)^K * |x| ≤ 4 := by
    intro hpos
    have h := hKmin (K - 1) (Nat.sub_lt hpos (by norm_num))
    have hpow : (4:ℝ)^K = 4 * (4:ℝ)^(K-1) := by
      conv_lhs => rw [show K = (K - 1) + 1 by omega]
      rw [pow_add]; ring
    rw [hpow]; nlinarith
  have h2K : (1:ℝ) ≤ (2:ℝ)^K * Real.sqrt |x| := by
    have h4 : (4:ℝ)^K * |x| = ((2:ℝ)^K * Real.sqrt |x|)^2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
      nlinarith [Real.sq_sqrt hxy.le]
    rw [h4] at hKspec
    have hs2 : (0:ℝ) ≤ (2:ℝ)^K * Real.sqrt |x| := by positivity
    nlinarith [hKspec, hs2, sq_nonneg ((2:ℝ)^K * Real.sqrt |x| - 1)]
  have hmono : ∀ k : ℕ, K ≤ k → 1 < (4:ℝ)^k * |x| := by
    intro k hk
    exact lt_of_lt_of_le hKspec (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hk) hxy.le)
  set f : ℕ → ℝ := fun k => ‖fresnelProfile ((4:ℝ)^k * x)
        - (if |(4:ℝ)^k * x| ≤ 1 then (1:ℂ) else 0)‖ with hf
  have hnonneg : ∀ k, 0 ≤ f k := fun k => norm_nonneg _
  have habs : ∀ k : ℕ, |(4:ℝ)^k * x| = (4:ℝ)^k * |x| := by
    intro k; rw [abs_mul, abs_of_nonneg (pow_pos (by norm_num) k).le]
  have hf_bound : ∀ k, f k ≤ (if k < K then 2 * Real.pi * ((4:ℝ)^k * |x|) else 0)
      + C0 * (Real.sqrt |x|)⁻¹ * (1/2)^k := by
    intro k
    show ‖fresnelProfile ((4:ℝ)^k * x) - (if |(4:ℝ)^k * x| ≤ 1 then (1:ℂ) else 0)‖ ≤ _
    have h2nn : (0:ℝ) ≤ C0 * (Real.sqrt |x|)⁻¹ * (1/2:ℝ)^k := by positivity
    rcases lt_or_ge k K with hk | hk
    · rw [if_pos hk, habs k, if_pos (hKmin k hk)]
      have h1 : ‖fresnelProfile ((4:ℝ)^k * x) - 1‖ ≤ 2 * Real.pi * ((4:ℝ)^k * |x|) := by
        have h := fresnelProfile_sub_one_le ((4:ℝ)^k * x)
        rwa [habs k] at h
      linarith [h1, h2nn]
    · rw [if_neg (not_lt.mpr hk), habs k, if_neg (not_le.mpr (hmono k hk))]
      have h1 : ‖fresnelProfile ((4:ℝ)^k * x) - 0‖ ≤ C0 * (Real.sqrt |x|)⁻¹ * (1/2:ℝ)^k := by
        rw [sub_zero]
        have hkd := hCd ((4:ℝ)^k * x) (by rw [habs k]; exact (hmono k hk).le)
        rw [div_eq_mul_inv, habs k, sqrt_four_pow_mul k hxy.le] at hkd
        have h4 : C0 * (2^k * Real.sqrt |x|)⁻¹ = C0 * (Real.sqrt |x|)⁻¹ * (1/2:ℝ)^k := by
          rw [mul_inv]
          have h5 : ((2:ℝ)^k)⁻¹ = (1/2:ℝ)^k := by
            rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num, inv_pow]
          rw [h5]; ring
        rwa [h4] at hkd
      simpa only [zero_add] using h1
  have hsumg : Summable (fun k : ℕ => (if k < K then 2 * Real.pi * ((4:ℝ)^k * |x|) else 0)
      + C0 * (Real.sqrt |x|)⁻¹ * (1/2)^k) := by
    refine Summable.add ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range K) ?_
      intro k hk
      rw [Finset.mem_range] at hk
      exact if_neg hk
    · exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  have hsumf : Summable f := Summable.of_nonneg_of_le hnonneg hf_bound hsumg
  rw [← Summable.sum_add_tsum_nat_add K hsumf]
  have hfin : ∑ i ∈ Finset.range K, f i ≤ 8 * Real.pi / 3 := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]; simp; positivity
    have h1 : ∑ i ∈ Finset.range K, f i
        ≤ ∑ i ∈ Finset.range K, 2 * Real.pi * ((4:ℝ)^i * |x|) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hik : i < K := Finset.mem_range.mp hi
      show ‖fresnelProfile ((4:ℝ)^i * x) - (if |(4:ℝ)^i * x| ≤ 1 then (1:ℂ) else 0)‖ ≤ _
      rw [habs i, if_pos (hKmin i hik)]
      have h := fresnelProfile_sub_one_le ((4:ℝ)^i * x)
      rwa [habs i] at h
    refine le_trans h1 ?_
    have h2 : ∑ i ∈ Finset.range K, 2 * Real.pi * ((4:ℝ)^i * |x|)
        = 2 * Real.pi * |x| * ∑ i ∈ Finset.range K, (4:ℝ)^i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h2, geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]
    have h3 : ((4:ℝ)^K - 1) / (4 - 1) ≤ (4:ℝ)^K / 3 := by
      rw [show (4:ℝ) - 1 = 3 by norm_num]
      exact div_le_div_of_nonneg_right
        (by linarith [pow_pos (by norm_num : (0:ℝ) < 4) K]) (by norm_num)
    calc 2 * Real.pi * |x| * (((4:ℝ)^K - 1) / (4-1))
        ≤ 2 * Real.pi * |x| * ((4:ℝ)^K / 3) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * Real.pi * ((4:ℝ)^K * |x|) / 3 := by ring
      _ ≤ 2 * Real.pi * 4 / 3 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          nlinarith [Real.pi_pos, hleK hpos]
      _ = 8 * Real.pi / 3 := by ring
  have htail : ∑' i : ℕ, f (i + K) ≤ 2 * C0 := by
    have hle : ∀ i : ℕ, f (i + K) ≤ C0 * ((2:ℝ)^K * Real.sqrt |x|)⁻¹ * (1/2)^i := by
      intro i
      have hKi : K ≤ i + K := Nat.le_add_left K i
      show ‖fresnelProfile ((4:ℝ)^(i+K) * x)
        - (if |(4:ℝ)^(i+K) * x| ≤ 1 then (1:ℂ) else 0)‖ ≤ _
      rw [habs (i + K), if_neg (not_le.mpr (hmono (i + K) hKi)), sub_zero]
      have h1 : ‖fresnelProfile ((4:ℝ)^(i+K) * x)‖
          ≤ C0 * (Real.sqrt ((4:ℝ)^(i+K) * |x|))⁻¹ := by
        have hkd := hCd ((4:ℝ)^(i+K) * x)
          (by rw [habs (i+K)]; exact (hmono (i+K) hKi).le)
        rwa [div_eq_mul_inv, habs (i+K)] at hkd
      rw [sqrt_four_pow_mul (i+K) hxy.le] at h1
      have h2i : (2:ℝ)^(i+K) = 2^i * 2^K := pow_add 2 i K
      rw [h2i] at h1
      refine le_trans h1 ?_
      have hEq : C0 * (2^i * 2^K * Real.sqrt |x|)⁻¹
          = C0 * ((2:ℝ)^K * Real.sqrt |x|)⁻¹ * (1/2)^i := by
        rw [mul_inv, mul_inv]
        have h4 : ((2:ℝ)^i)⁻¹ = (1/2:ℝ)^i := by
          rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num, inv_pow]
        rw [h4]; ring
      rw [hEq]
    have hsumg : Summable (fun i : ℕ => C0 * ((2:ℝ)^K * Real.sqrt |x|)⁻¹ * (1/2)^i) :=
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
    have hsumf' : Summable (fun i : ℕ => f (i + K)) :=
      hsumf.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hcmp := Summable.tsum_le_tsum hle hsumf' hsumg
    have hval : (∑' i : ℕ, C0 * ((2:ℝ)^K * Real.sqrt |x|)⁻¹ * (1/2:ℝ)^i)
        = 2 * (C0 * ((2:ℝ)^K * Real.sqrt |x|)⁻¹) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    rw [hval] at hcmp
    have h2Kpos : (0:ℝ) < (2:ℝ)^K * Real.sqrt |x| := by positivity
    have h2Kinv : ((2:ℝ)^K * Real.sqrt |x|)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ h2Kpos]; exact h2K
    nlinarith [hcmp, hC0, h2Kinv]
  linarith [hfin, htail]

/-- **Arc measure input.**  The integral over `[0,1]` of the indicator of an interval of length
`2r` is at most `2r`.  This is what turns the pointwise triangle inequality for the major-arc model
(whose support is the union of `≍ N^{1/2}` arcs of radius `N^{-5/4}`) into a bound of `O(N^{-3/4})`
for the Fourier coefficients of the model. -/
lemma interval_integral_indicator_Icc_le (c r : ℝ) (hr : 0 ≤ r) :
    ∫ θ in (0:ℝ)..1, (Set.Icc (c - r) (c + r)).indicator (fun _ => (1:ℝ)) θ ≤ 2 * r := by
  have hms : MeasurableSet (Set.Icc (c - r) (c + r)) := measurableSet_Icc
  have hsub : Set.Ioc (0:ℝ) 1 ∩ Set.Icc (c - r) (c + r) ⊆ Set.Icc (c - r) (c + r) :=
    Set.inter_subset_right
  have hfin : volume (Set.Icc (c - r) (c + r)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h1 : ∫ θ in Set.Ioc (0:ℝ) 1, (Set.Icc (c - r) (c + r)).indicator (fun _ => (1:ℝ)) θ
      = volume.real (Set.Ioc (0:ℝ) 1 ∩ Set.Icc (c - r) (c + r)) := by
    rw [← MeasureTheory.integral_indicator (μ := volume) (s := Set.Ioc (0:ℝ) 1)
      (f := (Set.Icc (c - r) (c + r)).indicator (fun _ => (1:ℝ))) measurableSet_Ioc,
      Set.indicator_indicator,
      MeasureTheory.integral_indicator_const (1:ℝ) (measurableSet_Ioc.inter hms),
      smul_eq_mul, mul_one]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), h1]
  have h2 := MeasureTheory.measureReal_mono hsub hfin
  have hvol : volume.real (Set.Icc (c - r) (c + r)) = 2 * r := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at h2
  exact h2

end Commons.Analysis.Fresnel

namespace Commons.Analysis.ExponentialSums

/-! ## Separation of the major-arc frequencies (`a/q + l`)

Proved in `Submission/Work/Analysis/ExponentialSums/majorArc_separation.lean` and stored here as
well: at most one major-arc term of the model is active at any `θ` (the arcs are disjoint). -/

/-- **Separation of the shifted rationals.**  For `a₁ < q₁`, `a₂ < q₂` with `q₁,q₂ > 0` and
distinct frequencies `a₁/q₁ + l₁ ≠ a₂/q₂ + l₂`, the distance is at least `(q₁q₂)⁻¹`. -/
theorem majorArc_shift_sep {q₁ q₂ : ℕ} {a₁ a₂ : ℕ} {l₁ l₂ : ℤ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (h : ((a₁:ℝ)/q₁ + (l₁:ℝ)) ≠ ((a₂:ℝ)/q₂ + (l₂:ℝ))) :
    ((q₁:ℝ)*(q₂:ℝ))⁻¹
      ≤ |(a₁:ℝ)/q₁ + (l₁:ℝ) - ((a₂:ℝ)/q₂ + (l₂:ℝ))| := by
  set n : ℤ := (a₁:ℤ)*q₂ - (a₂:ℤ)*q₁ + (l₁-l₂)*(q₁*q₂) with hn
  have hden : (0:ℝ) < (q₁:ℝ)*(q₂:ℝ) := by
    have : (0:ℝ) < q₁ := by exact_mod_cast hq₁
    have : (0:ℝ) < q₂ := by exact_mod_cast hq₂
    positivity
  have hrewrite : (a₁:ℝ)/q₁ + (l₁:ℝ) - ((a₂:ℝ)/q₂ + (l₂:ℝ))
      = (n:ℝ)/((q₁:ℝ)*(q₂:ℝ)) := by
    rw [hn]; push_cast
    field_simp
    ring
  have hn0 : n ≠ 0 := by
    intro hz
    have hsub : (a₁:ℝ)/q₁ + (l₁:ℝ) - ((a₂:ℝ)/q₂ + (l₂:ℝ)) = 0 := by
      rw [hrewrite, hz]; simp
    exact h (sub_eq_zero.mp hsub)
  have hn1 : (1:ℤ) ≤ |n| := Int.one_le_abs hn0
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have : ((|n| : ℤ) : ℝ) ≤ |(n:ℝ)| := by
      rw [Int.cast_abs]
    exact le_trans (by exact_mod_cast hn1) this
  rw [hrewrite, abs_div, abs_of_pos hden]
  rw [show ((q₁:ℝ)*(q₂:ℝ))⁻¹ = 1/((q₁:ℝ)*(q₂:ℝ)) by rw [one_div]]
  exact div_le_div_of_nonneg_right h1 hden.le

/-- **Fractions in lowest terms with the same value are equal.**  If `a₁/q₁ = a₂/q₂` with
`a_i < q_i > 0` and `(a_i,q_i) = 1` then `a₁ = a₂` and `q₁ = q₂`. -/
theorem frac_eq_of_coprime {q₁ q₂ a₁ a₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (h₁ : Nat.Coprime a₁ q₁) (h₂ : Nat.Coprime a₂ q₂) (ha₁ : a₁ < q₁) (ha₂ : a₂ < q₂)
    (h : (a₁:ℝ)/q₁ = (a₂:ℝ)/q₂) : q₁ = q₂ ∧ a₁ = a₂ := by
  have hnat : a₁ * q₂ = a₂ * q₁ := by
    have hq₁r : (q₁:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq₁
    have hq₂r : (q₂:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq₂
    have hreal : (a₁:ℝ) * q₂ = (a₂:ℝ) * q₁ := by
      field_simp at h
      rw [mul_comm (q₁:ℝ) (a₂:ℝ)] at h
      exact h
    exact_mod_cast hreal
  have hdvd₁ : q₁ ∣ q₂ := by
    have hd : q₁ ∣ a₁ * q₂ := ⟨a₂, by rw [hnat, mul_comm]⟩
    exact h₁.symm.dvd_of_dvd_mul_left hd
  have hdvd₂ : q₂ ∣ q₁ := by
    have hd : q₂ ∣ a₂ * q₁ := ⟨a₁, by rw [← hnat, mul_comm]⟩
    exact h₂.symm.dvd_of_dvd_mul_left hd
  have hq : q₁ = q₂ := Nat.dvd_antisymm hdvd₁ hdvd₂
  refine ⟨hq, ?_⟩
  rw [hq] at hnat
  exact Nat.mul_right_cancel hq₂ hnat

/-- **At most one major-arc term is active.**  If the arcs of radius `r` around the two distinct
frequencies `a₁/q₁ + l₁`, `a₂/q₂ + l₂` both contain `θ`, then `2r ≥ (q₁q₂)⁻¹`.  Equivalently: for
`2r < (q₁q₂)⁻¹` the two triples coincide. -/
theorem majorArc_term_unique {θ r : ℝ} {q₁ q₂ a₁ a₂ : ℕ} {l₁ l₂ : ℤ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (ha₁ : a₁ < q₁) (ha₂ : a₂ < q₂)
    (hg₁ : Nat.gcd a₁ q₁ = 1) (hg₂ : Nat.gcd a₂ q₂ = 1)
    (harc₁ : |θ - (a₁:ℝ)/q₁ - (l₁:ℝ)| ≤ r) (harc₂ : |θ - (a₂:ℝ)/q₂ - (l₂:ℝ)| ≤ r)
    (hr : 2*r < ((q₁:ℝ)*(q₂:ℝ))⁻¹) :
    q₁ = q₂ ∧ a₁ = a₂ ∧ l₁ = l₂ := by
  have key : ((a₁:ℝ)/q₁ + (l₁:ℝ)) = ((a₂:ℝ)/q₂ + (l₂:ℝ)) := by
    by_contra hne
    have hsep := majorArc_shift_sep hq₁ hq₂ hne
    have htri : |(a₁:ℝ)/q₁ + (l₁:ℝ) - ((a₂:ℝ)/q₂ + (l₂:ℝ))| ≤ 2*r := by
      have hsplit : (a₁:ℝ)/q₁ + (l₁:ℝ) - ((a₂:ℝ)/q₂ + (l₂:ℝ))
          = ((a₁:ℝ)/q₁ + (l₁:ℝ) - θ) + (θ - (a₂:ℝ)/q₂ - (l₂:ℝ)) := by ring
      rw [hsplit]
      calc |((a₁:ℝ)/q₁ + (l₁:ℝ) - θ) + (θ - (a₂:ℝ)/q₂ - (l₂:ℝ))|
          ≤ |(a₁:ℝ)/q₁ + (l₁:ℝ) - θ| + |θ - (a₂:ℝ)/q₂ - (l₂:ℝ)| := abs_add_le _ _
        _ = |θ - (a₁:ℝ)/q₁ - (l₁:ℝ)| + |θ - (a₂:ℝ)/q₂ - (l₂:ℝ)| := by
            rw [show (a₁:ℝ)/q₁ + (l₁:ℝ) - θ = -(θ - (a₁:ℝ)/q₁ - (l₁:ℝ)) by ring, abs_neg]
        _ ≤ r + r := add_le_add harc₁ harc₂
        _ = 2*r := by ring
    linarith
  -- the shift equality forces `l₁ = l₂` and equality of the fractions
  have hlr : ((l₁:ℝ) - (l₂:ℝ)) = (a₂:ℝ)/q₂ - (a₁:ℝ)/q₁ := by linarith
  have hbnd : |(l₁:ℝ) - (l₂:ℝ)| < 1 := by
    have h₁' : (0:ℝ) < q₁ := by exact_mod_cast hq₁
    have h₂' : (0:ℝ) < q₂ := by exact_mod_cast hq₂
    have ha₁' : (a₁:ℝ)/q₁ < 1 := by rw [div_lt_one h₁']; exact_mod_cast ha₁
    have ha₁'' : (0:ℝ) ≤ (a₁:ℝ)/q₁ := by positivity
    have ha₂' : (0:ℝ) ≤ (a₂:ℝ)/q₂ := by positivity
    have ha₂'' : (a₂:ℝ)/q₂ < 1 := by rw [div_lt_one h₂']; exact_mod_cast ha₂
    rw [hlr, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hl : l₁ = l₂ := by
    have hml : ((l₁ - l₂ : ℤ) : ℝ) = (l₁:ℝ) - (l₂:ℝ) := by push_cast; ring
    have hlt : (l₁ - l₂ : ℤ) < 1 := by
      have : ((l₁ - l₂ : ℤ) : ℝ) < 1 := by rw [hml]; exact (abs_lt.mp hbnd).2
      exact_mod_cast this
    have hgt : (-1 : ℤ) < l₁ - l₂ := by
      have : (-1 : ℝ) < ((l₁ - l₂ : ℤ) : ℝ) := by rw [hml]; exact (abs_lt.mp hbnd).1
      exact_mod_cast this
    omega
  have hfrac : (a₁:ℝ)/q₁ = (a₂:ℝ)/q₂ := by
    rw [hl] at key
    linarith
  obtain ⟨hqeq, haeq⟩ := frac_eq_of_coprime hq₁ hq₂ (Nat.coprime_iff_gcd_eq_one.mpr hg₁)
    (Nat.coprime_iff_gcd_eq_one.mpr hg₂) ha₁ ha₂ hfrac
  exact ⟨hqeq, haeq, hl⟩

/-! ## Route B: the sharp-core / profile-error split of the `q`-blocks

The `m`-th dyadic `q`-block of `majorArcModel (1/4) N` is the sum of the `majorArcBlock`s over the
denominators `q ∈ [2^m, 2^(m+1))`.  Bourgain's §6 argument replaces, *scale by scale*, the Fresnel
profile of each of these terms by the sharp indicator `1_{|N²β| ≤ 1}`: the *sharp core* is a
weighted periodised-neighbourhood indicator (a sub-family of the neighbourhood family of Lemma 4.1)
and the *profile error* has a pointwise `ℓ²`-in-the-scale bound (`fresnel_replace_sharp_tsum_le`).
This section formalises the identification of the sharp core; the error and the assembly follow. -/

open Classical in
/-- The Gauss-sum weight `τ_{a/q} = q⁻¹ ∑_{r<q} e(a r²/q)` of a single major-arc term. -/
noncomputable def blockGaussWeight (q : ℕ) (a : ℕ) : ℂ :=
  ((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ 2 / (q : ℂ)))

/-- The `(q,a)` pairs of the `m`-th dyadic `q`-block (`2^m ≤ q < 2^(m+1)`, `a < q` coprime). -/
noncomputable def blockPair (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico (2 ^ m) (2 ^ (m + 1))).biUnion
    (fun q => ((Finset.range q).filter (fun a => Nat.gcd a q = 1)).image (fun a => (q, a)))

open Classical in
/-- The **sharp core** of the `m`-th dyadic block at scale `k`: the profile of every term of the
block replaced by the sharp indicator at the dyadic radius `4^{-k}`. -/
noncomputable def blockCore (m k : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2 : ℤ) 2,
    starRingEnd ℂ (blockGaussWeight i.1 i.2) *
      (if |(4:ℝ)^k * (θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)

open Classical in
/-- The sharp core written as a **weighted periodised-neighbourhood** sum: this is the exact form
consumed by the wall estimate (`WeightedPeriodicNeighborhoodMaximal`). -/
noncomputable def blockCorePer (m k : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, starRingEnd ℂ (blockGaussWeight i.1 i.2) *
      (if ∃ l : ℤ, |θ + (l:ℝ) - (i.2:ℝ)/(i.1:ℝ)| ≤ (4:ℝ)^(-(k:ℝ)) then (1:ℂ) else 0)

/-- `|x - y| ≤ |x| + |y|` (used for the major-arc separation). -/
lemma abs_sub_zero (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have h := abs_sub_le x 0 y
  rwa [sub_zero, zero_sub, abs_neg] at h

/-- An integer lying within `r < 1/2` of a point of `(0,1)` shifted by a point of `[0,1)` lies in
the window `[-2,2]`. -/
lemma int_mem_Icc_of_close {c θ r : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r < 1 / 2) {l : ℤ}
    (hl : |θ - c - (l : ℝ)| ≤ r) : l ∈ Finset.Icc (-2 : ℤ) 2 := by
  have h1 : |(l:ℝ)| ≤ |θ - c| + r := by
    calc |(l:ℝ)| = |(θ - c - (l:ℝ)) - (θ - c)| := by
          rw [abs_sub_comm (θ - c - (l:ℝ)) (θ - c),
            show (θ - c) - (θ - c - (l:ℝ)) = (l:ℝ) by ring]
      _ ≤ |θ - c| + |θ - c - (l:ℝ)| := by
          have h := abs_sub_zero (θ - c - (l:ℝ)) (θ - c); linarith [abs_nonneg (θ - c - (l:ℝ))]
      _ ≤ |θ - c| + r := by linarith
  have h2 : |θ - c| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h3 : |(l:ℝ)| < 2 := by linarith
  rw [abs_lt] at h3
  rw [Finset.mem_Icc]
  constructor
  · have h4 : ((-2:ℤ):ℝ) < (l:ℝ) := by push_cast; linarith [h3.1]
    exact_mod_cast (le_of_lt h4)
  · have h4 : (l:ℝ) < ((2:ℤ):ℝ) := by push_cast; linarith [h3.2]
    exact_mod_cast (le_of_lt h4)

open Classical in
/-- **The single-frequency sharp-core identification.**  On `θ ∈ (0,1)`, for a frequency
`c ∈ [0,1)` and radius `r < 1/2`, the sum of the sharp indicators `1_{|θ - c - l| ≤ r}` over the
window `l ∈ [-2,2]` is the *periodised* indicator `1_{∃l, |θ + l - c| ≤ r}`. -/
lemma sharpCore_sum_eq_periodic (c θ r : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr0 : 0 < r) (hr : r < 1 / 2) :
    (∑ l ∈ Finset.Icc (-2 : ℤ) 2, (if |θ - c - (l : ℝ)| ≤ r then (1 : ℂ) else 0))
      = (if ∃ l : ℤ, |θ + (l : ℝ) - c| ≤ r then (1 : ℂ) else 0) := by
  have hsub : ∀ l : ℤ, |θ + (l : ℝ) - c| = |θ - c - ((-l : ℤ) : ℝ)| := by
    intro l
    rw [show θ + (l : ℝ) - c = θ - c - ((-l : ℤ) : ℝ) by push_cast; ring]
  have hequiv : (∃ l : ℤ, |θ + (l : ℝ) - c| ≤ r)
      ↔ (∃ l : ℤ, |θ - c - (l : ℝ)| ≤ r) := by
    constructor
    · rintro ⟨l, hl⟩; exact ⟨-l, by rw [← hsub l]; exact hl⟩
    · rintro ⟨l, hl⟩
      refine ⟨-l, ?_⟩
      rw [hsub (-l)]
      simpa using hl
  by_cases hnone : (∃ l : ℤ, |θ - c - (l : ℝ)| ≤ r)
  · obtain ⟨l₀, hl₀⟩ := hnone
    have hcond : (∃ l : ℤ, |θ + (l : ℝ) - c| ≤ r) := hequiv.mpr ⟨l₀, hl₀⟩
    rw [if_pos hcond]
    rw [Finset.sum_eq_single l₀ ?_ ?_]
    · rw [if_pos hl₀]
    · intro b hb hbne
      rw [if_neg]
      intro hcon
      have h2r : |θ - c - (l₀:ℝ)| + |θ - c - (b:ℝ)| < 1 := by linarith
      have hsplit : |(b:ℝ) - (l₀:ℝ)| ≤ |θ - c - (l₀:ℝ)| + |θ - c - (b:ℝ)| := by
        calc |(b:ℝ) - (l₀:ℝ)| = |(θ - c - (l₀:ℝ)) - (θ - c - (b:ℝ))| := by ring_nf
          _ ≤ |θ - c - (l₀:ℝ)| + |θ - c - (b:ℝ)| := abs_sub_zero _ _
      have hcast : (((b - l₀ : ℤ)) : ℝ) = (b:ℝ) - (l₀:ℝ) := by push_cast; ring
      have h1 : |((b - l₀ : ℤ) : ℝ)| < 1 := by rw [hcast]; linarith
      rw [← Int.cast_abs] at h1
      have h2 : |b - l₀| < (1:ℤ) := by exact_mod_cast h1
      rw [abs_lt] at h2
      exact hbne (by omega)
    · intro hnot
      exact absurd (int_mem_Icc_of_close hc0 hc1 hθ0 hθ1 hr hl₀) hnot
  · have hcond : ¬ (∃ l : ℤ, |θ + (l : ℝ) - c| ≤ r) := fun h => hnone (hequiv.mp h)
    rw [if_neg hcond]
    refine Finset.sum_eq_zero (fun l hl => ?_)
    rw [if_neg]
    intro hcon
    exact hnone ⟨l, hcon⟩

/-- Membership in `blockPair`. -/
lemma mem_blockPair {m : ℕ} {i : ℕ × ℕ} :
    i ∈ blockPair m ↔ 2^m ≤ i.1 ∧ i.1 < 2^(m+1) ∧ i.2 < i.1 ∧ Nat.gcd i.2 i.1 = 1 := by
  constructor
  · intro h
    rw [blockPair, Finset.mem_biUnion] at h
    obtain ⟨q, hq, hq'⟩ := h
    rw [Finset.mem_Ico] at hq
    rw [Finset.mem_image] at hq'
    obtain ⟨a, ha, rfl⟩ := hq'
    rw [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨hq.1, hq.2, ha.1, ha.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [blockPair, Finset.mem_biUnion]
    refine ⟨i.1, Finset.mem_Ico.mpr ⟨h1, h2⟩, ?_⟩
    rw [Finset.mem_image]
    exact ⟨i.2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h3, h4⟩, rfl⟩

open Classical in
/-- **The block-level sharp-core identification.**  On `θ ∈ (0,1)` and for `k ≥ 1`, the sharp core
of the `m`-th dyadic `q`-block is the weighted sum of the *periodised* `4^{-k}`-neighbourhood
indicators of its frequencies `a/q`. -/
theorem blockCore_eq_periodic (m k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    blockCore m k θ = blockCorePer m k θ := by
  rw [blockCore, blockCorePer]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hmem := mem_blockPair.mp hi
  have hq1 : 1 ≤ i.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  have hqpos : (0:ℝ) < (i.1 : ℝ) := by exact_mod_cast hq1
  set c : ℝ := (i.2:ℝ)/(i.1:ℝ) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hqpos]; exact_mod_cast hmem.2.2.1
  have hr0 : (0:ℝ) < (4:ℝ)^(-(k:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hr : (4:ℝ)^(-(k:ℝ)) < 1/2 := by
    have hkk : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h4 : (4:ℝ)^(-(k:ℝ)) ≤ (4:ℝ)^(-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h41 : (4:ℝ)^(-(1:ℝ)) = 1/4 := by norm_num
    rw [h41] at h4; linarith
  have hpos : (0:ℝ) < (4:ℝ)^k := by positivity
  have hiff : ∀ l : ℤ, (|(4:ℝ)^k * (θ - c - (l:ℝ))| ≤ 1)
      ↔ (|θ - c - (l:ℝ)| ≤ (4:ℝ)^(-(k:ℝ))) := by
    intro l
    rw [abs_mul, abs_of_pos hpos]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), Real.rpow_natCast, inv_eq_one_div,
      le_div_iff₀ hpos]
    constructor <;> intro h <;> linarith
  have hinner : (∑ l ∈ Finset.Icc (-2 : ℤ) 2,
        (if |(4:ℝ)^k * (θ - c - (l:ℝ))| ≤ 1 then (1:ℂ) else 0))
      = (if ∃ l : ℤ, |θ + (l:ℝ) - c| ≤ (4:ℝ)^(-(k:ℝ)) then (1:ℂ) else 0) := by
    have hpt : ∀ l : ℤ, (if |(4:ℝ)^k * (θ - c - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)
        = (if |θ - c - (l:ℝ)| ≤ (4:ℝ)^(-(k:ℝ)) then (1:ℂ) else 0) := by
      intro l
      by_cases h : |(4:ℝ)^k * (θ - c - (l:ℝ))| ≤ 1
      · rw [if_pos h, if_pos ((hiff l).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((hiff l).mpr hh))]
    refine (Finset.sum_congr rfl (fun l _ => hpt l)).trans ?_
    exact sharpCore_sum_eq_periodic c θ ((4:ℝ)^(-(k:ℝ))) hc0 hc1 hθ0 hθ1 hr0 hr
  rw [← Finset.mul_sum, hinner]

open Classical in
/-- The major-arc radius `N^{-5/4}` of the model `majorArcModel (1/4) N`. -/
noncomputable def arcRad (N : ℕ) : ℝ := ((N : ℝ) ^ (1 + (1:ℝ)/4))⁻¹

lemma arcRad_pos (N : ℕ) (hN : 1 ≤ N) : 0 < arcRad N := by
  rw [arcRad]; positivity

lemma arcRad_eq_rpow (N : ℕ) : arcRad N = (N : ℝ) ^ (-(1 + (1:ℝ)/4)) := by
  rw [arcRad, Real.rpow_neg (Nat.cast_nonneg N)]

lemma arcRad_eq (N : ℕ) : arcRad N = (N : ℝ) ^ (-(5:ℝ)/4) := by
  rw [arcRad_eq_rpow]; congr 1; norm_num

lemma arcRad_antitone {N N' : ℕ} (h : N ≤ N') (hN : 1 ≤ N) : arcRad N' ≤ arcRad N := by
  rw [arcRad_eq, arcRad_eq,
    show (-(5:ℝ)/4) = -((5:ℝ)/4) by ring, Real.rpow_neg (by positivity),
    Real.rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity)
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by norm_num))

lemma arcRad_two_pow (k : ℕ) : arcRad (2^k) = (2:ℝ) ^ (-(5:ℝ)/4 * (k:ℝ)) := by
  have h1 : ((2^k : ℕ) : ℝ) = (2:ℝ) ^ ((k:ℕ):ℝ) := by
    push_cast
    rw [Real.rpow_natCast]
  have h2 : ((2:ℝ) ^ ((k:ℕ):ℝ)) ^ (-(5:ℝ)/4) = (2:ℝ) ^ (-(5:ℝ)/4 * (k:ℝ)) :=
    calc ((2:ℝ) ^ ((k:ℕ):ℝ)) ^ (-(5:ℝ)/4)
        = (2:ℝ) ^ (((k:ℕ):ℝ) * (-(5:ℝ)/4)) := (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
      _ = (2:ℝ) ^ (-(5:ℝ)/4 * (k:ℝ)) := by ring_nf
  rw [arcRad_eq, h1, h2]

lemma two_mul_arcRad_two_pow_eq (k : ℕ) :
    2 * arcRad (2^k) = (2:ℝ) ^ (1 + (-(5:ℝ)/4 * (k:ℝ))) := by
  rw [arcRad_two_pow]
  calc (2:ℝ) * (2:ℝ)^(-(5:ℝ)/4 * (k:ℝ))
      = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-(5:ℝ)/4 * (k:ℝ)) := by rw [Real.rpow_one]
    _ = (2:ℝ)^((1:ℝ) + (-(5:ℝ)/4 * (k:ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    _ = (2:ℝ)^(1 + (-(5:ℝ)/4 * (k:ℝ))) := by norm_num

/-- `2 · arcRad (2^k) < 1` for `k ≥ 3`. -/
lemma two_mul_arcRad_two_pow_lt_one {k : ℕ} (hk : 3 ≤ k) : 2 * arcRad (2^k) < 1 := by
  rw [two_mul_arcRad_two_pow_eq]
  have hexp : (1:ℝ) + (-(5:ℝ)/4 * (k:ℝ)) < 0 := by
    have : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    nlinarith
  calc (2:ℝ)^(1 + (-(5:ℝ)/4 * (k:ℝ))) < (2:ℝ)^(0:ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    _ = 1 := Real.rpow_zero 2

/-- `2 · arcRad (2^k) < (2^(2m+2))⁻¹` for `k ≥ 2m+3`. -/
lemma two_mul_arcRad_two_pow_lt_inv {m k : ℕ} (hk : 2*m+3 ≤ k) :
    2 * arcRad (2^k) < ((2:ℝ)^(2*m+2))⁻¹ := by
  have hexp : (1:ℝ) + (-(5:ℝ)/4 * (k:ℝ)) < -((2*m+2 : ℕ) : ℝ) := by
    have h1 : (2*m+3 : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    push_cast at h1 ⊢
    nlinarith
  rw [two_mul_arcRad_two_pow_eq, ← Real.rpow_natCast (2:ℝ) (2*m+2),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp

open Classical in
/-- The **active index set** of the `m`-th dyadic block at scale `k`: the triples `(q,a,l)` whose
major arc of radius `N^{-5/4}` (with `N = 2^k`) contains `θ`. -/
noncomputable def actIdx (m k : ℕ) (θ : ℝ) : Finset ((ℕ × ℕ) × ℤ) :=
  (blockPair m ×ˢ Finset.Icc (-2 : ℤ) 2).filter
    (fun p => |θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (p.2 : ℝ)| ≤ arcRad (2^k))

lemma mem_actIdx {m k : ℕ} {θ : ℝ} {p : (ℕ × ℕ) × ℤ} :
    p ∈ actIdx m k θ ↔ p.1 ∈ blockPair m ∧ p.2 ∈ Finset.Icc (-2:ℤ) 2 ∧
      |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ arcRad (2^k) := by
  rw [actIdx, Finset.mem_filter, Finset.mem_product]
  tauto

lemma actIdx_subset {m : ℕ} {θ : ℝ} {k k' : ℕ} (h : k ≤ k') : actIdx m k' θ ⊆ actIdx m k θ := by
  intro p hp
  rw [mem_actIdx] at hp ⊢
  exact ⟨hp.1, hp.2.1,
    le_trans hp.2.2 (arcRad_antitone (Nat.pow_le_pow_right (by norm_num) h) Nat.one_le_two_pow)⟩

/-- **At most one term of a dyadic block is active at any frequency**, as soon as the scale is large
enough (`2m+3 ≤ k`). -/
lemma actIdx_card_le_one {m k : ℕ} (hk : 2*m + 3 ≤ k) (θ : ℝ) : (actIdx m k θ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  rw [mem_actIdx] at hp hq
  obtain ⟨hp1, hp2, hparc⟩ := hp
  obtain ⟨hq1, hq2, hqarc⟩ := hq
  have hmemP := mem_blockPair.mp hp1
  have hmemQ := mem_blockPair.mp hq1
  have hppos : 0 < p.1.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  have hqpos : 0 < q.1.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  by_cases hqa : p.1 = q.1
  · have hqarc' : |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ)| ≤ arcRad (2^k) := by
      have h := hqarc
      rw [← hqa] at h
      exact h
    have hl : p.2 = q.2 := by
      by_contra hne
      have h2r : 2 * arcRad (2^k) < 1 := two_mul_arcRad_two_pow_lt_one (by omega)
      have hkey : |(p.2:ℝ) - (q.2:ℝ)| ≤ 2 * arcRad (2^k) := by
        have h := abs_sub_zero (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
          (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ))
        rw [show (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
              - (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ)) = (q.2:ℝ) - (p.2:ℝ) by ring,
          abs_sub_comm] at h
        linarith
      have hcast : (((p.2 - q.2 : ℤ)) : ℝ) = (p.2:ℝ) - (q.2:ℝ) := by push_cast; ring
      have hlt : |((p.2 - q.2 : ℤ) : ℝ)| < 1 := by rw [hcast]; linarith
      rw [← Int.cast_abs] at hlt
      have h2 : |p.2 - q.2| < (1:ℤ) := by exact_mod_cast hlt
      rw [abs_lt] at h2
      exact hne (by omega)
    exact Prod.ext hqa hl
  · have hp_lt : (p.1.1:ℝ) < (2:ℝ)^(m+1) := by
      have := hmemP.2.1
      exact_mod_cast this
    have hq_lt : (q.1.1:ℝ) < (2:ℝ)^(m+1) := by
      have := hmemQ.2.1
      exact_mod_cast this
    have hppos' : (0:ℝ) < (p.1.1:ℝ) := by exact_mod_cast hppos
    have hqpos' : (0:ℝ) < (q.1.1:ℝ) := by exact_mod_cast hqpos
    have hpow : (2:ℝ)^(m+1) * (2:ℝ)^(m+1) = (2:ℝ)^(2*m+2) := by
      rw [← pow_add]
      congr 1
      ring
    have hprod : ((p.1.1:ℝ) * (q.1.1:ℝ)) ≤ (2:ℝ)^(2*m+2) := by
      have hpq : (p.1.1:ℝ) * (q.1.1:ℝ) < (2:ℝ)^(m+1) * (2:ℝ)^(m+1) :=
        mul_lt_mul hp_lt (le_of_lt hq_lt) hqpos' (by positivity)
      rw [hpow] at hpq
      exact le_of_lt hpq
    have hsep : 2 * arcRad (2^k) < ((p.1.1:ℝ) * (q.1.1:ℝ))⁻¹ :=
      lt_of_lt_of_le (two_mul_arcRad_two_pow_lt_inv hk)
        ((inv_le_inv₀ (by positivity) (by positivity)).mpr hprod)
    have huniq := majorArc_term_unique hppos hqpos hmemP.2.2.1 hmemQ.2.2.1
      (Nat.coprime_iff_gcd_eq_one.mp hmemP.2.2.2) (Nat.coprime_iff_gcd_eq_one.mp hmemQ.2.2.2)
      hparc hqarc hsep
    obtain ⟨h1, h2, h3⟩ := huniq
    exact absurd (Prod.ext (Prod.ext h1 h2) h3) (fun h' => hqa (congrArg Prod.fst h'))

open Classical in
/-- The **sharp term** of a single major-arc term at dyadic scale `k`. -/
noncomputable def sharpTerm (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  blockGaussWeight q a *
    (if |(4:ℝ)^k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)

open Classical in
/-- The single major-arc term of the block at dyadic scale `k`, restricted to its arc. -/
noncomputable def modelTermArc (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k) then modelTerm (2^k) q a l θ else 0

/-- The **error** of the `m`-th block at scale `k`: model minus sharp core (the core being switched
off below the threshold scale `4m+4`). -/
noncomputable def blockErr (m k : ℕ) (θ : ℝ) : ℂ :=
  starRingEnd ℂ (modelQBlock m (2^k) θ) -
    (if 4*m+4 ≤ k then blockCore m k θ else 0)

lemma conj_ite_one_zero (b : Prop) [Decidable b] :
    starRingEnd ℂ (if b then (1:ℂ) else 0) = (if b then (1:ℂ) else 0) := by
  by_cases hb : b <;> simp [hb]

lemma majorArcBlock_two_pow_eq_sum (q k : ℕ) (θ : ℝ) :
    majorArcBlock ((1:ℝ)/4) (2^k) θ q
      = ∑ a ∈ Finset.range q, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          (if Nat.gcd a q = 1 then modelTermArc q a l k θ else 0) := by
  have hmb : majorArcBlock ((1:ℝ)/4) (2^k) θ q
      = ∑ a ∈ Finset.range q, (if Nat.gcd a q = 1 then
          (∑ l ∈ Finset.Icc (-2:ℤ) 2, (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k)
            then modelTerm (2^k) q a l θ else 0)) else 0) := by
    rw [majorArcBlock]; rfl
  rw [hmb]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  by_cases hg : Nat.gcd a q = 1
  · rw [if_pos hg]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [if_pos hg, modelTermArc]
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro l hl; rw [if_neg hg]

lemma rpow_quarter_two_pow (k : ℕ) :
    (((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4) = (2:ℝ) ^ ((k:ℝ)/4) := by
  have h1 : (((2^k : ℕ) : ℝ)) = (2:ℝ) ^ ((k:ℕ):ℝ) := by
    push_cast
    rw [Real.rpow_natCast]
  calc (((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)
      = ((2:ℝ) ^ ((k:ℕ):ℝ)) ^ ((1:ℝ)/4) := by rw [h1]
    _ = (2:ℝ) ^ ((k:ℝ) * ((1:ℝ)/4)) := (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    _ = (2:ℝ) ^ ((k:ℝ)/4) := by ring_nf

lemma blockQ_eq (m k : ℕ) (hk : 4*m+4 ≤ k) :
    (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)))).filter (fun q => Nat.log 2 q = m)
      = Finset.Ico (2^m) (2^(m+1)) := by
  rw [filter_log_eq_filter_pow]
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  have hQ : 2^(m+1) - 1 ≤ Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) := by
    refine Nat.le_floor ?_
    have h2 : (2:ℝ)^(m+1) ≤ (((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4) := by
      rw [rpow_quarter_two_pow, ← Real.rpow_natCast (2:ℝ) (m+1)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hk' : ((4*m+4 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      push_cast at hk' ⊢
      linarith
    have h3 : ((2^(m+1) - 1 : ℕ) : ℝ) < (2:ℝ)^(m+1) := by
      have h4 := Nat.sub_lt (Nat.two_pow_pos (m+1)) (by norm_num : 0 < 1)
      push_cast
      exact_mod_cast h4
    linarith
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨by omega, h2, h3⟩

lemma sum_blockPair (m : ℕ) {α : Type*} [AddCommMonoid α] (F : ℕ × ℕ → α) :
    (∑ i ∈ blockPair m, F i)
      = ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1), F (q, a) := by
  rw [blockPair, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact congrArg Prod.snd hab
  · intro q hq q' hq' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hx'
    exact hne (congrArg Prod.fst hb').symm

lemma conj_blockGaussWeight_ite (q a : ℕ) (b : Prop) [Decidable b] :
    starRingEnd ℂ (blockGaussWeight q a * (if b then (1:ℂ) else 0))
      = starRingEnd ℂ (blockGaussWeight q a) * (if b then (1:ℂ) else 0) := by
  rw [map_mul, conj_ite_one_zero]

lemma blockCore_eq_sum_sharpTerm (m k : ℕ) (θ : ℝ) :
    blockCore m k θ
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          starRingEnd ℂ (sharpTerm i.1 i.2 l k θ) := by
  rw [blockCore]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [sharpTerm, conj_blockGaussWeight_ite]

lemma sum_ite_gcd_eq (a q : ℕ) (Y : ℤ → ℂ) :
    (∑ l ∈ Finset.Icc (-2:ℤ) 2, (if Nat.gcd a q = 1 then Y l else 0))
      = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-2:ℤ) 2, Y l else 0) := by
  by_cases hg : Nat.gcd a q = 1
  · rw [if_pos hg]
    simp only [hg, if_true]
  · rw [if_neg hg]
    refine Finset.sum_eq_zero (fun l hl => ?_)
    simp only [hg, if_false]

lemma conj_ite_zero (b : Prop) [Decidable b] (X : ℂ) :
    starRingEnd ℂ (if b then X else 0) = (if b then starRingEnd ℂ X else 0) := by
  by_cases h : b <;> simp [h]

lemma modelQBlock_two_pow_eq_blockPair {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ) :
    starRingEnd ℂ (modelQBlock m (2^k) θ)
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          starRingEnd ℂ (modelTermArc i.1 i.2 l k θ) := by
  have h1 : starRingEnd ℂ (modelQBlock m (2^k) θ)
      = ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-2:ℤ) 2, starRingEnd ℂ (modelTermArc q a l k θ) := by
    rw [modelQBlock, blockQ_eq m k hk, map_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [majorArcBlock_two_pow_eq_sum, map_sum]
    have hstep : ∀ a : ℕ,
        starRingEnd ℂ (∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if Nat.gcd a q = 1 then modelTermArc q a l k θ else 0))
          = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-2:ℤ) 2,
              starRingEnd ℂ (modelTermArc q a l k θ) else 0) := by
      intro a
      rw [map_sum]
      rw [Finset.sum_congr rfl (fun l hl => conj_ite_zero _ (modelTermArc q a l k θ))]
      exact sum_ite_gcd_eq a q (fun l => starRingEnd ℂ (modelTermArc q a l k θ))
    rw [Finset.sum_congr rfl (fun a ha => hstep a)]
    rw [← Finset.sum_filter]
  rw [h1, sum_blockPair m]

lemma blockErr_eq_sum {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    blockErr m k θ = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (modelTermArc i.1 i.2 l k θ - sharpTerm i.1 i.2 l k θ) := by
  rw [blockErr, if_pos hk, modelQBlock_two_pow_eq_blockPair hk θ,
    blockCore_eq_sum_sharpTerm]
  simp_rw [← Finset.sum_sub_distrib, ← map_sub]



open Commons.Analysis.Fresnel (fresnelProfile norm_fresnelProfile_le_one)

lemma modelTerm_eq_gaussWeight_mul_fresnel (N q a : ℕ) (l : ℤ) (θ : ℝ) :
    modelTerm N q a l θ = blockGaussWeight q a *
      fresnelProfile ((N:ℝ)^2 * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))) := by
  rw [modelTerm, blockGaussWeight, fresnelProfile]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun r hr => ?_)
    congr 1
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro s hs
    congr 1
    push_cast
    ring

lemma norm_modelTerm_le_gaussWeight (N q a : ℕ) (l : ℤ) (θ : ℝ) :
    ‖modelTerm N q a l θ‖ ≤ ‖blockGaussWeight q a‖ := by
  rw [modelTerm_eq_gaussWeight_mul_fresnel, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (norm_fresnelProfile_le_one ((N:ℝ)^2 * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))))

lemma four_pow_eq_two_pow_sq (k : ℕ) : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
  rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, ← pow_mul]
  rw [Nat.mul_comm]

lemma modelTermArc_eq_zero_of_not_act {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k)) : modelTermArc q a l k θ = 0 := by
  rw [modelTermArc, if_neg h]

lemma inv_four_pow_le_arcRad (k : ℕ) : ((4:ℝ)^k)⁻¹ ≤ arcRad (2^k) := by
  have hL : ((4:ℝ)^k)⁻¹ = (2:ℝ) ^ (-(2:ℝ) * (k:ℝ)) := by
    rw [← Real.rpow_natCast (4:ℝ) k, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hL, arcRad_two_pow]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ?_
  have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  nlinarith

lemma sharpTerm_eq_zero_of_not_act {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k)) : sharpTerm q a l k θ = 0 := by
  rw [sharpTerm]
  have h2 : ¬ |(4:ℝ)^k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))| ≤ 1 := by
    intro hc
    apply h
    have h4 : (0:ℝ) < (4:ℝ)^k := by positivity
    have hc' : (4:ℝ)^k * |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ 1 := by
      rwa [abs_mul, abs_of_pos h4] at hc
    have hb : |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((4:ℝ)^k)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ h4]
      linarith
    linarith [inv_four_pow_le_arcRad k]
  rw [if_neg h2, mul_zero]

lemma norm_modelTermArc_sub_sharp_le {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ) :
    ‖modelTermArc q a l k θ - sharpTerm q a l k θ‖
      ≤ ‖blockGaussWeight q a‖ * ‖fresnelProfile ((4:ℝ)^k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ)))
          - (if |(4:ℝ)^k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)‖ := by
  by_cases harc : |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k)
  · have h1 : modelTermArc q a l k θ = modelTerm (2^k) q a l θ := by
      rw [modelTermArc, if_pos harc]
    have hxy : (((2^k : ℕ)) : ℝ)^2 = (4:ℝ)^k := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact (four_pow_eq_two_pow_sq k).symm
    rw [h1, modelTerm_eq_gaussWeight_mul_fresnel, hxy, sharpTerm, ← mul_sub]
    exact le_of_eq (norm_mul _ _)
  · rw [modelTermArc_eq_zero_of_not_act q a l θ harc,
      sharpTerm_eq_zero_of_not_act q a l θ harc, sub_zero, norm_zero]
    positivity

open Classical in
/-- The `q`-block of the model at scale `k`, written as a filtered interval: possible denominators
are only `q ∈ [2^m, 2^(m+1))`. -/
theorem blockQ_eq_filter_le (m k : ℕ) (hk : 4*m ≤ k) :
    (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)))).filter (fun q => Nat.log 2 q = m)
      = (Finset.Ico (2^m) (2^(m+1))).filter
          (fun q => q ≤ Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4))) := by
  rw [filter_log_eq_filter_pow]
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  have h1 : 1 ≤ 2^m := Nat.one_le_two_pow
  constructor
  · rintro ⟨⟨h1', h2'⟩, h3', h4'⟩
    exact ⟨⟨h3', h4'⟩, h2'⟩
  · rintro ⟨⟨h3', h4'⟩, h2'⟩
    exact ⟨⟨by omega, h2'⟩, h3', h4'⟩

open Classical in
/-- The **partial-block expansion** of the `m`-th model block at scale `k` in terms of the
arc-restricted single terms. -/
theorem star_modelQBlock_eq_sum {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    starRingEnd ℂ (modelQBlock m (2^k) θ)
      = ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
            (fun q => q ≤ Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4))),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-2:ℤ) 2, starRingEnd ℂ (modelTermArc q a l k θ) := by
  rw [modelQBlock, blockQ_eq_filter_le m k hk, map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [majorArcBlock_two_pow_eq_sum, map_sum]
  have hstep : ∀ a : ℕ,
      starRingEnd ℂ (∑ l ∈ Finset.Icc (-2:ℤ) 2,
          (if Nat.gcd a q = 1 then modelTermArc q a l k θ else 0))
        = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            starRingEnd ℂ (modelTermArc q a l k θ) else 0) := by
    intro a
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun l hl => conj_ite_zero _ (modelTermArc q a l k θ))]
    exact sum_ite_gcd_eq a q (fun l => starRingEnd ℂ (modelTermArc q a l k θ))
  rw [Finset.sum_congr rfl (fun a ha => hstep a)]
  rw [← Finset.sum_filter]

open Classical in
/-- The set of all `(q,a,l)` index triples of the `m`-th block. -/
noncomputable def allIdx (m : ℕ) : Finset ((ℕ × ℕ) × ℤ) :=
  blockPair m ×ˢ Finset.Icc (-2 : ℤ) 2

lemma actIdx_eq_filter (m k : ℕ) (θ : ℝ) :
    actIdx m k θ = (allIdx m).filter
      (fun p => |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ arcRad (2^k)) := rfl

lemma mem_allIdx {m : ℕ} {p : (ℕ × ℕ) × ℤ} :
    p ∈ allIdx m ↔ p.1 ∈ blockPair m ∧ p.2 ∈ Finset.Icc (-2:ℤ) 2 := by
  rw [allIdx, Finset.mem_product]

open Classical in
/-- The `m`-th model block at scale `k` is bounded by the *active* index sum: the terms outside the
arcs vanish, and each surviving term is bounded by its Gauss weight. -/
theorem norm_star_modelQBlock_le_actIdx {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    ‖starRingEnd ℂ (modelQBlock m (2^k) θ)‖
      ≤ ∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖ := by
  rw [star_modelQBlock_eq_sum hk θ]
  set Q : ℕ := Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) with hQ
  -- step 1: triangle inequality
  have h1 : ‖∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2, starRingEnd ℂ (modelTermArc q a l k θ)‖
      ≤ ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k) then ‖blockGaussWeight q a‖ else 0) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun q hq => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a ha => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l hl => ?_))
    rw [Complex.norm_conj]
    by_cases harc : |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k)
    · rw [if_pos harc, modelTermArc, if_pos harc]
      exact norm_modelTerm_le_gaussWeight (2^k) q a l θ
    · rw [if_neg harc, modelTermArc_eq_zero_of_not_act q a l θ harc, norm_zero]
  -- step 2: enlarge the `q`-range
  have h2 : ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k) then ‖blockGaussWeight q a‖ else 0)
      ≤ ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k) then ‖blockGaussWeight q a‖ else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q hq hnot => ?_)
    positivity
  -- step 3: reindex to `allIdx` and restrict to the active set
  have h3 : ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ arcRad (2^k) then ‖blockGaussWeight q a‖ else 0)
      = ∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖ := by
    rw [← sum_blockPair m (F := fun (i : ℕ × ℕ) => ∑ l ∈ Finset.Icc (-2:ℤ) 2,
      (if |θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ arcRad (2^k) then ‖blockGaussWeight i.1 i.2‖ else 0))]
    rw [← Finset.sum_product (blockPair m) (Finset.Icc (-2:ℤ) 2)
      (fun p : (ℕ × ℕ) × ℤ => (if |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ arcRad (2^k)
        then ‖blockGaussWeight p.1.1 p.1.2‖ else 0))]
    rw [actIdx_eq_filter, allIdx, ← Finset.sum_filter]
  linarith [h1, h2, h3]

open Classical in
/-- The profile error of the `m`-th block at scale `k ≥ 4m+4` is bounded by the *active* profile
sum. -/
theorem norm_blockErr_le_actIdx {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ‖blockErr m k θ‖ ≤ ∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖ *
      ‖fresnelProfile ((4:ℝ)^k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)))
        - (if |(4:ℝ)^k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))| ≤ 1 then (1:ℂ) else 0)‖ := by
  set g : (ℕ × ℕ) × ℤ → ℝ := fun p =>
    ‖fresnelProfile ((4:ℝ)^k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)))
      - (if |(4:ℝ)^k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))| ≤ 1 then (1:ℂ) else 0)‖ with hg
  rw [blockErr_eq_sum hk θ hθ0 hθ1]
  rw [← Finset.sum_product (blockPair m) (Finset.Icc (-2:ℤ) 2)
    (fun p : (ℕ × ℕ) × ℤ =>
      starRingEnd ℂ (modelTermArc p.1.1 p.1.2 p.2 k θ - sharpTerm p.1.1 p.1.2 p.2 k θ))]
  calc ‖∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
          starRingEnd ℂ (modelTermArc p.1.1 p.1.2 p.2 k θ - sharpTerm p.1.1 p.1.2 p.2 k θ)‖
      ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
          (if |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ arcRad (2^k)
            then ‖blockGaussWeight p.1.1 p.1.2‖ * g p else 0) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
        by_cases harc : |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ arcRad (2^k)
        · rw [if_pos harc]
          have h := norm_modelTermArc_sub_sharp_le (k := k) p.1.1 p.1.2 p.2 θ
          rwa [Complex.norm_conj]
        · rw [if_neg harc]
          have h1 := modelTermArc_eq_zero_of_not_act (k := k) p.1.1 p.1.2 p.2 θ harc
          have h2 := sharpTerm_eq_zero_of_not_act (k := k) p.1.1 p.1.2 p.2 θ harc
          rw [h1, h2, sub_zero, map_zero, norm_zero]
    _ = ∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖ * g p := by
        rw [actIdx_eq_filter, allIdx, ← Finset.sum_filter]



open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

lemma exists_gaussWeight_cap : ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
    ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2) := by
  obtain ⟨A, hApos, hA⟩ := norm_modelWeight_le
  refine ⟨A, hApos, fun m i hi => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  have hq1 : 1 ≤ i.1 := le_trans Nat.one_le_two_pow h1
  have hgcd : Int.gcd (i.2 : ℤ) (i.1 : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]; simp only [Int.natAbs_natCast]; exact_mod_cast h4
  have h := hA i.1 m (i.2 : ℤ) hq1 h1 hgcd
  simpa [blockGaussWeight] using h

/-- The active index set of a dyadic block has at most `80` elements. -/
lemma card_actIdx_le_eighty {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) : (actIdx m k θ).card ≤ 80 := by
  by_cases h : 2*m+3 ≤ k
  · exact le_trans (actIdx_card_le_one h θ) (by norm_num)
  · have hm1 : m ≤ 1 := by omega
    have hsub : actIdx m k θ ⊆ ((Finset.range 4) ×ˢ (Finset.range 4)) ×ˢ (Finset.Icc (-2:ℤ) 2) := by
      intro p hp
      obtain ⟨hmem, hl, _⟩ := mem_actIdx.mp hp
      obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hmem
      have hm4 : 2^(m+1) ≤ 4 := by
        calc 2^(m+1) = 2^m * 2 := by rw [pow_succ]
          _ ≤ 2^1 * 2 := Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) hm1)
          _ = 4 := by norm_num
      rw [Finset.mem_product, Finset.mem_product]
      exact ⟨⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hl⟩
    calc (actIdx m k θ).card
        ≤ (((Finset.range 4) ×ˢ (Finset.range 4)) ×ˢ (Finset.Icc (-2:ℤ) 2)).card :=
          Finset.card_le_card hsub
      _ = 80 := by simp [Finset.card_product]

lemma sum_gaussWeight_le {m k : ℕ} (θ : ℝ) (A : ℝ)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m → ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2)) :
    (∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖)
      ≤ (actIdx m k θ).card * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
  calc ∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖
      ≤ ∑ _p ∈ actIdx m k θ, (A * (2:ℝ)^(-(m:ℝ)/2)) :=
        Finset.sum_le_sum (fun p hp => hA p.1 ((mem_actIdx.mp hp).1))
    _ = (actIdx m k θ).card * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

lemma norm_star_modelQBlock_le_cap {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m → ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2)) :
    ‖starRingEnd ℂ (modelQBlock m (2^k) θ)‖ ≤ 80 * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
  have h1 := norm_star_modelQBlock_le_actIdx hk θ
  have h2 := sum_gaussWeight_le (m := m) (k := k) θ A hA
  have h3 := card_actIdx_le_eighty hk θ
  have hcap : 0 ≤ A * (2:ℝ)^(-(m:ℝ)/2) := by positivity
  calc ‖starRingEnd ℂ (modelQBlock m (2^k) θ)‖
      ≤ ∑ p ∈ actIdx m k θ, ‖blockGaussWeight p.1.1 p.1.2‖ := h1
    _ ≤ (actIdx m k θ).card * (A * (2:ℝ)^(-(m:ℝ)/2)) := h2
    _ ≤ 80 * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_right _ hcap
        exact_mod_cast h3

/-- For `k < 4m` the `m`-th dyadic block of the model at scale `2^k` is empty. -/
lemma modelQBlock_eq_zero_of_lt {m k : ℕ} (hk : k < 4*m) (θ : ℝ) :
    modelQBlock m (2^k) θ = 0 := by
  have hempty : (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)))).filter
      (fun q => Nat.log 2 q = m) = ∅ := by
    rw [filter_log_eq_filter_pow, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, h2m, _⟩ := hq
    have hQ : Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) < 2^m := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_natCast (2:ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
      have hk' : (k:ℝ) < 4 * (m:ℝ) := by exact_mod_cast hk
      linarith
    omega
  rw [modelQBlock, hempty, Finset.sum_empty]

open Commons.Analysis.Fresnel

lemma fresnelProfile_zero : fresnelProfile 0 = 1 := by
  rw [fresnelProfile]
  norm_num

lemma rpow_four_pow_neg_half (K : ℕ) : (((4:ℝ)^K) ^ (-((1:ℝ)/2))) = ((1:ℝ)/2)^K := by
  rw [← Real.rpow_natCast (4:ℝ) K, show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (2:ℝ) * ↑K * (-((1:ℝ)/2)) = -((K:ℝ)) by ring]
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast (2:ℝ) K, ← inv_pow]
  norm_num

lemma rpow_neg_half_mul (K : ℕ) (x : ℝ) :
    (((4:ℝ)^K * |x|) ^ (-((1:ℝ)/2))) = ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/2)) := by
  rw [Real.mul_rpow (by positivity) (abs_nonneg x), rpow_four_pow_neg_half K]

/-- The real-valued Fresnel replacement error at dyadic scale `K` (Bourgain (6.23)). -/
noncomputable def errVal (x : ℝ) (K : ℕ) : ℝ :=
  ‖fresnelProfile ((4:ℝ)^K * x) - (if |(4:ℝ)^K * x| ≤ 1 then (1:ℂ) else 0)‖

/-- The `ℝ≥0∞`-valued Fresnel replacement error at dyadic scale `K`. -/
noncomputable def errNorm (q a : ℕ) (l : ℤ) (K : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (errVal (θ - (a:ℝ)/(q:ℝ) - (l:ℝ)) K)

/-- **Uniform bound on the Fresnel replacement error** (Bourgain (6.23)). -/
lemma errVal_le (x : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℕ, errVal x K ≤ M * ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/2)) := by
  obtain ⟨C, hCpos, hC⟩ := fresnelProfile_decay
  refine ⟨max (2*Real.pi) C, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun K => ?_⟩
  set M : ℝ := max (2*Real.pi) C with hM
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set y : ℝ := (4:ℝ)^K * x with hy
  have hyabs : |y| = (4:ℝ)^K * |x| := by rw [hy, abs_mul, abs_of_pos (by positivity)]
  rw [errVal, ← hy]
  have hmain : ‖fresnelProfile y - (if |y| ≤ 1 then (1:ℂ) else 0)‖ ≤ M * |y| ^ (-((1:ℝ)/2)) := by
    by_cases hyl : |y| ≤ 1
    · rw [if_pos hyl]
      have h1 := fresnelProfile_sub_one_le y
      have h2 : (2*Real.pi) * |y| ≤ M * |y| ^ (-((1:ℝ)/2)) := by
        rcases eq_or_lt_of_le (abs_nonneg y) with h0 | h0
        · rw [← h0]
          simp
        · have h1' : (1:ℝ) ≤ |y| ^ (-((1:ℝ)/2)) := by
            have hh := Real.rpow_le_rpow_of_nonpos h0 hyl (by norm_num : (-((1:ℝ)/2)) ≤ 0)
            simpa using hh
          have hM' : (2*Real.pi) ≤ M := le_max_left _ _
          calc (2*Real.pi) * |y| ≤ (2*Real.pi) * 1 :=
                mul_le_mul_of_nonneg_left hyl (by positivity)
            _ ≤ M * |y| ^ (-((1:ℝ)/2)) := by
                exact mul_le_mul hM' h1' (by norm_num) (by positivity)
      linarith
    · rw [if_neg hyl, sub_zero]
      have h1 := hC y (le_of_lt (lt_of_not_ge hyl))
      have h2 : C / Real.sqrt |y| ≤ C * |y| ^ (-((1:ℝ)/2)) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg (abs_nonneg y)]
      have h3 : C ≤ M := le_max_right _ _
      have h4 : 0 ≤ |y| ^ (-((1:ℝ)/2)) := Real.rpow_nonneg (abs_nonneg y) _
      calc ‖fresnelProfile y‖ ≤ C / Real.sqrt |y| := h1
        _ ≤ C * |y| ^ (-((1:ℝ)/2)) := h2
        _ ≤ M * |y| ^ (-((1:ℝ)/2)) := mul_le_mul_of_nonneg_right h3 h4
  calc ‖fresnelProfile y - (if |y| ≤ 1 then (1:ℂ) else 0)‖ ≤ M * |y| ^ (-((1:ℝ)/2)) := hmain
    _ = M * (((4:ℝ)^K * |x|) ^ (-((1:ℝ)/2))) := by rw [hyabs]
    _ = M * (((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/2))) := by rw [rpow_neg_half_mul]
    _ = M * ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/2)) := by ring

/-- The Fresnel replacement error is summable along the dyadic scales. -/
lemma summable_errVal (x : ℝ) : Summable (errVal x) := by
  obtain ⟨M, hMpos, hM⟩ := errVal_le x
  have hgeo : Summable (fun K : ℕ => ((1:ℝ)/2)^K) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hmaj : Summable (fun K : ℕ => M * |x| ^ (-((1:ℝ)/2)) * ((1:ℝ)/2)^K) :=
    (hgeo.mul_left (M * |x| ^ (-((1:ℝ)/2)))).congr (fun K => by ring)
  refine Summable.of_nonneg_of_le (fun K => norm_nonneg _) (fun K => ?_) hmaj
  calc errVal x K ≤ M * ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/2)) := hM K
    _ = M * |x| ^ (-((1:ℝ)/2)) * ((1:ℝ)/2)^K := by ring

/-- **Bourgain (6.23) in `ℝ≥0∞` form**: the Fresnel replacement errors summed over the dyadic
scales are bounded by the constant `Cf` of `fresnel_replace_sharp_tsum_le`. -/
lemma errNorm_tsum_le {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, errVal x k) ≤ Cf) :
    ∀ (q a : ℕ) (l : ℤ) (θ : ℝ), (∑' K : ℕ, errNorm q a l K θ) ≤ ENNReal.ofReal Cf := by
  intro q a l θ
  set x : ℝ := θ - (a:ℝ)/(q:ℝ) - (l:ℝ) with hx
  have h1 : (∑' K : ℕ, errNorm q a l K θ)
      = ENNReal.ofReal (∑' K : ℕ, errVal x K) := by
    simp only [errNorm, errVal, ← hx]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun K => norm_nonneg _) (summable_errVal x)]
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hx0 : x = 0
  · have hz : ∀ K, errVal x K = 0 := by
      intro K
      have : (4:ℝ)^K * x = 0 := by rw [hx0, mul_zero]
      rw [errVal, this]
      simp [fresnelProfile_zero]
    simp only [hz, tsum_zero]
    exact hCf0
  · exact hCf x hx0

lemma enorm_eq_ofReal_norm'' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- The profile error of the `m`-th block at a large scale is bounded by the active-index sum. -/
lemma blockErr_enorm_le_tail {m K : ℕ} (hK : 4*m+4 ≤ K) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m → ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2)) :
    ‖blockErr m K θ‖ₑ ≤ ∑ p ∈ actIdx m (4*m+4) θ,
      ENNReal.ofReal (A * (2:ℝ)^(-(m:ℝ)/2)) * errNorm p.1.1 p.1.2 p.2 K θ := by
  set cap : ℝ := A * (2:ℝ)^(-(m:ℝ)/2) with hcapdef
  have hcap0 : 0 ≤ cap := by rw [hcapdef]; positivity
  have h1 := norm_blockErr_le_actIdx hK θ hθ0 hθ1
  have h2 : ‖blockErr m K θ‖
      ≤ ∑ p ∈ actIdx m (4*m+4) θ, cap * errVal (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)) K := by
    refine le_trans h1 ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (actIdx_subset hK) ?_) ?_
    · intro p hp hnp
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · refine Finset.sum_le_sum (fun p hp => ?_)
      exact mul_le_mul_of_nonneg_right (hA p.1 (mem_actIdx.mp hp).1) (norm_nonneg _)
  calc ‖blockErr m K θ‖ₑ
      = ENNReal.ofReal ‖blockErr m K θ‖ := enorm_eq_ofReal_norm'' _
    _ ≤ ENNReal.ofReal (∑ p ∈ actIdx m (4*m+4) θ,
          cap * errVal (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)) K) :=
        ENNReal.ofReal_le_ofReal h2
    _ = ∑ p ∈ actIdx m (4*m+4) θ,
          ENNReal.ofReal (cap * errVal (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)) K) :=
        ENNReal.ofReal_sum_of_nonneg (fun p hp => mul_nonneg hcap0 (norm_nonneg _))
    _ = ∑ p ∈ actIdx m (4*m+4) θ,
          ENNReal.ofReal cap * errNorm p.1.1 p.1.2 p.2 K θ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [errNorm, ENNReal.ofReal_mul hcap0]

lemma sq_sum_eq_of_card_le_one {ι : Type*} {T : Finset ι} (h : T.card ≤ 1)
    (X : ι → ℝ≥0∞) : (∑ p ∈ T, X p)^2 = ∑ p ∈ T, (X p)^2 := by
  rcases Nat.eq_zero_or_pos T.card with h0 | h1
  · have hT : T = ∅ := Finset.card_eq_zero.mp h0
    simp [hT]
  · have h1' : T.card = 1 := le_antisymm h h1
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1'
    simp

lemma sq_le_tsum_sq {a : ℕ → ℝ≥0∞} : (∑' l, a l ^ 2) ≤ (∑' l, a l) ^ 2 := by
  have h : ∀ l, a l ^ 2 ≤ (∑' l, a l) * a l := by
    intro l
    rw [pow_two]
    exact mul_le_mul_left (ENNReal.le_tsum l) (a l)
  calc (∑' l, a l ^ 2) ≤ ∑' l, (∑' l, a l) * a l := ENNReal.tsum_le_tsum h
    _ = (∑' l, a l) * (∑' l, a l) := ENNReal.tsum_mul_left
    _ = (∑' l, a l) ^ 2 := by rw [pow_two]

lemma ennreal_tsum_finsetSum {ι : Type*} (s : Finset ι) (f : ℕ → ι → ℝ≥0∞) :
    (∑' a, ∑ b ∈ s, f a b) = ∑ b ∈ s, ∑' a, f a b :=
  Summable.tsum_finsetSum (fun i _ => ENNReal.summable)

/-- **Bourgain (6.23), block form**: the profile errors of the `m`-th dyadic `q`-block form a
square-summable family along the dyadic scales, with sum bounded by `(C·2^{-m/2})²`. -/
theorem blockErr_tsum_sq_le (A Cf : ℝ) (hA0 : 0 < A) (hCf0 : 0 < Cf)
    (hA : ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2))
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, errVal x k) ≤ Cf)
    (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑' K : ℕ, ‖blockErr m K θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2)) ^ 2) := by
  set cap : ℝ := A * (2:ℝ)^(-(m:ℝ)/2) with hcapdef
  have hcap0 : 0 ≤ cap := by rw [hcapdef]; positivity
  set D : ℝ := A * (160 + Cf) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun K => 4*m+4 ≤ K)]
  have hsmall : (∑ K ∈ s.filter (fun K => ¬ 4*m+4 ≤ K), ‖blockErr m K θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((160*cap)^2) := by
    set t : Finset ℕ := s.filter (fun K => ¬ 4*m+4 ≤ K) with ht
    have hstep : ∀ K ∈ t, ‖blockErr m K θ‖ₑ ^ (2:ℝ)
        ≤ (if 4*m ≤ K then (ENNReal.ofReal (80*cap))^2 else 0) := by
      intro K hK
      have hKlt : K < 4*m+4 := by
        rw [ht, Finset.mem_filter] at hK
        omega
      rw [ENNReal.rpow_two]
      by_cases hK4 : 4*m ≤ K
      · rw [if_pos hK4, enorm_eq_ofReal_norm'']
        have hb : ‖blockErr m K θ‖ ≤ 80*cap := by
          rw [blockErr, if_neg (by omega : ¬ 4*m+4 ≤ K), sub_zero, hcapdef]
          exact norm_star_modelQBlock_le_cap hK4 θ A (le_of_lt hA0) (hA m)
        exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hb) 2
      · rw [if_neg hK4]
        have hz : ‖blockErr m K θ‖ = 0 := by
          rw [blockErr, if_neg (by omega : ¬ 4*m+4 ≤ K), sub_zero,
            modelQBlock_eq_zero_of_lt (by omega : K < 4*m), map_zero, norm_zero]
        rw [enorm_eq_ofReal_norm'', hz]
        simp
    have hsub2 : t.filter (fun K => 4*m ≤ K) ⊆ Finset.Ico (4*m) (4*m+4) := by
      intro K hK
      rw [Finset.mem_filter] at hK
      rw [ht, Finset.mem_filter] at hK
      rw [Finset.mem_Ico]
      omega
    have hcard : (t.filter (fun K => 4*m ≤ K)).card ≤ 4 := by
      calc (t.filter (fun K => 4*m ≤ K)).card ≤ (Finset.Ico (4*m) (4*m+4)).card :=
            Finset.card_le_card hsub2
        _ = 4 := by simp
    calc ∑ K ∈ t, ‖blockErr m K θ‖ₑ ^ (2:ℝ)
        ≤ ∑ K ∈ t, (if 4*m ≤ K then (ENNReal.ofReal (80*cap))^2 else 0) := Finset.sum_le_sum hstep
      _ = ∑ K ∈ t.filter (fun K => 4*m ≤ K), (ENNReal.ofReal (80*cap))^2 := by
          rw [← Finset.sum_filter]
      _ = ((t.filter (fun K => 4*m ≤ K)).card : ℝ≥0∞) * (ENNReal.ofReal (80*cap))^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4:ℝ≥0∞) * (ENNReal.ofReal (80*cap))^2 := by
          gcongr
          exact_mod_cast hcard
      _ = ENNReal.ofReal ((160*cap)^2) := by
          rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hcap0)]
          have h4 : (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) := by norm_num
          rw [h4, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
          congr 1
          ring
  have htail : (∑ K ∈ s.filter (fun K => 4*m+4 ≤ K), ‖blockErr m K θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)/2))^2) := by
    set t : Finset ℕ := s.filter (fun K => 4*m+4 ≤ K) with ht
    have hstep : ∀ K ∈ t, ‖blockErr m K θ‖ₑ ^ (2:ℝ)
        ≤ (∑ p ∈ actIdx m (4*m+4) θ,
            ENNReal.ofReal cap * errNorm p.1.1 p.1.2 p.2 K θ)^2 := by
      intro K hK
      have hK4 : 4*m+4 ≤ K := by
        rw [ht, Finset.mem_filter] at hK
        exact hK.2
      rw [ENNReal.rpow_two]
      exact pow_le_pow_left₀
        (by positivity) (blockErr_enorm_le_tail hK4 θ hθ0 hθ1 A (le_of_lt hA0) (hA m)) 2
    calc ∑ K ∈ t, ‖blockErr m K θ‖ₑ ^ (2:ℝ)
        ≤ ∑ K ∈ t, (∑ p ∈ actIdx m (4*m+4) θ,
            ENNReal.ofReal cap * errNorm p.1.1 p.1.2 p.2 K θ)^2 := Finset.sum_le_sum hstep
      _ ≤ ∑' K : ℕ, (∑ p ∈ actIdx m (4*m+4) θ,
            ENNReal.ofReal cap * errNorm p.1.1 p.1.2 p.2 K θ)^2 := ENNReal.sum_le_tsum _
      _ = ∑' K : ℕ, ∑ p ∈ actIdx m (4*m+4) θ,
            (ENNReal.ofReal cap * errNorm p.1.1 p.1.2 p.2 K θ)^2 := by
          refine tsum_congr (fun K => ?_)
          rw [sq_sum_eq_of_card_le_one (actIdx_card_le_one (m := m) (k := 4*m+4) (by omega) θ)]
      _ = ∑ p ∈ actIdx m (4*m+4) θ, ∑' K : ℕ,
            (ENNReal.ofReal cap * errNorm p.1.1 p.1.2 p.2 K θ)^2 := ennreal_tsum_finsetSum _ _
      _ = ∑ p ∈ actIdx m (4*m+4) θ, (ENNReal.ofReal cap)^2 *
            ∑' K : ℕ, (errNorm p.1.1 p.1.2 p.2 K θ)^2 := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun K => by rw [mul_pow])
      _ ≤ ∑ p ∈ actIdx m (4*m+4) θ, (ENNReal.ofReal cap)^2 *
            (∑' K : ℕ, errNorm p.1.1 p.1.2 p.2 K θ)^2 := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact mul_le_mul_right sq_le_tsum_sq _
      _ ≤ (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := by
          have hcard : (actIdx m (4*m+4) θ).card ≤ 1 := actIdx_card_le_one (by omega) θ
          calc ∑ p ∈ actIdx m (4*m+4) θ, (ENNReal.ofReal cap)^2 *
                (∑' K : ℕ, errNorm p.1.1 p.1.2 p.2 K θ)^2
              ≤ ∑ _p ∈ actIdx m (4*m+4) θ,
                  (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := by
                refine Finset.sum_le_sum (fun p hp => ?_)
                exact mul_le_mul_right (pow_le_pow_left₀ (by positivity)
                  (errNorm_tsum_le (le_of_lt hCf0) hCf p.1.1 p.1.2 p.2 θ) 2) _
            _ = ((actIdx m (4*m+4) θ).card : ℝ≥0∞) *
                  ((ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 1 * ((ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2) := by
                gcongr
                exact_mod_cast hcard
            _ = (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := one_mul _
      _ = ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)/2))^2) := by
          rw [hcapdef, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine le_trans (add_le_add htail hsmall) ?_
  calc ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)/2))^2) + ENNReal.ofReal ((160*cap)^2)
      = ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)/2))^2 + (160*cap)^2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((D * (2:ℝ)^(-(m:ℝ)/2))^2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcapdef, hDdef]
        have hs : (0:ℝ) ≤ (2:ℝ)^(-(m:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
        nlinarith [sq_nonneg (A * (2:ℝ)^(-(m:ℝ)/2)), sq_nonneg ((2:ℝ)^(-(m:ℝ)/2)),
          sq_nonneg (Cf * (2:ℝ)^(-(m:ℝ)/2)), le_of_lt hA0, le_of_lt hCf0, hs]



open Commons.Analysis.Fourier (plancherel_circle_enorm_sq sum_intervalIntegral_sq_mul_le
  enorm_complex_pow_two plancherel_trig_polynomial) in
theorem multiplier_square_function_l2' (m : ℕ → ℝ → ℂ) (A : ℝ)
    (hm : ∀ j, Measurable (m j))
    (hb : ∀ j, ∃ C : ℝ, ∀ θ, ‖m j θ‖ ≤ C)
    (hsum : ∀ θ, Summable (fun j : ℕ => ‖m j θ‖ ^ 2) ∧ ∑' j : ℕ, ‖m j θ‖ ^ 2 ≤ A ^ 2)
    (f : ℤ → ℂ) (s : Finset ℤ) (hf : ∀ n, n ∉ s → f n = 0) :
    ∫⁻ m', (∑' j : ℕ, ‖∫ θ in (0:ℝ)..1,
        m j θ * (∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
          * Complex.exp (-(2*Real.pi*Complex.I*(((m':ℤ):ℂ))*(θ:ℂ)))‖ₑ^(2:ℝ))
      ∂MeasureTheory.Measure.count
    ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ n, ‖f n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by

  classical
  set P : ℝ → ℂ := fun θ => ∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))
    with hPdef
  have hPcont : Continuous P := by
    rw [hPdef]
    refine continuous_finsetSum _ (fun n _ => ?_)
    fun_prop
  have hPm : Measurable P := hPcont.measurable
  have hMbound : ∀ θ : ℝ, ‖P θ‖ ≤ ∑ n ∈ s, ‖f n‖ := fun θ => by
    rw [hPdef]
    calc ‖∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖
        ≤ ∑ n ∈ s, ‖f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ s, ‖f n‖ := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          have hexp : ‖Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ = 1 := by
            rw [show 2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)
                  = ((2*Real.pi*(n:ℝ)*θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
            rw [Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, hexp, mul_one]
  have hPb : ∃ M : ℝ, ∀ θ, ‖P θ‖ ≤ M := ⟨_, hMbound⟩
  have hPmem : MemLp P 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound hPm.aestronglyMeasurable (∑ n ∈ s, ‖f n‖) (ae_of_all _ hMbound)
  have hLHS : ∫⁻ m', (∑' j : ℕ, ‖∫ θ in (0:ℝ)..1,
        m j θ * P θ * Complex.exp (-(2*Real.pi*Complex.I*(((m':ℤ):ℂ))*(θ:ℂ)))‖ₑ^(2:ℝ))
      ∂MeasureTheory.Measure.count
      = ∑' j : ℕ, ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2) := by
    rw [lintegral_count, ENNReal.tsum_comm]
    refine tsum_congr (fun j => ?_)
    exact plancherel_circle_enorm_sq (m j) P (hm j) (hb j) hPmem
  rw [hLHS]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun t => ?_)
  have hI0 : ∀ j, 0 ≤ ∫ θ in (0:ℝ)..1, ‖m j θ‖ ^ 2 * ‖P θ‖ ^ 2 := fun j =>
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by positivity)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hI0 j)]
  refine le_trans (ENNReal.ofReal_le_ofReal
    (sum_intervalIntegral_sq_mul_le m A hm hb hsum P hPm hPb t)) ?_
  rw [ENNReal.ofReal_mul (sq_nonneg A)]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  have hplanch : ∫ θ in (0:ℝ)..1, ‖P θ‖ ^ 2 = ∑ n ∈ s, ‖f n‖ ^ 2 := by
    rw [hPdef]
    exact (plancherel_trig_polynomial s f).symm
  rw [hplanch, ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg _)]
  calc ∑ n ∈ s, ENNReal.ofReal (‖f n‖ ^ 2)
      = ∑ n ∈ s, ‖f n‖ₑ ^ (2:ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [enorm_complex_pow_two]
    _ ≤ ∑' n : ℤ, ‖f n‖ₑ ^ (2:ℝ) := ENNReal.sum_le_tsum s
    _ = ∫⁻ n, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        (lintegral_count (fun n : ℤ => ‖f n‖ₑ ^ (2:ℝ))).symm

/-- The profile error of the `m`-th block, as a multiplier on `(0,1)` (extended by `0`). -/
noncomputable def errMult (m K : ℕ) (θ : ℝ) : ℂ :=
  if 0 < θ ∧ θ < 1 then blockErr m K θ else 0

lemma measurable_blockCore (m k : ℕ) : Measurable (fun θ : ℝ => blockCore m k θ) := by
  unfold blockCore
  refine Finset.measurable_sum _ (fun i hi => ?_)
  refine Finset.measurable_sum _ (fun l hl => ?_)
  refine Measurable.mul measurable_const ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (by fun_prop) measurable_const

lemma measurable_blockErr (m K : ℕ) : Measurable (fun θ : ℝ => blockErr m K θ) := by
  unfold blockErr
  refine Measurable.sub ?_ ?_
  · exact Complex.continuous_conj.measurable.comp (measurable_modelQBlock m (2^K))
  · by_cases h4 : 4*m+4 ≤ K
    · simpa [h4] using measurable_blockCore m K
    · simpa [h4] using measurable_const (a := (0:ℂ))

lemma measurable_errMult (m K : ℕ) : Measurable (errMult m K) := by
  unfold errMult
  refine Measurable.ite ?_ (measurable_blockErr m K) measurable_const
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_id measurable_const)

lemma hxy_ennreal (x y : ℝ≥0∞) : x * y ≤ x^2 + y^2 := by
  rcases le_total x y with h | h
  · calc x * y ≤ y * y := by gcongr
      _ = y^2 := by ring
      _ ≤ x^2 + y^2 := by simp
  · calc x * y ≤ x * x := by gcongr
      _ = x^2 := by ring
      _ ≤ x^2 + y^2 := by simp

lemma sq_iSup_le_two_tsum_sq {a : ℕ → ℝ≥0∞} : (⨆ i, a i)^2 ≤ 2 * ∑' i, a i^2 := by
  have hterm : ∀ i j : ℕ, a i * a j ≤ 2 * ∑' k, a k^2 := by
    intro i j
    have hi : a i ^ 2 ≤ ∑' k, a k ^ 2 := ENNReal.le_tsum (f := fun k => a k ^ 2) i
    have hj : a j ^ 2 ≤ ∑' k, a k ^ 2 := ENNReal.le_tsum (f := fun k => a k ^ 2) j
    calc a i * a j ≤ a i^2 + a j^2 := hxy_ennreal _ _
      _ ≤ (∑' k, a k^2) + (∑' k, a k^2) := add_le_add hi hj
      _ = 2 * ∑' k, a k^2 := by ring
  calc (⨆ i, a i)^2 = (⨆ i, a i) * (⨆ j, a j) := by rw [pow_two]
    _ = ⨆ i, a i * (⨆ j, a j) := ENNReal.iSup_mul _ _
    _ = ⨆ i, ⨆ j, a i * a j := by simp only [ENNReal.mul_iSup]
    _ ≤ 2 * ∑' k, a k^2 := iSup_le fun i => iSup_le fun j => hterm i j

/-- **Bourgain (6.23), summability form**: for every `θ` the profile errors of the `m`-th block form
a square-summable family in the scale with sum bounded by `(A(160+Cf)2^{-m/2})²`. -/
lemma errMult_hsum (A Cf : ℝ) (hA0 : 0 < A) (hCf0 : 0 < Cf)
    (hA : ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2))
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, errVal x k) ≤ Cf)
    (m : ℕ) (θ : ℝ) :
    Summable (fun K : ℕ => ‖errMult m K θ‖ ^ 2) ∧
      (∑' K : ℕ, ‖errMult m K θ‖ ^ 2) ≤ (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2 := by
  by_cases hθ : 0 < θ ∧ θ < 1
  · have hmain := blockErr_tsum_sq_le A Cf hA0 hCf0 hA hCf m θ hθ.1 hθ.2
    have hE0 : (0:ℝ) ≤ (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2 := by positivity
    have hfin : ∀ t : Finset ℕ,
        ∑ K ∈ t, ‖blockErr m K θ‖ ^ 2 ≤ (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2 := by
      intro t
      have h1 : ∑ K ∈ t, ‖blockErr m K θ‖ₑ ^ (2:ℝ)
          ≤ ENNReal.ofReal ((A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2) :=
        le_trans (ENNReal.sum_le_tsum t) hmain
      rw [Finset.sum_congr rfl (fun K hK =>
        Commons.Analysis.Fourier.enorm_complex_pow_two (blockErr m K θ))] at h1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun K hK => sq_nonneg _)] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hE0).mp h1
    have heq : ∀ K, errMult m K θ = blockErr m K θ := fun K => by rw [errMult, if_pos hθ]
    constructor
    · simpa only [heq] using summable_of_sum_range_le (fun K => sq_nonneg _)
        (fun n => by simpa using hfin (Finset.range n))
    · simpa only [heq] using Real.tsum_le_of_sum_range_le (fun K => sq_nonneg _)
        (fun n => by simpa using hfin (Finset.range n))
  · have hz : ∀ K, errMult m K θ = 0 := fun K => by rw [errMult, if_neg hθ]
    constructor
    · simpa [hz] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    · have hz' : (∑' K : ℕ, ‖errMult m K θ‖ ^ 2) = 0 := by simp [hz]
      rw [hz']
      exact sq_nonneg _


lemma norm_blockCore_le (m k : ℕ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m → ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2))
    (θ : ℝ) :
    ‖blockCore m k θ‖ ≤ ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
  rw [blockCore_eq_sum_sharpTerm]
  rw [show (∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (sharpTerm i.1 i.2 l k θ))
      = ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (sharpTerm p.1.1 p.1.2 p.2 k θ) from
    (Finset.sum_product (blockPair m) (Finset.Icc (-2:ℤ) 2)
      (fun p : (ℕ × ℕ) × ℤ => starRingEnd ℂ (sharpTerm p.1.1 p.1.2 p.2 k θ))).symm]
  calc ‖∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (sharpTerm p.1.1 p.1.2 p.2 k θ)‖
      ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
          ‖starRingEnd ℂ (sharpTerm p.1.1 p.1.2 p.2 k θ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2, ‖blockGaussWeight p.1.1 p.1.2‖ := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp1 : p.1 ∈ blockPair m := (Finset.mem_product.mp hp).1
        rw [Complex.norm_conj, sharpTerm, norm_mul]
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        split_ifs <;> simp
    _ ≤ ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
        rw [allIdx]
        calc ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2, ‖blockGaussWeight p.1.1 p.1.2‖
            ≤ ∑ _p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2, (A * (2:ℝ)^(-(m:ℝ)/2)) :=
              Finset.sum_le_sum (fun p hp => hA p.1 (Finset.mem_product.mp hp).1)
          _ = ((blockPair m ×ˢ Finset.Icc (-2:ℤ) 2).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]

lemma norm_blockErr_le_generic {m K : ℕ} (hk : 4*m ≤ K) (θ : ℝ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m → ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2)) :
    ‖blockErr m K θ‖ ≤ (80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
  have hc : 0 ≤ A * (2:ℝ)^(-(m:ℝ)/2) := by positivity
  have hcard : (0:ℝ) ≤ ((allIdx m).card : ℝ) := by positivity
  rw [blockErr]
  by_cases h4 : 4*m+4 ≤ K
  · rw [if_pos h4]
    refine le_trans (norm_sub_le _ _) ?_
    calc ‖starRingEnd ℂ (modelQBlock m (2^K) θ)‖ + ‖blockCore m K θ‖
        ≤ 80 * (A * (2:ℝ)^(-(m:ℝ)/2)) + ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)/2)) :=
          add_le_add (norm_star_modelQBlock_le_cap hk θ A hA0 hA) (norm_blockCore_le m K A hA0 hA θ)
      _ = (80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)/2)) := by ring
  · rw [if_neg h4, sub_zero]
    refine le_trans (norm_star_modelQBlock_le_cap hk θ A hA0 hA) ?_
    calc 80 * (A * (2:ℝ)^(-(m:ℝ)/2))
        ≤ (80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)/2)) := by
          exact mul_le_mul_of_nonneg_right (by linarith) hc

/-- **Bourgain (6.23), maximal form**: the profile errors of the `m`-th dyadic block are an `ℓ²`
maximal family with constant `2(A(160+Cf)2^{-m/2})²`. -/
theorem errMult_maximal_le (A Cf : ℝ) (hA0 : 0 < A) (hCf0 : 0 < Cf)
    (hA : ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2))
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, errVal x k) ≤ Cf)
    (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (hgs : ∀ n, n ∉ s → g n = 0) :
    ∫⁻ x : ℤ, (⨆ K : ℕ, ‖∫ θ in (0:ℝ)..1, errMult m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  set E : ℝ := A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hbound : ∀ K : ℕ, ∃ C : ℝ, ∀ θ : ℝ, ‖errMult m K θ‖ ≤ C := by
    intro K
    by_cases hk : 4*m ≤ K
    · refine ⟨(80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)/2)), fun θ => ?_⟩
      by_cases hθ : 0 < θ ∧ θ < 1
      · rw [errMult, if_pos hθ]
        exact norm_blockErr_le_generic hk θ A (le_of_lt hA0) (hA m)
      · rw [errMult, if_neg hθ, norm_zero]; positivity
    · refine ⟨1, fun θ => ?_⟩
      by_cases hθ : 0 < θ ∧ θ < 1
      · rw [errMult, if_pos hθ, blockErr, if_neg (by omega : ¬ 4*m+4 ≤ K), sub_zero,
          modelQBlock_eq_zero_of_lt (by omega : K < 4*m), map_zero, norm_zero]
        norm_num
      · rw [errMult, if_neg hθ, norm_zero]; norm_num
  have hsum : ∀ θ, Summable (fun K : ℕ => ‖errMult m K θ‖ ^ 2) ∧
      ∑' K : ℕ, ‖errMult m K θ‖ ^ 2 ≤ E ^ 2 := fun θ => by
    rw [hEdef]; exact errMult_hsum A Cf hA0 hCf0 hA hCf m θ
  have hsquare := multiplier_square_function_l2' (fun K => errMult m K) E
    (fun K => measurable_errMult m K) hbound hsum g s hgs
  rw [hEdef] at hsquare ⊢
  calc ∫⁻ x : ℤ, (⨆ K : ℕ, ‖∫ θ in (0:ℝ)..1, errMult m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, 2 * ∑' K : ℕ, ‖∫ θ in (0:ℝ)..1, errMult m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => by
          simp only [ENNReal.rpow_two]
          exact sq_iSup_le_two_tsum_sq)
    _ = 2 * ∫⁻ x : ℤ, ∑' K : ℕ, ‖∫ θ in (0:ℝ)..1, errMult m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        lintegral_const_mul' 2 _ (by norm_num)
    _ ≤ 2 * (ENNReal.ofReal ((A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
        mul_le_mul_right hsquare 2
    _ = ENNReal.ofReal (2 * (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
        rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]



open Classical

/-- The periodised indicator of the `r`-neighbourhood of a real frequency `lam`. -/
noncomputable def perNbhd (lam r : ℝ) (θ : ℝ) : ℂ :=
  if ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r then 1 else 0

/-- The indicator of the union of the periodised `r`-neighbourhoods of the frequencies of `T`. -/
noncomputable def unNbhd (T : Finset (ℝ × ℂ)) (r : ℝ) (θ : ℝ) : ℂ :=
  if ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r then 1 else 0

/-- The *fixed* weighted profile attached to `T` at radius `δ/3`. -/
noncomputable def coreW (T : Finset (ℝ × ℂ)) (δ : ℝ) (θ : ℝ) : ℂ :=
  ∑ p ∈ T, p.2 * perNbhd p.1 (δ/3) θ

lemma perNbhd_eq_one {lam r θ : ℝ} :
    perNbhd lam r θ = 1 ↔ ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r := by
  rw [perNbhd]
  by_cases h : ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r <;> simp [h]

lemma perNbhd_eq_zero {lam r θ : ℝ} (h : perNbhd lam r θ = 0) :
    ¬ ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r := by
  by_contra hh
  rw [perNbhd, if_pos hh] at h
  exact one_ne_zero h

lemma unNbhd_eq_one {T : Finset (ℝ × ℂ)} {r θ : ℝ} :
    unNbhd T r θ = 1 ↔ ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r := by
  rw [unNbhd]
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r <;> simp [h]

lemma unNbhd_eq_zero {T : Finset (ℝ × ℂ)} {r θ : ℝ} (h : unNbhd T r θ = 0) :
    ¬ ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r := by
  by_contra hh
  rw [unNbhd, if_pos hh] at h
  exact one_ne_zero h

lemma perNbhd_mono {lam r r' θ : ℝ} (h : r ≤ r') (h1 : perNbhd lam r θ = 1) :
    perNbhd lam r' θ = 1 := by
  rw [perNbhd_eq_one] at h1 ⊢
  obtain ⟨l, hl⟩ := h1
  exact ⟨l, le_trans hl h⟩

lemma perNbhd_nonneg (lam r θ : ℝ) : 0 ≤ (perNbhd lam r θ).re := by
  rw [perNbhd]; split <;> simp

lemma perNbhd_ne_zero {lam r θ : ℝ} (h : perNbhd lam r θ ≠ 0) : perNbhd lam r θ = 1 := by
  rw [perNbhd] at h ⊢
  by_cases hh : ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r <;> simp [hh] at h ⊢

/-- **The fixed-multiplier identity.**  If the frequencies of `T` are periodically `δ`-separated
and `r ≤ δ/3`, then the weighted sum of the `r`-neighbourhood indicators equals the fixed profile
`coreW T δ` times the indicator of the union. -/
lemma coreW_mul_unNbhd (T : Finset (ℝ × ℂ)) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ l : ℤ, δ ≤ |p.1 - q.1 + (l:ℝ)|)
    {r : ℝ} (hr : r ≤ δ/3) (θ : ℝ) :
    coreW T δ θ * unNbhd T r θ = ∑ p ∈ T, p.2 * perNbhd p.1 r θ := by
  have hsub : ∀ (p : ℝ × ℂ), perNbhd p.1 r θ = 1 → perNbhd p.1 (δ/3) θ = 1 :=
    fun p => perNbhd_mono hr
  have huniq : ∀ (p : ℝ × ℂ), p ∈ T → ∀ (q : ℝ × ℂ), q ∈ T →
      perNbhd p.1 (δ/3) θ = 1 → perNbhd q.1 (δ/3) θ = 1 → p = q := by
    intro p hp q hq hp1 hq1
    by_contra hne
    obtain ⟨l, hl⟩ := (perNbhd_eq_one.mp hp1)
    obtain ⟨l', hl'⟩ := (perNbhd_eq_one.mp hq1)
    have hkey : |p.1 - q.1 + ((l' - l : ℤ):ℝ)| ≤ 2 * (δ/3) := by
      have h1 : p.1 - q.1 + ((l' - l : ℤ):ℝ)
          = -(θ + (l:ℝ) - p.1) + (θ + (l':ℝ) - q.1) := by push_cast; ring
      rw [h1]
      calc |-(θ + (l:ℝ) - p.1) + (θ + (l':ℝ) - q.1)|
          ≤ |-(θ + (l:ℝ) - p.1)| + |θ + (l':ℝ) - q.1| := abs_add_le _ _
        _ = |θ + (l:ℝ) - p.1| + |θ + (l':ℝ) - q.1| := by rw [abs_neg]
        _ ≤ δ/3 + δ/3 := add_le_add hl hl'
        _ = 2 * (δ/3) := by ring
    have hsep' := hsep p hp q hq hne (l' - l)
    have : (2:ℝ) * (δ/3) < δ := by linarith
    linarith
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r
  · obtain ⟨p₀, hp₀T, l₀, hl₀⟩ := h
    have hp₀ : perNbhd p₀.1 r θ = 1 := perNbhd_eq_one.mpr ⟨l₀, hl₀⟩
    have hun : unNbhd T r θ = 1 := unNbhd_eq_one.mpr ⟨p₀, hp₀T, l₀, hl₀⟩
    have hother : ∀ (q : ℝ × ℂ), q ∈ T → q ≠ p₀ → perNbhd q.1 r θ = 0 := by
      intro q hq hqne
      have hq0 : ¬ ∃ l : ℤ, |θ + (l:ℝ) - q.1| ≤ r := by
        rintro ⟨l, hl⟩
        have h1 : perNbhd q.1 (δ/3) θ = 1 := hsub q (perNbhd_eq_one.mpr ⟨l, hl⟩)
        exact hqne (huniq q hq p₀ hp₀T h1 (hsub p₀ hp₀))
      rw [perNbhd]; simp only [hq0, if_false]
    have hsub2 : ∀ (q : ℝ × ℂ), q ∈ T → q ≠ p₀ → perNbhd q.1 (δ/3) θ = 0 := by
      intro q hq hqne
      have hq0 : ¬ ∃ l : ℤ, |θ + (l:ℝ) - q.1| ≤ δ/3 := by
        rintro ⟨l, hl⟩
        have h1 : perNbhd q.1 (δ/3) θ = 1 := perNbhd_eq_one.mpr ⟨l, hl⟩
        exact hqne (huniq q hq p₀ hp₀T h1 (hsub p₀ hp₀))
      rw [perNbhd]; simp only [hq0, if_false]
    have hW : coreW T δ θ = p₀.2 := by
      rw [coreW, Finset.sum_eq_single p₀]
      · rw [hsub p₀ hp₀, mul_one]
      · intro q hq hqne
        rw [hsub2 q hq hqne, mul_zero]
      · intro hnot; exact absurd hp₀T hnot
    have hR : (∑ p ∈ T, p.2 * perNbhd p.1 r θ) = p₀.2 := by
      rw [Finset.sum_eq_single p₀]
      · rw [hp₀, mul_one]
      · intro q hq hqne; rw [hother q hq hqne, mul_zero]
      · intro hnot; exact absurd hp₀T hnot
    rw [hW, hun, hR, mul_one]
  · have h0 : unNbhd T r θ = 0 := by rw [unNbhd]; simp only [h, if_false]
    have hz : ∀ (p : ℝ × ℂ), p ∈ T → perNbhd p.1 r θ = 0 := by
      intro p hp
      have hh : ¬ ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r := fun ⟨l, hl⟩ => h ⟨p, hp, l, hl⟩
      rw [perNbhd]; simp only [hh, if_false]
    rw [h0, mul_zero]
    exact (Finset.sum_eq_zero (f := fun p : ℝ × ℂ => p.2 * perNbhd p.1 r θ)
      (fun p hp => by rw [hz p hp, mul_zero])).symm


/-- **The circle-form neighbourhood maximal for a finite frequency set** (Bourgain's Lemma 4.1 in
circle form, applied to arbitrary `L²((0,1))` functions).  This is the hypothesis consumed by the
fixed-multiplier step; it follows from the ℝ-line band-pass maximal via
`Commons.Analysis.Fourier.periodic_neighborhood_of_real_line_bandpass` + density. -/
def CircleNeighborhoodMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (ℝ × ℂ)) (Q : ℝ → ℂ),
    MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) →
    ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
      ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C * Real.log ((T.card:ℝ)+2)^2)^2) *
        ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ)

lemma measurable_perNbhd (lam r : ℝ) : Measurable (perNbhd lam r) := by
  rw [show perNbhd lam r = fun θ : ℝ =>
      if ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r then (1:ℂ) else 0 from rfl]
  refine Measurable.ite ?_ measurable_const measurable_const
  rw [show {θ : ℝ | ∃ l : ℤ, |θ + (l:ℝ) - lam| ≤ r}
      = ⋃ l : ℤ, {θ : ℝ | |θ + (l:ℝ) - lam| ≤ r} from by ext θ; simp]
  exact MeasurableSet.iUnion (fun l => measurableSet_le (by fun_prop) measurable_const)

lemma measurable_unNbhd (T : Finset (ℝ × ℂ)) (r : ℝ) : Measurable (unNbhd T r) := by
  rw [show unNbhd T r = fun θ : ℝ =>
      if ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r then (1:ℂ) else 0 from rfl]
  refine Measurable.ite ?_ measurable_const measurable_const
  rw [show {θ : ℝ | ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r}
      = ⋃ p ∈ T, ⋃ l : ℤ, {θ : ℝ | |θ + (l:ℝ) - p.1| ≤ r} from by
    ext θ; simp [Set.mem_iUnion, exists_prop]]
  exact MeasurableSet.biUnion T.countable_toSet
    (fun p hp => MeasurableSet.iUnion (fun l => measurableSet_le (by fun_prop) measurable_const))

lemma measurable_coreW (T : Finset (ℝ × ℂ)) (δ : ℝ) : Measurable (coreW T δ) := by
  rw [show coreW T δ = fun θ : ℝ => ∑ p ∈ T, p.2 * perNbhd p.1 (δ/3) θ from rfl]
  exact Finset.measurable_sum _ (fun p hp => measurable_const.mul (measurable_perNbhd _ _))

/-- At scale `δ/3` at most one frequency of `T` is active, hence `‖coreW T δ θ‖ ≤ cap`. -/
lemma norm_coreW_le (T : Finset (ℝ × ℂ)) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ l : ℤ, δ ≤ |p.1 - q.1 + (l:ℝ)|)
    {cap : ℝ} (hcap0 : 0 ≤ cap) (hcap : ∀ p ∈ T, ‖p.2‖ ≤ cap) (θ : ℝ) :
    ‖coreW T δ θ‖ ≤ cap := by
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ δ/3
  · obtain ⟨p₀, hp₀T, l₀, hl₀⟩ := h
    have hp₀ : perNbhd p₀.1 (δ/3) θ = 1 := perNbhd_eq_one.mpr ⟨l₀, hl₀⟩
    have huniq : ∀ (q : ℝ × ℂ), q ∈ T → perNbhd q.1 (δ/3) θ = 1 → q = p₀ := by
      intro q hq hq1
      by_contra hne
      obtain ⟨l', hl'⟩ := (perNbhd_eq_one.mp hq1)
      have hkey : |q.1 - p₀.1 + ((l₀ - l' : ℤ):ℝ)| ≤ 2 * (δ/3) := by
        have h1 : q.1 - p₀.1 + ((l₀ - l' : ℤ):ℝ)
            = -(θ + (l':ℝ) - q.1) + (θ + (l₀:ℝ) - p₀.1) := by push_cast; ring
        rw [h1]
        calc |-(θ + (l':ℝ) - q.1) + (θ + (l₀:ℝ) - p₀.1)|
            ≤ |-(θ + (l':ℝ) - q.1)| + |θ + (l₀:ℝ) - p₀.1| := abs_add_le _ _
          _ = |θ + (l':ℝ) - q.1| + |θ + (l₀:ℝ) - p₀.1| := by rw [abs_neg]
          _ ≤ δ/3 + δ/3 := add_le_add hl' hl₀
          _ = 2 * (δ/3) := by ring
      have hsep' := hsep q hq p₀ hp₀T hne (l₀ - l')
      have : (2:ℝ) * (δ/3) < δ := by linarith
      linarith
    have hW : coreW T δ θ = p₀.2 := by
      rw [show coreW T δ θ = ∑ p ∈ T, p.2 * perNbhd p.1 (δ/3) θ from rfl,
        Finset.sum_eq_single p₀]
      · rw [hp₀, mul_one]
      · intro q hq hqne
        have hq0 : perNbhd q.1 (δ/3) θ = 0 := by
          by_contra hc
          exact hqne (huniq q hq (perNbhd_ne_zero hc))
        rw [hq0, mul_zero]
      · intro hnot; exact absurd hp₀T hnot
    rw [hW]; exact hcap p₀ hp₀T
  · have hz : ∀ (p : ℝ × ℂ), p ∈ T → perNbhd p.1 (δ/3) θ = 0 := by
      intro p hp
      have hh : ¬ ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ δ/3 := fun ⟨l, hl⟩ => h ⟨p, hp, l, hl⟩
      rw [perNbhd]; simp only [hh, if_false]
    rw [show coreW T δ θ = ∑ p ∈ T, p.2 * perNbhd p.1 (δ/3) θ from rfl,
      Finset.sum_eq_zero (f := fun p : ℝ × ℂ => p.2 * perNbhd p.1 (δ/3) θ)
        (fun p hp => by rw [hz p hp, mul_zero]), norm_zero]
    exact hcap0

/-- **The weighted core maximal.**  From the circle-form neighbourhood maximal, the weighted
periodised-neighbourhood family of a periodically separated frequency set is an `ℓ²` maximal
family, with constant `C·cap·(log |T|)²`. -/
theorem weighted_core_maximal (H : CircleNeighborhoodMaximal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (ℝ × ℂ)) (cap δ : ℝ), 0 < δ → 0 ≤ cap →
      (∀ p ∈ T, ‖p.2‖ ≤ cap) →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ l : ℤ, δ ≤ |p.1 - q.1 + (l:ℝ)|) →
      ∀ (j₀ : ℕ), (0:ℝ) < (2:ℝ)^(-(j₀:ℝ)-1) → (2:ℝ)^(-(j₀:ℝ)-1) ≤ δ/3 →
      ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
          (if j₀ ≤ j then ∑ p ∈ T, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0) *
          (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * cap * Real.log ((T.card:ℝ)+2)^2)^2) *
          ∫⁻ n : ℤ, ‖g n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := H
  refine ⟨C₀, hC₀pos, fun T cap δ hδ hcap0 hcap hsep j₀ hj₀ hj₀δ g s hgs => ?_⟩
  set W : ℝ → ℂ := coreW T δ with hWdef
  set χ : ℕ → ℝ → ℂ :=
    fun j θ => if j₀ ≤ j then unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ else 0 with hχ
  have hWbd : ∀ θ, ‖W θ‖ ≤ cap := fun θ => by
    rw [hWdef]; exact norm_coreW_le T δ hδ hsep hcap0 hcap θ
  have hWm : Measurable W := measurable_coreW T δ
  have hr_le : ∀ j : ℕ, j₀ ≤ j → (2:ℝ)^(-(j:ℝ)-1) ≤ δ/3 := by
    intro j hj
    refine le_trans ?_ hj₀δ
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (j₀:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    linarith
  have hmax : ∀ Q : ℝ → ℂ, MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1, χ j θ * Q θ *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C₀ * Real.log ((T.card:ℝ)+2)^2)^2) *
          ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ) := by
    intro Q hQ
    refine le_trans (lintegral_mono (fun m => ?_)) (hC₀ T Q hQ)
    refine ENNReal.rpow_le_rpow (iSup_le (fun j => ?_)) (by norm_num)
    by_cases hj : j₀ ≤ j
    · rw [hχ]
      simp only [hj, if_true]
      exact le_iSup (f := fun (j : ℕ) => ‖∫ θ in (0:ℝ)..1,
        unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ) j
    · rw [hχ]
      simp only [hj, if_false, zero_mul]
      simp
  have hpoint : ∀ (j : ℕ) (θ : ℝ), W θ * χ j θ =
      (if j₀ ≤ j then ∑ p ∈ T, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0) := by
    intro j θ
    by_cases hj : j₀ ≤ j
    · rw [hWdef, hχ]
      simp only [hj, if_true]
      exact coreW_mul_unNbhd T δ hδ hsep (hr_le j hj) θ
    · rw [hWdef, hχ]
      simp only [hj, if_false, mul_zero]
  have hfm := maximal_l2_of_fixed_multiplier χ W (C₀ * Real.log ((T.card:ℝ)+2)^2) cap
    (by positivity) hcap0 hmax hWm hWbd g s hgs
  have heq : (∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1, W θ * χ j θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count)
      = ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
          (if j₀ ≤ j then ∑ p ∈ T, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0) *
          (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count := by
    refine lintegral_congr (fun m => ?_)
    congr 1
    refine iSup_congr (fun j => ?_)
    congr 1
    refine intervalIntegral.integral_congr (fun θ hθ => ?_)
    rw [hpoint j θ]
  calc ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
          (if j₀ ≤ j then ∑ p ∈ T, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0) *
          (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count
      = ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1, W θ * χ j θ *
          (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count :=
        heq.symm
    _ ≤ ENNReal.ofReal ((C₀ * Real.log ((T.card:ℝ)+2)^2)^2 * cap^2) *
          ∫⁻ m : ℤ, ‖g m‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := hfm
    _ = ENNReal.ofReal ((C₀ * cap * Real.log ((T.card:ℝ)+2)^2)^2) *
          ∫⁻ m : ℤ, ‖g m‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
        congr 1
        congr 1
        ring



/-- The (frequency, weight) pairs of the `m`-th dyadic `q`-block. -/
noncomputable def blockT (m : ℕ) : Finset (ℝ × ℂ) :=
  (blockPair m).image (fun i : ℕ × ℕ => ((i.2:ℝ)/(i.1:ℝ), starRingEnd ℂ (blockGaussWeight i.1 i.2)))

lemma blockT_injOn (m : ℕ) :
    ∀ i ∈ blockPair m, ∀ i' ∈ blockPair m,
      ((i.2:ℝ)/(i.1:ℝ), starRingEnd ℂ (blockGaussWeight i.1 i.2))
        = ((i'.2:ℝ)/(i'.1:ℝ), starRingEnd ℂ (blockGaussWeight i'.1 i'.2)) → i = i' := by
  intro i hi i' hi' heq
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hi'
  have hfr : (i.2:ℝ)/(i.1:ℝ) = (i'.2:ℝ)/(i'.1:ℝ) := congrArg Prod.fst heq
  have hq1 : 0 < i.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq2 : 0 < i'.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  obtain ⟨hqeq, haeq⟩ := frac_eq_of_coprime hq1 hq2
    (Nat.coprime_iff_gcd_eq_one.mpr h4) (Nat.coprime_iff_gcd_eq_one.mpr h4') h3 h3' hfr
  exact Prod.ext hqeq haeq

lemma blockPair_card_le (m : ℕ) : (blockPair m).card ≤ 2^(2*m+1) := by
  rw [blockPair]
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        (((Finset.range q).filter (fun a => Nat.gcd a q = 1)).image (fun a => (q, a))).card
      ≤ ∑ q ∈ Finset.Ico (2^m) (2^(m+1)), q := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        refine le_trans Finset.card_image_le ?_
        refine le_trans (Finset.card_filter_le _ _) ?_
        rw [Finset.card_range]
    _ ≤ ∑ _q ∈ Finset.Ico (2^m) (2^(m+1)), 2^(m+1) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        exact le_of_lt (Finset.mem_Ico.mp hq).2
    _ = 2^(2*m+1) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Ico]
        have hsub : 2^(m+1) - 2^m = 2^m := by
          rw [pow_succ]
          omega
        rw [hsub, ← pow_add]
        congr 1
        omega

lemma blockT_card_le (m : ℕ) : (blockT m).card ≤ 2^(2*m+1) := by
  rw [blockT]
  exact le_trans Finset.card_image_le (blockPair_card_le m)

lemma log_blockT_le (m : ℕ) : Real.log (((blockT m).card : ℝ) + 2) ≤ 2 * ((m:ℝ) + 2) := by
  have hcard : (((blockT m).card : ℕ) : ℝ) ≤ (2:ℝ)^(2*m+1) := by
    have h := blockT_card_le m
    push_cast [← Nat.cast_pow]
    exact_mod_cast h
  have h2 : ((blockT m).card : ℝ) + 2 ≤ (2:ℝ)^(2*m+2) := by
    have hpos : (1:ℝ) ≤ (2:ℝ)^(2*m+1) := one_le_pow₀ (by norm_num)
    calc ((blockT m).card : ℝ) + 2 ≤ (2:ℝ)^(2*m+1) + 2 := by linarith
      _ ≤ (2:ℝ)^(2*m+1) + (2:ℝ)^(2*m+1) := by
          have : (2:ℝ) ≤ (2:ℝ)^(2*m+1) := by
            calc (2:ℝ) = (2:ℝ)^1 := (pow_one 2).symm
              _ ≤ (2:ℝ)^(2*m+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
          linarith
      _ = 2 * (2:ℝ)^(2*m+1) := by ring
      _ = (2:ℝ)^(2*m+2) := by
          rw [show (2:ℝ)^(2*m+2) = (2:ℝ)^(2*m+1) * 2 from by
            rw [show (2*m+2 : ℕ) = (2*m+1)+1 by omega, pow_succ]]
          ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  calc Real.log (((blockT m).card : ℝ) + 2) ≤ Real.log ((2:ℝ)^(2*m+2)) :=
        Real.log_le_log (by positivity) h2
    _ = ((2*m+2 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (2*m+2)
    _ ≤ 2 * ((m:ℝ) + 2) := by
        have hlog2nn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h4 : (0:ℝ) ≤ ((2*m+2 : ℕ) : ℝ) := by positivity
        have h5 : ((2*m+2 : ℕ) : ℝ) * Real.log 2 ≤ ((2*m+2 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 h4
        push_cast at h5 ⊢
        linarith

/-- The sharp core is the weighted periodised-neighbourhood family of `blockT m` at radius
`4^{-k}`. -/
lemma blockCore_eq_weighted {m k : ℕ} (hk : 1 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    blockCore m k θ = ∑ p ∈ blockT m, p.2 * perNbhd p.1 ((4:ℝ)^(-(k:ℝ))) θ := by
  rw [blockCore_eq_periodic m k hk θ hθ0 hθ1, blockCorePer, blockT]
  rw [Finset.sum_image (blockT_injOn m)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [perNbhd]

/-- Two distinct block frequencies never differ by an integer. -/
lemma blockT_freq_ne_zero {m : ℕ} {i i' : ℕ × ℕ} (hi : i ∈ blockPair m) (hi' : i' ∈ blockPair m)
    (hne : i ≠ i') (l : ℤ) : (i.2:ℝ)/i.1 - (i'.2:ℝ)/i'.1 + (l:ℝ) ≠ 0 := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hi'
  have hq1 : 0 < i.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq2 : 0 < i'.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  have b1 : (0:ℝ) ≤ (i.2:ℝ)/i.1 := by positivity
  have b1' : (i.2:ℝ)/i.1 < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast h3
  have b2 : (0:ℝ) ≤ (i'.2:ℝ)/i'.1 := by positivity
  have b2' : (i'.2:ℝ)/i'.1 < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast h3'
  have hlt1 : (l:ℝ) < 1 := by linarith
  have hgt1 : (-1:ℝ) < (l:ℝ) := by linarith
  have hl0 : l = 0 := by
    have h2'' : l < (1:ℤ) := by exact_mod_cast hlt1
    have h1'' : (-1:ℤ) < l := by exact_mod_cast hgt1
    omega
  rw [hl0] at h
  simp only [Int.cast_zero, add_zero] at h
  have hfr : (i.2:ℝ)/i.1 = (i'.2:ℝ)/i'.1 := by linarith
  obtain ⟨hqeq, haeq⟩ := frac_eq_of_coprime hq1 hq2
    (Nat.coprime_iff_gcd_eq_one.mpr h4) (Nat.coprime_iff_gcd_eq_one.mpr h4') h3 h3' hfr
  exact hne (Prod.ext hqeq haeq)

/-- The frequencies of `blockT m` are periodically `4^{-m-1}`-separated. -/
lemma blockT_sep (m : ℕ) : ∀ p ∈ blockT m, ∀ q ∈ blockT m, p ≠ q →
    ∀ l : ℤ, (4:ℝ)^(-(m:ℝ)-1) ≤ |p.1 - q.1 + (l:ℝ)| := by
  intro p hp q hq hpq l
  rw [blockT, Finset.mem_image] at hp hq
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨i', hi', rfl⟩ := hq
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hi'
  have hq1 : 0 < i.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq2 : 0 < i'.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  have hii : i ≠ i' := by
    intro heq
    exact hpq (by rw [heq])
  have hne : (i.2:ℝ)/i.1 + ((0:ℤ):ℝ) ≠ (i'.2:ℝ)/i'.1 + (((-l : ℤ)):ℝ) := by
    intro hcontra
    refine blockT_freq_ne_zero hi hi' hii l ?_
    push_cast at hcontra
    linarith
  have hsep := majorArc_shift_sep (q₁ := i.1) (q₂ := i'.1) (a₁ := i.2) (a₂ := i'.2)
    (l₁ := 0) (l₂ := -l) hq1 hq2 hne
  simp only [Int.cast_zero, Int.cast_neg, add_zero] at hsep
  have hqq : (4:ℝ)^(-(m:ℝ)-1) ≤ ((i.1:ℝ)*(i'.1:ℝ))⁻¹ := by
    have hq1' : (i.1:ℝ) < (2:ℝ)^(m+1) := by exact_mod_cast h2
    have hq2' : (i'.1:ℝ) < (2:ℝ)^(m+1) := by exact_mod_cast h2'
    have hprod : (i.1:ℝ)*(i'.1:ℝ) ≤ (4:ℝ)^(m+1) := by
      rw [show (4:ℝ)^(m+1) = (2:ℝ)^(m+1) * (2:ℝ)^(m+1) by rw [← mul_pow]; norm_num]
      exact mul_le_mul hq1'.le hq2'.le (by positivity) (by positivity)
    calc (4:ℝ)^(-(m:ℝ)-1) = ((4:ℝ)^(m+1))⁻¹ := by
          rw [show (-(m:ℝ)-1) = -(((m+1 : ℕ) : ℝ)) by push_cast; ring,
            Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), ← Real.rpow_natCast (4:ℝ) (m+1)]
      _ ≤ ((i.1:ℝ)*(i'.1:ℝ))⁻¹ :=
          (inv_le_inv₀ (by positivity) (by positivity)).mpr hprod
  calc (4:ℝ)^(-(m:ℝ)-1) ≤ ((i.1:ℝ)*(i'.1:ℝ))⁻¹ := hqq
    _ ≤ |(i.2:ℝ)/(i.1:ℝ) - ((i'.2:ℝ)/(i'.1:ℝ) + (-(l:ℝ)))| := hsep
    _ = |(i.2:ℝ)/(i.1:ℝ) - (i'.2:ℝ)/(i'.1:ℝ) + (l:ℝ)| := by
        congr 1
        ring



/-- Integrability of `f · P · e(-2πixθ)` for bounded measurable `f` and a trigonometric polynomial
`P`. -/
lemma intervalIntegrable_mul_exp {f P : ℝ → ℂ} (hfm : Measurable f) (hPm : Measurable P)
    {Cf CP : ℝ} (hfb : ∀ θ, ‖f θ‖ ≤ Cf) (hPb : ∀ θ, ‖P θ‖ ≤ CP) (x : ℤ) :
    IntervalIntegrable (fun θ => f θ * P θ *
      Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))) volume 0 1 := by
  refine intervalIntegrable_of_measurable_bound ?_ (Cf * CP) (fun θ => ?_)
  · exact (hfm.mul hPm).mul (by fun_prop)
  · rw [norm_mul, norm_mul]
    have hexp : Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))
        = Complex.exp (((-(2*Real.pi*(x:ℝ)*θ) : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hfb 0)
    exact mul_le_mul (hfb θ) (hPb θ) (norm_nonneg _) hCf0


/-- A uniform bound on the block error (crude, for integrability). -/
lemma norm_blockErr_le_const (m : ℕ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m → ‖blockGaussWeight i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (k : ℕ) (θ : ℝ), ‖blockErr m k θ‖ ≤ B := by
  refine ⟨max 1 ((80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)/2))), ?_, fun k θ => ?_⟩
  · exact le_trans zero_le_one (le_max_left _ _)
  · by_cases hk : 4*m ≤ k
    · exact le_trans (norm_blockErr_le_generic hk θ A hA0 hA) (le_max_right _ _)
    · have hz : blockErr m k θ = 0 := by
        rw [blockErr, if_neg (by omega : ¬ 4*m+4 ≤ k), sub_zero,
          modelQBlock_eq_zero_of_lt (by omega : k < 4*m), map_zero]
      rw [hz, norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)



lemma two_mul_le_sq_add_sq (a b : ℝ≥0∞) : 2 * a * b ≤ a^2 + b^2 := by
  rw [mul_assoc]
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h
    calc 2*(a*(a+c)) ≤ 2*(a*(a+c)) + c^2 := le_add_right le_rfl
      _ = (a+c)^2 + a^2 := by ring
      _ = a^2 + (a+c)^2 := by ring
  · obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h
    calc 2*((b+c)*b) ≤ 2*((b+c)*b) + c^2 := le_add_right le_rfl
      _ = (b+c)^2 + b^2 := by ring

/-- Two functions that agree on the open interval `(0,1)` have the same integral over `0..1`. -/
lemma intervalIntegral_eq_of_eq_Ioo {f g : ℝ → ℂ} (h : ∀ θ, 0 < θ → θ < 1 → f θ = g θ) :
    (∫ θ in (0:ℝ)..1, f θ) = ∫ θ in (0:ℝ)..1, g θ := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (by simp : (volume : Measure ℝ) ({1} : Set ℝ) = 0)
  intro θ hθ
  simp only [Set.mem_setOf_eq] at hθ
  simp only [Set.mem_singleton_iff]
  by_contra hne1
  exact hθ (fun hθI => by
    rw [Set.mem_uIoc] at hθI
    rcases hθI with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · exact h θ h0 (lt_of_le_of_ne h1 hne1)
    · linarith)

/-- The numerical comparison behind the per-block constant. -/
lemma const_key (u v s X : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (hX : 1 ≤ X) :
    2*(u*s*X)^2 + 2*(v*s)^2 ≤ (2*(u+v)*s*X)^2 := by
  have h1 : 0 ≤ 2*u^2*s^2*X^2 := by positivity
  have h2 : 0 ≤ 8*u*v*s^2*X^2 := by positivity
  have h3 : 0 ≤ 2*v^2*s^2*(2*X^2 - 1) := by
    have hX2 : 1 ≤ X^2 := by nlinarith
    have : (0:ℝ) ≤ 2*X^2 - 1 := by nlinarith
    positivity
  nlinarith [h1, h2, h3]

theorem block_maximal_of_circle (H : CircleNeighborhoodMaximal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2 *
          ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨Cwγ, hCwγpos, hCwγ⟩ := weighted_core_maximal H
  obtain ⟨A, hApos, hgauss⟩ := exists_gaussWeight_cap
  obtain ⟨Cf, hCfpos, hCf0⟩ := Commons.Analysis.Fresnel.fresnel_replace_sharp_tsum_le
  have hCf' : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, errVal x k) ≤ Cf := by
    intro x hx
    refine le_trans (le_of_eq ?_) (hCf0 x hx)
    refine tsum_congr (fun k => ?_)
    rw [errVal, fresnelProfile]
  refine ⟨2 * (4 * Cwγ * A + 2 * A * (160 + Cf)), by positivity, fun m g s hgs => ?_⟩
  set P : ℝ → ℂ := fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)) with hPdef
  have hPcont : Continuous P := by
    rw [hPdef]
    refine continuous_finsetSum _ (fun n hn => ?_)
    fun_prop
  have hPm : Measurable P := hPcont.measurable
  have hPbd : ∀ θ, ‖P θ‖ ≤ ∑ n ∈ s, ‖g n‖ := by
    intro θ
    rw [hPdef]
    calc ‖∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖
        ≤ ∑ n ∈ s, ‖g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ := norm_sum_le _ _
      _ = ∑ n ∈ s, ‖g n‖ := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [norm_mul]
          have : ‖Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ = 1 := by
            rw [show 2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)
                  = (((2*Real.pi*(n:ℝ)*θ : ℝ)) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [this, mul_one]
  set Ef : ℤ → ℝ → ℂ := fun x θ => Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ))) with hEf
  set CoreFam : ℕ → ℤ → ℂ := fun j x => ∫ θ in (0:ℝ)..1,
      (if 8*m+7 ≤ j then ∑ p ∈ blockT m, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0) *
        P θ * Ef x θ with hCoreFam
  set ErrFam : ℕ → ℤ → ℂ := fun K x => ∫ θ in (0:ℝ)..1, errMult m K θ * P θ * Ef x θ with hErrFam
  have hcap0 : 0 ≤ A * (2:ℝ)^(-(m:ℝ)/2) := by positivity
  have hcap : ∀ p ∈ blockT m, ‖p.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)/2) := by
    intro p hp
    rw [blockT, Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [Complex.norm_conj]
    exact hgauss m i hi
  -- the core bound
  have hj₀δ : (2:ℝ)^(-(((8*m+7 : ℕ)):ℝ)-1) ≤ (4:ℝ)^(-(m:ℝ)-1)/3 := by
    have h1 : (-(((8*m+7 : ℕ)):ℝ)-1) = -(((8*m+8 : ℕ)):ℝ) := by push_cast; ring
    have h2 : (-(m:ℝ)-1) = -(((m+1 : ℕ)):ℝ) := by push_cast; ring
    rw [h1, h2]
    have h4 : (4:ℝ)^(-(((m+1 : ℕ)):ℝ)) = (2:ℝ)^(-(((2*m+2 : ℕ)):ℝ)) := by
      rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    rw [h4]
    have h5 : (2:ℝ)^(-(((8*m+8 : ℕ)):ℝ)) ≤ (2:ℝ)^(-(((2*m+4 : ℕ)):ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hAB : ((2*m+4 : ℕ) : ℝ) ≤ ((8*m+8 : ℕ) : ℝ) := by
        have : (2*m+4:ℕ) ≤ 8*m+8 := by omega
        exact_mod_cast this
      linarith
    have h6 : (2:ℝ)^(-(((2*m+4 : ℕ)):ℝ)) ≤ (2:ℝ)^(-(((2*m+2 : ℕ)):ℝ))/3 := by
      have h7 : (2:ℝ)^(-(((2*m+2 : ℕ)):ℝ))/4 = (2:ℝ)^(-(((2*m+4 : ℕ)):ℝ)) := by
        rw [show (-(((2*m+2 : ℕ)):ℝ)) = -(((2*m+4 : ℕ)):ℝ) + 2 by push_cast; ring,
          Real.rpow_add (by norm_num : (0:ℝ) < 2), show (2:ℝ)^(2:ℝ) = 4 by norm_num]
        ring
      rw [← h7]
      have hp : (0:ℝ) < (2:ℝ)^(-(((2*m+2 : ℕ)):ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    linarith [h5, h6]
  have hcore_raw := hCwγ (blockT m) (A * (2:ℝ)^(-(m:ℝ)/2)) ((4:ℝ)^(-(m:ℝ)-1))
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 4) _) hcap0 hcap (blockT_sep m) (8*m+7)
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hj₀δ g s hgs
  have hlognn : 0 ≤ Real.log (((blockT m).card:ℝ)+2) := by
    refine Real.log_nonneg ?_
    have h : (0:ℝ) ≤ ((blockT m).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hlog2 : Real.log (((blockT m).card:ℝ)+2)^2 ≤ (2*((m:ℝ)+2))^2 := by
    have h := log_blockT_le m
    have h2 : (0:ℝ) ≤ 2*((m:ℝ)+2) := by positivity
    nlinarith [h, hlognn]
  have hcore : ∫⁻ x : ℤ, (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
    refine le_trans hcore_raw ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hp1 : (0:ℝ) ≤ Cwγ * (A * (2:ℝ)^(-(m:ℝ)/2)) * Real.log (((blockT m).card:ℝ)+2)^2 := by positivity
    have hp2 : (0:ℝ) ≤ (4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2) := by positivity
    calc (Cwγ * (A * (2:ℝ)^(-(m:ℝ)/2)) * Real.log (((blockT m).card:ℝ)+2)^2)^2
        ≤ (Cwγ * (A * (2:ℝ)^(-(m:ℝ)/2)) * (2*((m:ℝ)+2))^2)^2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = (4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2)^2 := by ring
  -- the error bound
  have herr_raw := errMult_maximal_le A Cf hApos hCfpos hgauss hCf' m g s hgs
  have herr : ∫⁻ x : ℤ, (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((2 * A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2))^2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
    refine le_trans herr_raw ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hp : (0:ℝ) ≤ A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2) := by positivity
    nlinarith [hp]
  -- a uniform bound for the error, for integrability
  obtain ⟨B, hB0, hB⟩ := norm_blockErr_le_const m A hApos.le (hgauss m)
  -- integrability of the two pieces
  have hint_core : ∀ k x, IntervalIntegrable (fun θ =>
      (if 4*m+4 ≤ k then blockCore m k θ else 0) * P θ * Ef x θ) volume 0 1 := by
    intro k x
    refine intervalIntegrable_mul_exp (f := fun θ => (if 4*m+4 ≤ k then blockCore m k θ else 0))
      (P := P) (Cf := ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)/2))) (CP := ∑ n ∈ s, ‖g n‖) ?_ hPm ?_ hPbd x
    · by_cases hk : 4*m+4 ≤ k
      · simpa [hk] using measurable_blockCore m k
      · simpa [hk] using measurable_const (a := (0:ℂ))
    · intro θ
      by_cases hk : 4*m+4 ≤ k
      · rw [if_pos hk]
        exact norm_blockCore_le m k A hApos.le (hgauss m) θ
      · rw [if_neg hk, norm_zero]
        positivity
  have hint_err : ∀ k x, IntervalIntegrable (fun θ =>
      blockErr m k θ * P θ * Ef x θ) volume 0 1 :=
    fun k x => intervalIntegrable_mul_exp (f := fun θ => blockErr m k θ) (P := P)
      (Cf := B) (CP := ∑ n ∈ s, ‖g n‖) (measurable_blockErr m k) hPm
      (fun θ => hB k θ) hPbd x
  -- the decomposition of the block operator
  have hCore_eq : ∀ (k : ℕ) (x : ℤ),
      (∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then blockCore m k θ else 0) * P θ * Ef x θ)
        = CoreFam (2*k-1) x := by
    intro k x
    rw [hCoreFam]
    refine intervalIntegral_eq_of_eq_Ioo (fun θ hθ0 hθ1 => ?_)
    by_cases hk : 4*m+4 ≤ k
    · have h2k : 8*m+7 ≤ 2*k-1 := by omega
      rw [if_pos hk, if_pos h2k]
      have hrad : (2:ℝ)^(-(((2*k-1 : ℕ)):ℝ)-1) = (4:ℝ)^(-(k:ℝ)) := by
        have hcast : (((2*k-1 : ℕ)):ℝ) = 2*(k:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2*k)]
          push_cast
          ring
        rw [hcast, show -(2*(k:ℝ) - 1) - 1 = -(2*(k:ℝ)) by ring,
          show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [hrad, blockCore_eq_weighted (by omega : 1 ≤ k) θ hθ0 hθ1]
    · have h2k : ¬ (8*m+7 ≤ 2*k-1) := by omega
      rw [if_neg hk, if_neg h2k, zero_mul, zero_mul]
  have hErr_eq : ∀ (K : ℕ) (x : ℤ),
      (∫ θ in (0:ℝ)..1, blockErr m K θ * P θ * Ef x θ) = ErrFam K x := by
    intro K x
    rw [hErrFam]
    refine intervalIntegral_eq_of_eq_Ioo (fun θ hθ0 hθ1 => ?_)
    rw [errMult, if_pos ⟨hθ0, hθ1⟩]
  have hTk_eq : ∀ (k : ℕ) (x : ℤ), TkBlockMax g s m k x
      = (∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then blockCore m k θ else 0) * P θ * Ef x θ)
        + ErrFam k x := by
    intro k x
    rw [TkBlockMax]
    have h1 : (∫ θ in (0:ℝ)..1, starRingEnd ℂ (modelQBlock m (2^k) θ) * P θ * Ef x θ)
        = ∫ θ in (0:ℝ)..1, (((if 4*m+4 ≤ k then blockCore m k θ else 0) * P θ * Ef x θ)
            + (blockErr m k θ * P θ * Ef x θ)) := by
      refine intervalIntegral.integral_congr (fun θ hθ => ?_)
      have h2 : starRingEnd ℂ (modelQBlock m (2^k) θ)
          = (if 4*m+4 ≤ k then blockCore m k θ else 0) + blockErr m k θ := by
        rw [blockErr, add_sub_cancel]
      rw [h2]
      ring
    rw [h1, intervalIntegral.integral_add (hint_core k x) (hint_err k x), hErr_eq k x]
  have hdec : ∀ (k : ℕ) (x : ℤ), ‖TkBlockMax g s m k x‖ₑ
      ≤ ‖CoreFam (2*k-1) x‖ₑ + ‖ErrFam k x‖ₑ := by
    intro k x
    rw [hTk_eq k x]
    calc ‖(∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then blockCore m k θ else 0) * P θ * Ef x θ)
          + ErrFam k x‖ₑ
        ≤ ‖(∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then blockCore m k θ else 0) * P θ * Ef x θ)‖ₑ
          + ‖ErrFam k x‖ₑ := by
          rw [enorm_eq_ofReal_norm'', enorm_eq_ofReal_norm'', enorm_eq_ofReal_norm'',
            ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ‖CoreFam (2*k-1) x‖ₑ + ‖ErrFam k x‖ₑ := by rw [hCore_eq k x]
  -- the sup and the square
  have hsup : ∀ x : ℤ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ)
      ≤ 2 * (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ)
        + 2 * (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) := by
    intro x
    have h1 : (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ) ≤
        (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ) :=
      iSup_le (fun k => le_trans (hdec k x) (add_le_add
        (le_iSup (fun j => ‖CoreFam j x‖ₑ) (2*k-1))
        (le_iSup (fun K => ‖ErrFam K x‖ₑ) k)))
    rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two]
    calc (⨆ k, ‖TkBlockMax g s m k x‖ₑ)^2
        ≤ ((⨆ j, ‖CoreFam j x‖ₑ) + (⨆ K, ‖ErrFam K x‖ₑ))^2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (⨆ j, ‖CoreFam j x‖ₑ)^2 + 2*((⨆ j, ‖CoreFam j x‖ₑ)*(⨆ K, ‖ErrFam K x‖ₑ))
          + (⨆ K, ‖ErrFam K x‖ₑ)^2 := by ring
      _ ≤ (⨆ j, ‖CoreFam j x‖ₑ)^2 + ((⨆ j, ‖CoreFam j x‖ₑ)^2 + (⨆ K, ‖ErrFam K x‖ₑ)^2)
          + (⨆ K, ‖ErrFam K x‖ₑ)^2 := by
          refine add_le_add (add_le_add le_rfl ?_) le_rfl
          calc 2*((⨆ j, ‖CoreFam j x‖ₑ)*(⨆ K, ‖ErrFam K x‖ₑ))
              = 2 * (⨆ j, ‖CoreFam j x‖ₑ) * (⨆ K, ‖ErrFam K x‖ₑ) := by ring
            _ ≤ (⨆ j, ‖CoreFam j x‖ₑ)^2 + (⨆ K, ‖ErrFam K x‖ₑ)^2 :=
              two_mul_le_sq_add_sq (⨆ j, ‖CoreFam j x‖ₑ) (⨆ K, ‖ErrFam K x‖ₑ)
      _ = 2 * (⨆ j, ‖CoreFam j x‖ₑ)^2 + 2 * (⨆ K, ‖ErrFam K x‖ₑ)^2 := by ring_nf
  -- the assembly
  set I : ℝ≥0∞ := ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count with hI
  set Kc : ℝ := 4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)/2) * ((m:ℝ)+2)^2 with hKc
  set Ke : ℝ := 2 * A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)/2) with hKe
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hKe0 : 0 ≤ Ke := by rw [hKe]; positivity
  have hfin : 2 * (ENNReal.ofReal (Kc^2) * I) + 2 * (ENNReal.ofReal (Ke^2) * I)
      ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)/2)
          * ((m:ℝ)+2)^2)^2) * I := by
    have hx : (0:ℝ) < (2:ℝ)^(-(m:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
    have hm2 : (1:ℝ) ≤ ((m:ℝ)+2)^2 := by
      have h : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      nlinarith
    have hsum : (2:ℝ≥0∞) * ENNReal.ofReal (Kc^2) + (2:ℝ≥0∞) * ENNReal.ofReal (Ke^2)
        ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)/2)
            * ((m:ℝ)+2)^2)^2) := by
      have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
      rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hKc, hKe]
      exact const_key (4 * Cwγ * A) (2 * A * (160 + Cf)) ((2:ℝ)^(-(m:ℝ)/2)) (((m:ℝ)+2)^2)
        (by positivity) (by positivity) (le_of_lt hx) hm2
    calc 2 * (ENNReal.ofReal (Kc^2) * I) + 2 * (ENNReal.ofReal (Ke^2) * I)
        = ((2:ℝ≥0∞) * ENNReal.ofReal (Kc^2) + (2:ℝ≥0∞) * ENNReal.ofReal (Ke^2)) * I := by ring
      _ ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)/2)
            * ((m:ℝ)+2)^2)^2) * I := mul_le_mul_left hsum I
  calc ∫⁻ x : ℤ, (⨆ k : ℕ, ‖TkBlockMax g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (2 * (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ)
          + 2 * (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono hsup
    _ = 2 * ∫⁻ x : ℤ, (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        + 2 * ∫⁻ x : ℤ, (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [lintegral_add_left (measurable_of_countable _),
          lintegral_const_mul' 2 _ (by norm_num), lintegral_const_mul' 2 _ (by norm_num)]
    _ ≤ 2 * (ENNReal.ofReal (Kc^2) * I) + 2 * (ENNReal.ofReal (Ke^2) * I) := by
        rw [hKc, hKe, hI]
        exact add_le_add (mul_le_mul_right hcore 2) (mul_le_mul_right herr 2)
    _ ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)/2)
          * ((m:ℝ)+2)^2)^2) * I := hfin
    _ = ENNReal.ofReal (2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)/2)
          * ((m:ℝ)+2)^2) ^ 2 * ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [hI, ← ENNReal.ofReal_pow (by positivity)]

/-- **The target follows from the circle-form neighbourhood maximal.** -/
theorem quadratic_kernel_model_maximal_l2_of_circle_maximal (H : CircleNeighborhoodMaximal) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
  quadratic_kernel_model_maximal_l2_of_block (block_maximal_of_circle H)




/-- `‖unNbhd T r θ‖ ≤ 1`. -/
lemma norm_unNbhd_le_one (T : Finset (ℝ × ℂ)) (r θ : ℝ) : ‖unNbhd T r θ‖ ≤ 1 := by
  rw [unNbhd]
  split <;> simp

/-- **Step 2 of the density extension.**  The single-scale band-pass operator (multiplier
`unNbhd T (2^{-j-1})`, of modulus `≤ 1`) is a contraction from `L²((0,1))` to `ℓ²(ℤ)`. -/
lemma tOp_enorm_tsum_le (T : Finset (ℝ × ℂ)) (j : ℕ) {Q : ℝ → ℂ}
    (hQ : MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    (∑' m : ℤ, ‖∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ *
        Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ))
      ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ) := by
  set χ : ℝ → ℂ := unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) with hχ
  have hχm : Measurable χ := measurable_unNbhd T _
  have hχb : ∀ θ, ‖χ θ‖ ≤ 1 := fun θ => norm_unNbhd_le_one T _ θ
  rw [Commons.Analysis.Fourier.plancherel_circle_enorm_sq χ Q hχm ⟨1, hχb⟩ hQ]
  have hQint : Integrable (fun θ => ‖Q θ‖ ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    hQ.integrable_norm_pow (by norm_num)
  have hkey : ∀ θ, ‖χ θ‖ ^ 2 * ‖Q θ‖ ^ 2 ≤ ‖Q θ‖ ^ 2 := by
    intro θ
    calc ‖χ θ‖ ^ 2 * ‖Q θ‖ ^ 2 ≤ 1 * ‖Q θ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (hχb θ)) (sq_nonneg _)
      _ = ‖Q θ‖ ^ 2 := one_mul _
  have hχ2m : AEStronglyMeasurable (fun θ => ‖χ θ‖ ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (hχm.norm.pow_const 2).aestronglyMeasurable
  have hχQint : Integrable (fun θ => ‖χ θ‖ ^ 2 * ‖Q θ‖ ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine Integrable.bdd_mul (g := fun θ => ‖Q θ‖ ^ 2) (c := 1) hQint hχ2m ?_
    filter_upwards with θ
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_one₀ (norm_nonneg _) (hχb θ)
  calc ENNReal.ofReal (∫ θ in (0:ℝ)..1, ‖χ θ‖ ^ 2 * ‖Q θ‖ ^ 2)
      = ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (‖χ θ‖ ^ 2 * ‖Q θ‖ ^ 2) := by
        rw [intervalIntegral.integral_of_le (by norm_num),
          ofReal_integral_eq_lintegral_ofReal hχQint (Eventually.of_forall (fun θ => by positivity))]
    _ ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (‖Q θ‖ ^ 2) :=
        lintegral_mono (fun θ => ENNReal.ofReal_le_ofReal (hkey θ))
    _ = ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr (fun θ => ?_)
        rw [enorm_eq_ofReal_norm'', ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]



/-- The symmetric intervals `Icc (-N) N` are cofinal in `Finset ℤ`. -/
lemma tendsto_Icc_atTop : Tendsto (fun N : ℕ => Finset.Icc (-(N:ℤ)) (N:ℤ)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  filter_upwards [eventually_ge_atTop (s.sup (fun z => z.natAbs))] with N hN
  intro z hz
  have h1 : |z| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Finset.le_sup (f := fun z => z.natAbs) hz) hN
  rw [Finset.mem_Icc]
  exact abs_le.mp h1

/-- `volume = haarAddCircle` on `AddCircle 1`. -/
lemma volume_addCircle_one : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- **Circle-level Fourier density**: an `L²` function on `AddCircle 1` is approximated by finite
linear combinations of the Fourier monomials. -/
lemma dense_fourierLp (G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ n, n ∉ s → c n = 0) ∧
      ‖G - ∑ n ∈ s, c n • (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖
        < ε := by
  have hHS := hasSum_fourier_series_L2 (T := 1) G
  have hconv : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      fourierCoeff (↑↑G) n • (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
      atTop (𝓝 G) := hHS.comp tendsto_Icc_atTop
  have hev : ∀ᶠ N : ℕ in atTop,
      dist (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        fourierCoeff (↑↑G) n • (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
        G < ε := hconv.eventually (Metric.ball_mem_nhds G hε)
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨Finset.Icc (-(N:ℤ)) (N:ℤ), fun n => if n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ)
    then fourierCoeff (↑↑G) n else 0, fun n hn => if_neg hn, ?_⟩
  have hsum : (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      (if n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) then fourierCoeff (↑↑G) n else 0) •
        (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
      = ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        fourierCoeff (↑↑G) n • (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
    refine Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  rw [hsum]
  rwa [dist_eq_norm, norm_sub_rev] at hN



/-- `AddCircle.liftIoc` is additive (pointwise, by reduction to the window representative). -/
lemma liftIoc_sub_one (f g : ℝ → ℂ) :
    AddCircle.liftIoc 1 0 (fun θ => f θ - g θ)
      = fun t : AddCircle (1:ℝ) => AddCircle.liftIoc 1 0 f t - AddCircle.liftIoc 1 0 g t := by
  funext t
  rfl


/-- The `Lp` class of a finite linear combination of `Lp` elements is a.e. the corresponding finite
linear combination of their representatives (for scalar multiplication that is pointwise
multiplication). -/
lemma coeFn_sum_smul {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (c : ι → ℂ) (f : ι → Lp ℂ 2 μ) (g : ι → α → ℂ)
    (h : ∀ i, (f i : α → ℂ) =ᵐ[μ] g i) :
    (((∑ i ∈ s, c i • f i) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, c i * g i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
    have h1 : ((c a • f a : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => c a * g a x := by
      filter_upwards [Lp.coeFn_smul (c a) (f a), h a] with x h2 h3
      simp only [h2, Pi.smul_apply, smul_eq_mul, h3]
    calc (((∑ i ∈ insert a s, c i • f i) : Lp ℂ 2 μ) : α → ℂ)
        = (((c a • f a + ∑ i ∈ s, c i • f i) : Lp ℂ 2 μ) : α → ℂ) := by
          rw [Finset.sum_insert ha]
      _ =ᵐ[μ] (((c a • f a : Lp ℂ 2 μ) : α → ℂ) + (((∑ i ∈ s, c i • f i) : Lp ℂ 2 μ) : α → ℂ)) :=
          Lp.coeFn_add _ _
      _ =ᵐ[μ] ((fun x => c a * g a x) + (fun x => ∑ i ∈ s, c i * g i x)) := h1.add ih
      _ =ᵐ[μ] (fun x => ∑ i ∈ insert a s, c i * g i x) := by
          refine Filter.EventuallyEq.of_eq ?_
          funext x
          rw [Finset.sum_insert ha]
          rfl

/-- The `Lp` class of a finite sum of Fourier monomials is a.e. the corresponding trigonometric
polynomial on the circle. -/
lemma coeFn_sum_fourierLp (s : Finset ℤ) (c : ℤ → ℂ) :
    (((∑ n ∈ s, c n • (fourierLp (T := 1) 2 n :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))
      : AddCircle (1:ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun t => ∑ n ∈ s, c n * fourier n t :=
  coeFn_sum_smul s c
    (fun n => (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
    (fun n t => fourier n t)
    (fun n => coeFn_fourierLp (T := 1) 2 n)




/-- The `L²` norm-squared of an `Lp` element is the integral of the squared norm of its
representative. -/
lemma ofReal_norm_sq_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Lp ℂ 2 μ) :
    ENNReal.ofReal (‖F‖ ^ 2) = ∫⁻ x, ‖(F : α → ℂ) x‖ₑ ^ (2:ℝ) ∂μ := by
  set H : ℝ≥0∞ := ∫⁻ x, ‖(F : α → ℂ) x‖ₑ ^ (2:ℝ) ∂μ with hH
  have h1 : eLpNorm (F : α → ℂ) 2 μ = H ^ (1/2:ℝ) := by
    rw [hH, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable F)]
    norm_num
  have hsq : (H ^ (1/2:ℝ)) ^ 2 = H := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hHtop : H ≠ ∞ := by
    have h2 : H = (eLpNorm (F : α → ℂ) 2 μ) * (eLpNorm (F : α → ℂ) 2 μ) := by
      rw [h1, ← pow_two]
      exact hsq.symm
    rw [h2]
    exact ENNReal.mul_ne_top (ne_of_lt (Lp.memLp F).eLpNorm_lt_top)
      (ne_of_lt (Lp.memLp F).eLpNorm_lt_top)
  have htoReal : H.toReal = ((H ^ (1/2:ℝ)).toReal) ^ 2 := by
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
    exact (Real.sq_sqrt (show (0:ℝ) ≤ H.toReal by positivity)).symm
  have hnorm : ‖F‖ = (H ^ (1/2:ℝ)).toReal := by
    rw [Lp.norm_def, h1]
  calc ENNReal.ofReal (‖F‖ ^ 2)
      = ENNReal.ofReal (((H ^ (1/2:ℝ)).toReal) ^ 2) := by rw [hnorm]
    _ = ENNReal.ofReal (H.toReal) := by rw [htoReal]
    _ = H := ENNReal.ofReal_toReal hHtop



/-- `liftIoc` commutes with the pointwise norm. -/
lemma liftIoc_norm_one (f : ℝ → ℂ) :
    AddCircle.liftIoc 1 0 (fun θ => ‖f θ‖)
      = fun t : AddCircle (1:ℝ) => ‖AddCircle.liftIoc 1 0 f t‖ := by
  funext t
  rfl

/-- `liftIoc` commutes with the pointwise `ℂ → ℝ` norm. -/
lemma liftIoc_norm_one_real (f : ℝ → ℝ) :
    AddCircle.liftIoc 1 0 (fun θ => ‖f θ‖)
      = fun t : AddCircle (1:ℝ) => ‖AddCircle.liftIoc 1 0 f t‖ := by
  funext t
  rfl



/-- `liftIoc` of a trigonometric polynomial is the corresponding combination of the Fourier
monomials on the circle. -/
lemma liftIoc_trigPoly (s : Finset ℤ) (c : ℤ → ℂ) :
    AddCircle.liftIoc 1 0 (fun θ : ℝ => ∑ n ∈ s, c n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)))
      = fun t : AddCircle (1:ℝ) => ∑ n ∈ s, c n * fourier n t := by
  funext t
  obtain ⟨x, hx, hxt⟩ : ∃ x ∈ Set.Ioc (0:ℝ) (0 + 1), (x : AddCircle (1:ℝ)) = t :=
    ⟨((AddCircle.equivIoc 1 0 t : ↥(Set.Ioc (0:ℝ) (0 + 1))) : ℝ),
      (AddCircle.equivIoc 1 0 t).2, AddCircle.coe_equivIoc⟩
  rw [← hxt, AddCircle.liftIoc_coe_apply hx]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring_nf


/-- **Step 1 of the density extension (interval form).**  Trigonometric polynomials are dense in
`L²((0,1))`. -/
theorem trigPoly_dense_L2_Ioc (Q : ℝ → ℂ)
    (hQ : MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ n, n ∉ s → c n = 0) ∧
      ∫⁻ θ in Set.Ioc (0:ℝ) 1,
        ‖Q θ - ∑ n ∈ s, c n * Complex.exp (2 * Real.pi * Complex.I * (n:ℂ) * (θ:ℂ))‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal ε := by
  set δ : ℝ := min ε 1 with hδ
  have hδpos : 0 < δ := lt_min hε one_pos
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hδleε : δ ≤ ε := min_le_left _ _
  have hQ' : MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) (0 + 1))) := by simpa using hQ
  have hG : MemLp (AddCircle.liftIoc 1 0 Q) 2 (volume : Measure (AddCircle (1:ℝ))) :=
    hQ'.memLp_liftIoc
  have hGh : MemLp (AddCircle.liftIoc 1 0 Q) 2 (AddCircle.haarAddCircle (T := 1)) := by
    rwa [volume_addCircle_one] at hG
  set G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := hGh.toLp _ with hGdef
  obtain ⟨s, c, hc0, hclose⟩ := dense_fourierLp G hδpos
  refine ⟨s, c, hc0, ?_⟩
  set P : ℝ → ℂ := fun θ => ∑ n ∈ s, c n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)) with hPdef
  set S : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    ∑ n ∈ s, c n • (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))
    with hSdef
  -- the a.e. identification of `G - S` with `liftIoc 1 0 (Q - P)`
  have hident : ((G - S : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : AddCircle (1:ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 0 (fun θ => Q θ - P θ) := by
    have h1 : (G : AddCircle (1:ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)]
        AddCircle.liftIoc 1 0 Q := by
      rw [hGdef]
      exact MemLp.coeFn_toLp hGh
    have h2 : (S : AddCircle (1:ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)]
        AddCircle.liftIoc 1 0 P := by
      rw [hSdef, hPdef]
      exact (coeFn_sum_fourierLp s c).trans (Filter.EventuallyEq.of_eq (liftIoc_trigPoly s c)).symm
    filter_upwards [Lp.coeFn_sub G S, h1, h2,
      Filter.EventuallyEq.of_eq (liftIoc_sub_one Q P)] with t h3 h4 h5 h6
    rw [h3, Pi.sub_apply, h4, h5, ← h6]
  -- transport to the circle, as a lower integral identity
  have key : (∫⁻ b : AddCircle (1:ℝ),
        ‖AddCircle.liftIoc 1 0 (fun θ' : ℝ => Q θ' - P θ') b‖ₑ ^ (2:ℝ)
        ∂AddCircle.haarAddCircle (T := 1))
      = ∫⁻ a in Set.Ioc (0:ℝ) 1,
        ‖AddCircle.liftIoc 1 0 (fun θ' : ℝ => Q θ' - P θ') (a : AddCircle (1:ℝ))‖ₑ ^ (2:ℝ) := by
    rw [← volume_addCircle_one]
    rw [← AddCircle.lintegral_preimage (T := 1) (t := 0)
      (f := fun b : AddCircle (1:ℝ) =>
        ‖AddCircle.liftIoc 1 0 (fun θ' : ℝ => Q θ' - P θ') b‖ₑ ^ (2:ℝ))]
    norm_num
  have hA : ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ - P θ‖ₑ ^ (2:ℝ)
      = ∫⁻ b : AddCircle (1:ℝ), ‖AddCircle.liftIoc 1 0 (fun θ' : ℝ => Q θ' - P θ') b‖ₑ ^ (2:ℝ)
          ∂AddCircle.haarAddCircle (T := 1) := by
    rw [key]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hθ' : θ ∈ Set.Ioc (0:ℝ) (0 + 1) := by simpa using hθ
    rw [AddCircle.liftIoc_coe_apply hθ']
  have hE : (fun b : AddCircle (1:ℝ) =>
        ‖AddCircle.liftIoc 1 0 (fun θ' : ℝ => Q θ' - P θ') b‖ₑ ^ (2:ℝ))
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      (fun b : AddCircle (1:ℝ) =>
        ‖((G - S : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : AddCircle (1:ℝ) → ℂ) b‖ₑ ^ (2:ℝ)) := by
    filter_upwards [hident] with b hb
    rw [← hb]
  have hfin : (∫⁻ b : AddCircle (1:ℝ),
        ‖AddCircle.liftIoc 1 0 (fun θ' : ℝ => Q θ' - P θ') b‖ₑ ^ (2:ℝ)
        ∂AddCircle.haarAddCircle (T := 1)) = ENNReal.ofReal (‖G - S‖ ^ 2) := by
    rw [lintegral_congr_ae hE]
    exact (ofReal_norm_sq_eq_lintegral (μ := AddCircle.haarAddCircle (T := 1)) (G - S)).symm
  rw [hA, hfin]
  calc ENNReal.ofReal (‖G - S‖ ^ 2) ≤ ENNReal.ofReal (δ ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hclose) 2
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hδpos, hδle1, hδleε, sq_nonneg δ]





open scoped FourierTransform

/-- **The real-line band-pass maximal in multiplier form** (Bourgain 1989, Lemma 4.11 /
(4.14)).  For every finite frequency set `s` the maximal over the dyadic scales of the
band-pass projection onto the `2^{-j-1}`-neighbourhoods of `s` is bounded by
`C (log |s|)⁴` in `L²`. -/
def RealLineMultiplierMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (f : ℝ → ℂ), Integrable f →
    ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖∫ ξ in (-(1/2):ℝ)..(1/2),
        (𝓕 f) ξ *
        Set.indicator {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2:ℝ)^(-(j:ℝ)-1)} (fun _ => (1:ℂ)) ξ *
        Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))‖ₑ)^(2:ℝ) ∂volume
      ≤ ENNReal.ofReal ((C * Real.log ((s.card:ℝ)+2)^2)^2) * ∫⁻ x, ‖f x‖ₑ^(2:ℝ) ∂volume

/-- An enumeration of the distinct frequencies of `T`. -/
noncomputable def freqEnum (T : Finset (ℝ × ℂ)) (k : Fin (T.image Prod.fst).card) : ℝ :=
  ((T.image Prod.fst).equivFin.symm k : ℝ)

lemma freqEnum_mem (T : Finset (ℝ × ℂ)) (k : Fin (T.image Prod.fst).card) :
    freqEnum T k ∈ T.image Prod.fst :=
  ((T.image Prod.fst).equivFin.symm k).2

lemma exists_freqEnum_eq {T : Finset (ℝ × ℂ)} {a : ℝ} (ha : a ∈ T.image Prod.fst) :
    ∃ k : Fin (T.image Prod.fst).card, freqEnum T k = a :=
  ⟨(T.image Prod.fst).equivFin ⟨a, ha⟩, by simp [freqEnum]⟩

/-- The active-frequency condition of `unNbhd` in terms of the enumeration `freqEnum`. -/
lemma mem_unNbhd_set (T : Finset (ℝ × ℂ)) (r θ : ℝ) :
    (∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r) ↔
      (∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ,
        |θ + (l:ℝ) - freqEnum T k| ≤ r) := by
  constructor
  · rintro ⟨p, hp, l, hl⟩
    obtain ⟨k, hk⟩ := exists_freqEnum_eq (T := T) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    exact ⟨k, l, by rw [hk]; exact hl⟩
  · rintro ⟨k, l, hl⟩
    obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp (freqEnum_mem T k)
    exact ⟨p, hp, l, by rw [hp1]; exact hl⟩

/-- `unNbhd T r` is the indicator of `freqSet T r`. -/
lemma unNbhd_eq_indicator_freq (T : Finset (ℝ × ℂ)) (r : ℝ) (θ : ℝ) :
    unNbhd T r θ = Set.indicator ({θ : ℝ | ∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ, |θ + (l:ℝ) - freqEnum T k| ≤ r}) (fun _ => (1:ℂ)) θ := by
  classical
  have hmem : (∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r) ↔ θ ∈ {θ : ℝ | ∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ, |θ + (l:ℝ) - freqEnum T k| ≤ r} :=
    mem_unNbhd_set T r θ
  rw [unNbhd, Set.indicator_apply]
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r
  · rw [if_pos h, if_pos (hmem.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hmem.mpr hh))]

/-- Multiplying the `unNbhd` indicator into a function gives the indicator of `freqSet` applied
to that function. -/
lemma unNbhd_mul_eq_indicator (T : Finset (ℝ × ℂ)) (r : ℝ) (P : ℝ → ℂ) (θ : ℝ) :
    unNbhd T r θ * P θ = Set.indicator ({θ : ℝ | ∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ, |θ + (l:ℝ) - freqEnum T k| ≤ r}) P θ := by
  classical
  have hmem : (∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r) ↔ θ ∈ {θ : ℝ | ∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ, |θ + (l:ℝ) - freqEnum T k| ≤ r} :=
    mem_unNbhd_set T r θ
  rw [unNbhd, Set.indicator_apply]
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ r
  · rw [if_pos h, if_pos (hmem.mp h), one_mul]
  · rw [if_neg h, if_neg (fun hh => h (hmem.mpr hh)), zero_mul]

/-- **The circle-form neighbourhood maximal for trigonometric polynomials** (from the periodic
transference lemma). -/
lemma trigPoly_unNbhd_maximal (H : RealLineMultiplierMaximal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (ℝ × ℂ)) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
          unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ *
          (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C * Real.log (((T.image Prod.fst).card:ℝ)+2)^2)^2)
        * ∫⁻ n : ℤ, ‖g n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := H
  obtain ⟨D, hDpos, hD⟩ :=
    Commons.Analysis.Fourier.periodic_neighborhood_of_real_line_bandpass ⟨C, hCpos, hC⟩
  refine ⟨D, hDpos, ?_⟩
  intro T g s hg
  refine le_trans (le_of_eq ?_) (hD (T.image Prod.fst).card (freqEnum T) g s hg)
  refine lintegral_congr (fun m => ?_)
  congr 1
  refine iSup_congr (fun j => ?_)
  congr 1
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  have hfun : ∀ θ' : ℝ, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ' *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ':ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ':ℂ)))
      = Set.indicator {θ' : ℝ | ∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ, |θ' + (l:ℝ) - freqEnum T k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun θ' => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ':ℂ))) θ' *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ':ℂ))) := by
    intro θ'
    rw [unNbhd_eq_indicator_freq]
    by_cases h : θ' ∈ {θ'' : ℝ | ∃ k : Fin (T.image Prod.fst).card, ∃ l : ℤ, |θ'' + (l:ℝ) - freqEnum T k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [hfun θ]


/-- The exponential factor `θ ↦ e(-2πi m θ)`. -/
noncomputable def Ef (m : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))

lemma measurable_Ef (m : ℤ) : Measurable (Ef m) := by
  show Measurable (fun θ : ℝ => Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ))))
  fun_prop

lemma norm_Ef (m : ℤ) (θ : ℝ) : ‖Ef m θ‖ = 1 := by
  show ‖Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ = 1
  rw [show -(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)) = ((-(2*Real.pi*(m:ℝ)*θ) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- `‖unNbhd T r · e(-2πim·)‖ ≤ 1`. -/
lemma norm_unNbhd_mul_Ef_le (T : Finset (ℝ × ℂ)) (r : ℝ) (m : ℤ) (θ : ℝ) :
    ‖unNbhd T r θ * Ef m θ‖ ≤ 1 := by
  rw [norm_mul, norm_Ef, mul_one]
  exact norm_unNbhd_le_one T r θ

/-- A function in `L²((0,1))` multiplied by the bounded multiplier `unNbhd · e(-2πim·)` is
interval-integrable on `[0,1]`. -/
lemma intervalIntegrable_unNbhd_mul {T : Finset (ℝ × ℂ)} {r : ℝ} (m : ℤ) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    IntervalIntegrable (fun θ => unNbhd T r θ * φ θ * Ef m θ) volume 0 1 := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ]; simp⟩
  have hχm : Measurable (fun θ => unNbhd T r θ * Ef m θ) :=
    (measurable_unNbhd T r).mul (measurable_Ef m)
  have hb : ∀ θ : ℝ, ‖unNbhd T r θ * Ef m θ‖ ≤ 1 := fun θ => norm_unNbhd_mul_Ef_le T r m θ
  have hφint : Integrable φ μ := memLp_one_iff_integrable.mp (hφ.mono_exponent (by norm_num))
  have hint : Integrable (fun θ => φ θ * (unNbhd T r θ * Ef m θ)) μ :=
    hφint.mul_bdd hχm.aestronglyMeasurable (Eventually.of_forall hb)
  constructor
  · show Integrable (fun θ => unNbhd T r θ * φ θ * Ef m θ) (volume.restrict (Set.Ioc (0:ℝ) 1))
    exact hint.congr (Eventually.of_forall (fun θ => by ring))
  · rw [Set.Ioc_eq_empty (by norm_num : ¬ (1:ℝ) < 0)]
    exact integrableOn_empty

/-- **Linearity of the single-scale band-pass operator** on `[0,1]`. -/
lemma tOp_sub_val {T : Finset (ℝ × ℂ)} {r : ℝ} (m : ℤ) {φ ψ : ℝ → ℂ}
    (hφ : IntervalIntegrable (fun θ => unNbhd T r θ * φ θ * Ef m θ) volume 0 1)
    (hψ : IntervalIntegrable (fun θ => unNbhd T r θ * ψ θ * Ef m θ) volume 0 1) :
    (∫ θ in (0:ℝ)..1, unNbhd T r θ * φ θ * Ef m θ)
      - (∫ θ in (0:ℝ)..1, unNbhd T r θ * ψ θ * Ef m θ)
    = ∫ θ in (0:ℝ)..1, unNbhd T r θ * (φ θ - ψ θ) * Ef m θ := by
  rw [← intervalIntegral.integral_sub hφ hψ]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  ring

/-- **Bessel's inequality** for the Fourier partial sums on the circle. -/
lemma fourierCoeff_partial_sum_sq_le (G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖fourierCoeff G n‖ ^ 2)
      ≤ ∫ t : AddCircle (1:ℝ), ‖G t‖ ^ 2 ∂(AddCircle.haarAddCircle (T := 1)) := by
  have h := hasSum_sq_fourierCoeff (T := 1) G
  have hle := h.summable.sum_le_tsum (Finset.Icc (-(N:ℤ)) (N:ℤ)) (fun i _ => by positivity)
  rwa [h.tsum_eq] at hle


/-- **Transport of the `L²`-mass of an interval function to the circle.** -/
lemma lintegral_liftIoc_eq (f : ℝ → ℂ) :
    (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖f θ‖ₑ ^ (2:ℝ))
      = ∫⁻ t : AddCircle (1:ℝ), ‖AddCircle.liftIoc 1 0 f t‖ₑ ^ (2:ℝ)
          ∂AddCircle.haarAddCircle (T := 1) := by
  have hKey : (∫⁻ b : AddCircle (1:ℝ), ‖AddCircle.liftIoc 1 0 f b‖ₑ ^ (2:ℝ)
        ∂AddCircle.haarAddCircle (T := 1))
      = ∫⁻ a in Set.Ioc (0:ℝ) 1,
          ‖AddCircle.liftIoc 1 0 f (a : AddCircle (1:ℝ))‖ₑ ^ (2:ℝ) := by
    rw [← volume_addCircle_one]
    rw [← AddCircle.lintegral_preimage (T := 1) (t := 0)
      (f := fun b : AddCircle (1:ℝ) => ‖AddCircle.liftIoc 1 0 f b‖ₑ ^ (2:ℝ))]
    norm_num
  rw [hKey]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  have hθ' : θ ∈ Set.Ioc (0:ℝ) (0 + 1) := by simpa using hθ
  rw [AddCircle.liftIoc_coe_apply hθ']

/-- **Transport of the `L²`-distance to the circle.** -/
lemma lintegral_sub_sq_eq_norm_sq {Q P : ℝ → ℂ}
    {G S : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hG : (G : AddCircle (1:ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 0 Q)
    (hS : (S : AddCircle (1:ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 0 P) :
    (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ - P θ‖ₑ ^ (2:ℝ))
      = ENNReal.ofReal (‖G - S‖ ^ 2) := by
  have hsub : ((G - S : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : AddCircle (1:ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 0 (fun θ => Q θ - P θ) := by
    filter_upwards [Lp.coeFn_sub G S, hG, hS,
      Filter.EventuallyEq.of_eq (liftIoc_sub_one Q P)] with t h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, ← h4]
  rw [lintegral_liftIoc_eq (fun θ => Q θ - P θ)]
  rw [ofReal_norm_sq_eq_lintegral (μ := AddCircle.haarAddCircle (T := 1)) (G - S)]
  refine lintegral_congr_ae ?_
  filter_upwards [hsub] with t ht
  rw [← ht]

/-- Real arithmetic: if `0 ≤ x` and `0 ≤ y < x²` there is `ε ∈ (0, x]` with `(x - ε)² > y`. -/
lemma exists_eps_of_lt_sq {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y < x ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ x ∧ y < (x - ε) ^ 2 := by
  have hxpos : 0 < x := by
    rcases hx.lt_or_eq with h | h
    · exact h
    · rw [← h] at hy; linarith
  refine ⟨min (x/2) ((x^2 - y)/(4*x)), ?_, ?_, ?_⟩
  · refine lt_min (by linarith) ?_
    have : 0 < x^2 - y := by nlinarith
    positivity
  · exact le_trans (min_le_left _ _) (by linarith)
  · have h1 : 2 * x * min (x/2) ((x^2 - y)/(4*x)) ≤ (x^2 - y)/2 := by
      have h2 : x * min (x/2) ((x^2 - y)/(4*x)) ≤ x * ((x^2 - y)/(4*x)) := by
        refine mul_le_mul_of_nonneg_left (min_le_right _ _) hx
      have h3 : x * ((x^2 - y)/(4*x)) = (x^2 - y)/4 := by
        field_simp
      linarith [h2, h3.le, h3.ge]
    have h4 : (min (x/2) ((x^2 - y)/(4*x)))^2 ≥ 0 := sq_nonneg _
    nlinarith [h1, h4]





lemma log_card_image_le (T : Finset (ℝ × ℂ)) :
    Real.log (((T.image Prod.fst).card : ℝ) + 2) ≤ Real.log ((T.card : ℝ) + 2) := by
  refine Real.log_le_log (by positivity) ?_
  have h := Finset.card_image_le (s := T) (f := Prod.fst)
  have h' : ((T.image Prod.fst).card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h
  linarith

/-- **The circle-form neighbourhood maximal from the real-line multiplier maximal.** -/
theorem circleNeighborhoodMaximal_of_multiplierMaximal (H : RealLineMultiplierMaximal) :
    CircleNeighborhoodMaximal := by
  obtain ⟨Cp, hCppos, hP⟩ := trigPoly_unNbhd_maximal H
  refine ⟨Cp, hCppos, ?_⟩
  intro T Q hQ
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩
  -- the circle class of `Q` and its Fourier partial sums
  have hQ' : MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) (0 + 1))) := by simpa using hQ
  have hGl : MemLp (AddCircle.liftIoc 1 0 Q) 2 (volume : Measure (AddCircle (1:ℝ))) :=
    hQ'.memLp_liftIoc
  have hGh : MemLp (AddCircle.liftIoc 1 0 Q) 2 (AddCircle.haarAddCircle (T := 1)) := by
    rwa [volume_addCircle_one] at hGl
  set G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := hGh.toLp _ with hGdef
  have hGcoe : (G : AddCircle (1:ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 0 Q := by
    rw [hGdef]; exact MemLp.coeFn_toLp hGh
  set cc : ℤ → ℂ := fun n => fourierCoeff (G : AddCircle (1:ℝ) → ℂ) n with hcc
  set SN : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := fun N =>
    ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      cc n • (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) with hSN
  set PN : ℕ → ℝ → ℂ := fun N θ =>
    ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      cc n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)) with hPN
  have hSN_eq : ∀ N, ((SN N : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
        AddCircle (1:ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 0 (PN N) := by
    intro N
    rw [hSN, hPN]
    exact (coeFn_sum_fourierLp _ _).trans
      (Filter.EventuallyEq.of_eq (liftIoc_trigPoly _ _)).symm
  have hSN_tendsto : Tendsto SN atTop (𝓝 G) := by
    have h : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), cc n •
        (fourierLp (T := 1) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) atTop (𝓝 G) :=
      (hasSum_fourier_series_L2 (T := 1) G).comp tendsto_Icc_atTop
    rw [hSN]
    exact h
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ‖G - SN N‖ < ε := by
    intro ε hε
    filter_upwards [hSN_tendsto.eventually (Metric.ball_mem_nhds G hε)] with N hN
    rw [dist_eq_norm, norm_sub_rev] at hN
    exact hN
  -- `PN N` is a trigonometric polynomial
  have hPNcont : ∀ N, Continuous (PN N) := by
    intro N
    rw [hPN]
    refine continuous_finsetSum _ (fun n hn => ?_)
    fun_prop
  have hPNbd : ∀ N θ, ‖PN N θ‖ ≤ ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖ := by
    intro N θ
    rw [hPN]
    calc ‖∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
          cc n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))‖
        ≤ ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
            ‖cc n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖ := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [norm_mul]
          have hexp : ‖Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))‖ = 1 := by
            rw [show 2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)
                  = (((2*Real.pi*(n:ℝ)*θ : ℝ)) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [hexp, mul_one]
  have hPNmem : ∀ N, MemLp (PN N) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := fun N =>
    MemLp.of_bound (hPNcont N).aestronglyMeasurable _
      (Eventually.of_forall (hPNbd N))
  have hQPN : ∀ N, MemLp (fun θ => Q θ - PN N θ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    fun N => hQ.sub (hPNmem N)
  -- the `L²`-mass of the difference
  have heps : ∀ N, (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ - PN N θ‖ₑ^(2:ℝ))
      = ENNReal.ofReal (‖G - SN N‖^2) :=
    fun N => lintegral_sub_sq_eq_norm_sq hGcoe (hSN_eq N)
  -- the contraction bound
  have hcontract : ∀ (j N : ℕ) (m : ℤ),
      (‖∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m θ‖ₑ)^(2:ℝ)
        ≤ ENNReal.ofReal (‖G - SN N‖^2) := by
    intro j N m
    have h := tOp_enorm_tsum_le T j (hQPN N)
    refine le_trans (ENNReal.le_tsum (f := fun m' : ℤ => (‖∫ θ in (0:ℝ)..1,
      unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m' θ‖ₑ) ^ (2:ℝ)) m) ?_
    rw [← heps N]
    exact h
  -- linearity of the single-scale operator
  have hlin : ∀ (j N : ℕ) (m : ℤ),
      (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ)
        - (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ)
      = ∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m θ :=
    fun j N m => tOp_sub_val m (intervalIntegrable_unNbhd_mul m hQ)
      (intervalIntegrable_unNbhd_mul m (hPNmem N))
  -- the uniform Lipschitz bound
  have hlip : ∀ (j N : ℕ) (m : ℤ),
      ‖(∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ)
        - (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ)‖
      ≤ ‖G - SN N‖ := by
    intro j N m
    rw [hlin j N m]
    have hc := hcontract j N m
    have h1 : (‖∫ θ in (0:ℝ)..1,
          unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m θ‖ₑ)^(2:ℝ)
        = ENNReal.ofReal (‖∫ θ in (0:ℝ)..1,
          unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m θ‖ ^ 2) := by
      rw [enorm_eq_ofReal_norm'', ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [h1] at hc
    have h2 : ‖∫ θ in (0:ℝ)..1,
          unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m θ‖ ^ 2
        ≤ ‖G - SN N‖ ^ 2 := by
      have h3 : (ENNReal.ofReal (‖G - SN N‖ ^ 2)).toReal = ‖G - SN N‖ ^ 2 :=
        ENNReal.toReal_ofReal (by positivity)
      have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
      rwa [ENNReal.toReal_ofReal (by positivity), h3] at h4
    calc ‖∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * (Q θ - PN N θ) * Ef m θ‖
        ≤ Real.sqrt (‖G - SN N‖ ^ 2) := (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr h2
      _ = ‖G - SN N‖ := Real.sqrt_sq (norm_nonneg _)
  -- the maximal family of the partial sums
  set FN : ℕ → ℤ → ℝ≥0∞ := fun N m => (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
      unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ₑ)^(2:ℝ) with hFN
  set FQ : ℤ → ℝ≥0∞ := fun m => (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
      unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ‖ₑ)^(2:ℝ) with hFQ
  -- the pointwise liminf comparison
  have hpoint : ∀ m : ℤ, FQ m ≤ Filter.liminf (fun N => FN N m) atTop := by
    intro m
    refine (Filter.le_liminf_iff (u := fun N => FN N m)).2 ?_
    intro y hy
    rw [hFQ] at hy
    simp only [] at hy
    rw [ENNReal.rpow_two, ENNReal.iSup_pow] at hy
    obtain ⟨j, hj⟩ := lt_iSup_iff.mp hy
    set x : ℝ := ‖∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ‖ with hx
    have hxrpow : (‖∫ θ in (0:ℝ)..1,
          unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ‖ₑ) ^ 2
        = ENNReal.ofReal (x ^ 2) := by
      rw [hx, enorm_eq_ofReal_norm'', ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [hxrpow] at hj
    have hyne : y ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hj le_top)
    have hyt : y.toReal < x ^ 2 := by
      have h2 := hj
      rw [← ENNReal.toReal_lt_toReal hyne ENNReal.ofReal_ne_top] at h2
      rwa [ENNReal.toReal_ofReal (by positivity)] at h2
    obtain ⟨ε, hεpos, hεx, hεy⟩ := exists_eps_of_lt_sq (norm_nonneg _) (ENNReal.toReal_nonneg) hyt
    filter_upwards [hsmall ε hεpos] with N hN
    have hlt : ‖(∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ)
        - (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ)‖
        ≤ ‖G - SN N‖ := hlip j N m
    have hpos : 0 ≤ x - ε := by rw [hx]; linarith
    have hsub : x - ε < ‖∫ θ in (0:ℝ)..1,
        unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ := by
      have hnum : ‖(∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ)‖
          ≤ ‖(∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ)
              - (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ)‖
            + ‖∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ := by
        have h := norm_add_le
          ((∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * Q θ * Ef m θ)
            - (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ))
          (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ)
        simpa only [sub_add_cancel] using h
      rw [hx]
      linarith [hnum, hlt]
    have hsq : (x - ε) ^ 2 < ‖∫ θ in (0:ℝ)..1,
        unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ ^ 2 :=
      pow_lt_pow_left₀ hsub hpos (by norm_num : (2:ℕ) ≠ 0)
    have h2 : ENNReal.ofReal (‖∫ θ in (0:ℝ)..1,
          unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ ^ 2) ≤ FN N m := by
      rw [hFN]
      simp only []
      rw [ENNReal.rpow_two, ENNReal.iSup_pow]
      rw [show ENNReal.ofReal (‖∫ θ in (0:ℝ)..1,
            unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ ^ 2)
          = (‖∫ θ in (0:ℝ)..1,
            unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ₑ) ^ 2 by
        rw [enorm_eq_ofReal_norm'', ← ENNReal.ofReal_pow (norm_nonneg _)]]
      exact le_iSup (α := ℝ≥0∞) (fun i : ℕ => (‖∫ θ in (0:ℝ)..1,
        unNbhd T ((2:ℝ)^(-(i:ℝ)-1)) θ * PN N θ * Ef m θ‖ₑ) ^ 2) j
    calc y = ENNReal.ofReal y.toReal := (ENNReal.ofReal_toReal hyne).symm
      _ < ENNReal.ofReal ((x - ε) ^ 2) :=
          (ENNReal.ofReal_lt_ofReal_iff (p := y.toReal) (q := (x - ε) ^ 2)
            (by linarith [ENNReal.toReal_nonneg (a := y), hεy])).mpr hεy
      _ < ENNReal.ofReal (‖∫ θ in (0:ℝ)..1,
            unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ ^ 2) :=
          (ENNReal.ofReal_lt_ofReal_iff (p := (x - ε) ^ 2)
            (q := ‖∫ θ in (0:ℝ)..1,
              unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ * PN N θ * Ef m θ‖ ^ 2)
            (by linarith [sq_nonneg (x - ε), hsq])).mpr hsq
      _ ≤ FN N m := h2
  -- the bound for the partial sums
  have hbound : ∀ N, (∫⁻ m : ℤ, FN N m ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal ((Cp * Real.log (((T.image Prod.fst).card : ℝ)+2)^2)^2)
        * (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ)) := by
    intro N
    have hg := hP T (fun n => if n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) then cc n else 0)
      (Finset.Icc (-(N:ℤ)) (N:ℤ)) (fun n hn => if_neg hn)
    have hlhs : (∫⁻ m : ℤ, FN N m ∂MeasureTheory.Measure.count)
        = ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
            unNbhd T ((2:ℝ)^(-(j:ℝ)-1)) θ *
            (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
              (if n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) then cc n else 0) *
                Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) *
            Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count := by
      refine lintegral_congr (fun m => ?_)
      rw [hFN]
      simp only []
      congr 1
      refine iSup_congr (fun j => ?_)
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [hPN]
      congr 2
      refine Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
    have hrhs : (∫⁻ n : ℤ, ‖(if n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) then cc n else 0)‖ₑ^(2:ℝ)
          ∂MeasureTheory.Measure.count)
        = ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖ₑ^(2:ℝ) := by
      rw [MeasureTheory.lintegral_count]
      rw [tsum_eq_sum (s := Finset.Icc (-(N:ℤ)) (N:ℤ))
        (f := fun n : ℤ => ‖(if n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) then cc n else 0)‖ₑ^(2:ℝ))
        (fun n hn => by rw [if_neg hn]; simp)]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [if_pos hn]
    rw [hlhs]
    refine le_trans hg ?_
    rw [hrhs]
    suffices hchain : (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖ₑ^(2:ℝ))
        ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ) by
      exact mul_le_mul_right hchain _
    have hbes := fourierCoeff_partial_sum_sq_le G N
    have h1 : (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖ₑ^(2:ℝ))
        = ENNReal.ofReal (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖^2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [enorm_eq_ofReal_norm'', ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have h2 : ENNReal.ofReal (∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ‖cc n‖^2)
        ≤ ENNReal.ofReal (∫ t : AddCircle (1:ℝ), ‖G t‖ ^ 2
            ∂AddCircle.haarAddCircle (T := 1)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      simpa [hcc] using hbes
    have h3 : ENNReal.ofReal (∫ t : AddCircle (1:ℝ), ‖G t‖ ^ 2
          ∂AddCircle.haarAddCircle (T := 1))
        = ∫⁻ t : AddCircle (1:ℝ), ‖G t‖ₑ ^ (2:ℝ) ∂AddCircle.haarAddCircle (T := 1) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        ((Lp.memLp G).integrable_norm_pow (by norm_num))
        (Eventually.of_forall (fun t => by positivity))]
      refine lintegral_congr (fun t => ?_)
      rw [enorm_eq_ofReal_norm'', ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have h4 : (∫⁻ t : AddCircle (1:ℝ), ‖G t‖ₑ ^ (2:ℝ) ∂AddCircle.haarAddCircle (T := 1))
        = ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ) := by
      rw [lintegral_liftIoc_eq Q]
      refine lintegral_congr_ae ?_
      filter_upwards [hGcoe] with t ht
      rw [ht]
    rw [h1]
    refine le_trans h2 ?_
    rw [h3, h4]
  -- assemble
  have hmain : (∫⁻ m : ℤ, FQ m ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal ((Cp * Real.log (((T.image Prod.fst).card : ℝ)+2)^2)^2)
        * (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ)) := by
    calc (∫⁻ m : ℤ, FQ m ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ m : ℤ, Filter.liminf (fun N => FN N m) atTop ∂MeasureTheory.Measure.count :=
          lintegral_mono hpoint
      _ ≤ Filter.liminf (fun N => ∫⁻ m : ℤ, FN N m ∂MeasureTheory.Measure.count) atTop :=
          lintegral_liminf_le' (fun N => (measurable_of_countable (FN N)).aemeasurable)
      _ ≤ ENNReal.ofReal ((Cp * Real.log (((T.image Prod.fst).card : ℝ)+2)^2)^2)
            * (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ^(2:ℝ)) := by
          refine Filter.liminf_le_of_le (h := ?_)
          intro b hb
          obtain ⟨N, hN⟩ := hb.exists
          exact le_trans hN (hbound N)
  refine le_trans hmain ?_
  refine mul_le_mul_left ?_ _
  refine ENNReal.ofReal_le_ofReal ?_
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  refine mul_le_mul_of_nonneg_left ?_ hCppos.le
  refine pow_le_pow_left₀ ?_ (log_card_image_le T) 2
  refine Real.log_nonneg ?_
  have : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  linarith



/-- **The target from the real-line band-pass multiplier maximal.**  Bourgain's Lemma 4.11 in
multiplier form (the last analytic input, itself a consequence of the windowed maximal
estimate `SmoothWindowMaximal`) implies the model `ℓ²` maximal estimate. -/
theorem quadratic_kernel_model_maximal_l2_of_multiplier_maximal (H : RealLineMultiplierMaximal) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
  quadratic_kernel_model_maximal_l2_of_circle_maximal
    (circleNeighborhoodMaximal_of_multiplierMaximal H)


namespace LThOp
open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology FourierTransform Convolution
open Commons.Analysis.Fourier


open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology FourierTransform Convolution
open Commons.Analysis.Fourier


namespace BandLift

noncomputable def bandPass (C : Set ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
    (𝓕 g) ξ * Set.indicator C (fun _ => (1 : ℂ)) ξ *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))

/-- Band-pass operators with frequency sets that agree on the fundamental domain agree. -/
lemma bandPass_congr (g : ℝ → ℂ) {C D : Set ℝ}
    (h : ∀ ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), (ξ ∈ C ↔ ξ ∈ D)) :
    ∀ x : ℝ, bandPass C g x = bandPass D g x := by
  intro x
  refine intervalIntegral.integral_congr (fun ξ hξ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hξ
  have hidx : Set.indicator C (fun _ => (1 : ℂ)) ξ = Set.indicator D (fun _ => (1 : ℂ)) ξ := by
    by_cases hC : ξ ∈ C
    · rw [Set.indicator_of_mem hC, Set.indicator_of_mem ((h ξ hξ).mp hC)]
    · rw [Set.indicator_of_notMem hC, Set.indicator_of_notMem]
      intro hcon
      exact hC ((h ξ hξ).mpr hcon)
  rw [hidx]

lemma bandPass_eq_fourierInv {C : Set ℝ} (f : ℝ → ℂ)
    (hf : MeasureTheory.Integrable f) (x : ℝ) :
    bandPass C f x
      = 𝓕⁻ (fun ξ : ℝ => Set.indicator C (fun _ => (1 : ℂ)) ξ *
          Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1 : ℂ)) ξ *
          (𝓕 f) ξ) x := by
  classical
  have harg : ∀ ξ : ℝ,
      (↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ) := by
    intro ξ
    rw [Real.inner_apply]
    push_cast
    ring
  rw [bandPass, Real.fourierInv_eq']
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae ?_
  have hnull : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume, ξ ≠ (-(1 / 2) : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa using MeasureTheory.measure_singleton (-(1 / 2) : ℝ)
  filter_upwards [hnull] with ξ hξ
  have hmem : ξ ∈ Set.Ioc (-(1 / 2) : ℝ) (1 / 2) ↔ ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
    constructor
    · intro h; exact ⟨le_of_lt h.1, h.2⟩
    · intro h
      rcases eq_or_lt_of_le h.1 with h1 | h1
      · exact absurd h1.symm hξ
      · exact ⟨h1, h.2⟩
  simp only [Set.indicator_apply]
  by_cases hI : ξ ∈ Set.Ioc (-(1 / 2) : ℝ) (1 / 2)
  · rw [if_pos hI, if_pos (hmem.mp hI), harg ξ]
    by_cases hC : ξ ∈ C
    · rw [if_pos hC]; ring
    · rw [if_neg hC]; ring
  · rw [if_neg hI, if_neg (fun h => hI (hmem.mpr h))]
    by_cases hC : ξ ∈ C
    · rw [if_pos hC]; ring
    · rw [if_neg hC]; ring

/-- The `2^{-j-1}`-neighbourhood of a finite set of frequencies. -/

noncomputable def freqNeigh (s : Finset ℝ) (j : ℕ) : Set ℝ :=
  {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}


def RealLineBandpassMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (f : ℝ → ℂ), Integrable f →
    ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖bandPass (freqNeigh s j) f x‖ₑ) ^ (2 : ℝ) ∂volume
      ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ (x : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂volume


lemma measurableSet_freqNeigh (s : Finset ℝ) (j : ℕ) : MeasurableSet (freqNeigh s j) := by
  have h : freqNeigh s j
      = ⋃ a ∈ s, Set.Icc (a - (2 : ℝ) ^ (-(j : ℝ) - 1)) (a + (2 : ℝ) ^ (-(j : ℝ) - 1)) := by
    ext ξ
    simp only [freqNeigh, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha, habs⟩
      rw [abs_le] at habs
      exact ⟨a, ha, by constructor <;> linarith [habs.1, habs.2]⟩
    · rintro ⟨a, ha, h1, h2⟩
      exact ⟨a, ha, by rw [abs_le]; constructor <;> linarith⟩
  rw [h]
  exact Finset.measurableSet_biUnion s (fun a _ => measurableSet_Icc)

/-- `freqNeigh s j` is bounded. -/
lemma isBounded_freqNeigh (s : Finset ℝ) (j : ℕ) : Bornology.IsBounded (freqNeigh s j) := by
  have h : freqNeigh s j
      = ⋃ a ∈ s, Set.Icc (a - (2 : ℝ) ^ (-(j : ℝ) - 1)) (a + (2 : ℝ) ^ (-(j : ℝ) - 1)) := by
    ext ξ
    simp only [freqNeigh, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha, habs⟩
      rw [abs_le] at habs
      exact ⟨a, ha, by constructor <;> linarith [habs.1, habs.2]⟩
    · rintro ⟨a, ha, h1, h2⟩
      exact ⟨a, ha, by rw [abs_le]; constructor <;> linarith⟩
  rw [h]
  exact (s.finite_toSet.isCompact_biUnion fun a _ => isCompact_Icc).isBounded


end BandLift
noncomputable def thOp {K : ℕ} (lam : Fin K → ℝ) (rho : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f y * (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
    (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)

/-- Membership scaling: `cθ` lies in the `cρ`-neighbourhood of `cλ` iff `θ` lies in the
`ρ`-neighbourhood of `λ` (for `c > 0`). -/
lemma mem_scale {K : ℕ} (lam : Fin K → ℝ) (rho c θ : ℝ) (hc : 0 < c) :
    (∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho) ↔ (∃ k : Fin K, |θ - lam k| ≤ rho) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : |c * θ - c * lam k| = c * |θ - lam k| := by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
    rw [h1] at hk
    exact le_of_mul_le_mul_left hk hc
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hk hc.le

/-- Scaling of the θ-symbol indicator. -/
lemma indicator_scale {K : ℕ} (lam : Fin K → ℝ) (rho c θ : ℝ) (hc : 0 < c) :
    Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho} (fun _ => (1:ℂ)) (c * θ)
      = Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho} (fun _ => (1:ℂ)) θ := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases h : ∃ k : Fin K, |θ - lam k| ≤ rho
  · have h' : ∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho := (mem_scale lam rho c θ hc).mpr h
    rw [if_pos h', if_pos h]
  · have h' : ¬ (∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho) :=
      fun hc' => h ((mem_scale lam rho c θ hc).mp hc')
    rw [if_neg h', if_neg h]

/-- Kernel scaling: the θ-symbol `nbhd(cλ, cρ)` at frequency `w` equals `c` times the
θ-symbol `nbhd(λ, ρ)` at frequency `c w`. -/
lemma kernel_scale {K : ℕ} (lam : Fin K → ℝ) (rho c w : ℝ) (hc : 0 < c) :
    (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
        (fun θ => Complex.exp (-(Complex.I * (w : ℂ) * (θ : ℂ)))) θ)
      = c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * ((c * w : ℝ) : ℂ) * (θ : ℂ)))) θ := by
  set Gc : ℝ → ℂ := fun θ => Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
      (fun θ => Complex.exp (-(Complex.I * (w : ℂ) * (θ : ℂ)))) θ with hGcdef
  set G1 : ℝ → ℂ := fun θ => Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
      (fun θ => Complex.exp (-(Complex.I * ((c * w : ℝ) : ℂ) * (θ : ℂ)))) θ with hG1def
  have hG : ∀ θ : ℝ, Gc (c * θ) = G1 θ := by
    intro θ
    rw [hGcdef, hG1def]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : ∃ k : Fin K, |θ - lam k| ≤ rho
    · have h' : ∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho := (mem_scale lam rho c θ hc).mpr h
      rw [if_pos h', if_pos h, Complex.ofReal_mul]
      congr 1
      push_cast
      ring
    · have h' : ¬ (∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho) :=
        fun hc' => h ((mem_scale lam rho c θ hc).mp hc')
      rw [if_neg h', if_neg h]
  have hset : {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
      = ⋃ k : Fin K, Set.Icc (c * lam k - c * rho) (c * lam k + c * rho) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨k, h1, h2⟩
      exact ⟨k, by linarith, by linarith⟩
    · rintro ⟨k, h1, h2⟩
      exact ⟨k, by linarith, by linarith⟩
  have h1 := MeasureTheory.Measure.integral_comp_mul_left Gc c
  simp only [hG] at h1
  rw [h1, Complex.real_smul, abs_of_pos (inv_pos.mpr hc)]
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hcC, one_mul]

/-- **Scaling of the θ-form band operator.**  Replacing the centres `λ` by `cλ` and the radius
`ρ` by `cρ` is the same as applying the unrescaled operator to `f(·/c)` and evaluating at `c x`. -/
theorem thOp_scale {K : ℕ} (lam : Fin K → ℝ) (rho c : ℝ) (hc : 0 < c) (f : ℝ → ℂ) (x : ℝ) :
    thOp (fun k => c * lam k) (c * rho) f x
      = thOp lam rho (fun y => f (y / c)) (c * x) := by
  unfold thOp
  -- step 1: the inner θ-integral scales
  have h1 : ∀ y : ℝ,
      (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      = c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ := by
    intro y
    simpa only [mul_sub] using kernel_scale lam rho c (x - y) hc
  have hmain : (∫ y, f y * (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = ∫ y, f y * (c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [h1 y]
  rw [hmain]
  -- substitute back: `z = c y`
  have hsub : ∀ y : ℝ,
      f y * (c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      = c * (f ((c * y) / c) * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ) := by
    intro y
    rw [mul_div_cancel_left₀ y hc.ne']
    ring
  rw [show (∫ y, f y * (c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = c * ∫ y, f ((c * y) / c) * (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ) from by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    exact hsub y]
  have h5 := MeasureTheory.Measure.integral_comp_mul_left
    (fun z : ℝ => f (z / c) * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
      (fun θ => Complex.exp (-(Complex.I * (((c * x - z : ℝ) : ℂ)) * (θ : ℂ)))) θ) c
  rw [h5, Complex.real_smul, abs_of_pos (inv_pos.mpr hc)]
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hcC, one_mul]

/-- `thOp` is the convolution with the band kernel of the indicator symbol. -/
lemma thOp_eq_conv {K : ℕ} (mu : Fin K → ℝ) (rho : ℝ) (f : ℝ → ℂ) :
    thOp mu rho f = fun x => ∫ y, f y * bandKernel
      (Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} (fun _ => (1:ℂ))) (x - y) := by
  funext x
  rw [thOp]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  rw [bandKernel]
  refine integral_congr_ae ?_
  filter_upwards with θ
  by_cases h : θ ∈ {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- The symbol set is the union of the corresponding closed intervals. -/
lemma nbhd_eq_iUnion {K : ℕ} (mu : Fin K → ℝ) (rho : ℝ) :
    {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho}
      = ⋃ k : Fin K, Set.Icc (mu k - rho) (mu k + rho) := by
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, by linarith, by linarith⟩
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, by linarith, by linarith⟩

/-- `thOp` of an `L²` function is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_thOp {K : ℕ} (mu : Fin K → ℝ) (rho : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) : AEStronglyMeasurable (thOp mu rho f) volume := by
  have hS : MeasurableSet {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} := by
    rw [nbhd_eq_iUnion]
    exact MeasurableSet.iUnion fun k : Fin K => measurableSet_Icc
  have hmeas : Measurable (bandKernel
      (Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} (fun _ => (1:ℂ)))) := by
    have h : bandKernel (Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} (fun _ => (1:ℂ)))
        = fun z : ℝ => ∫ θ : ℝ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho}
            (fun _ => (1:ℂ)) θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))) := rfl
    rw [h]
    refine StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right ?_)
    exact Measurable.stronglyMeasurable
      (Measurable.mul ((measurable_const.indicator hS).comp measurable_snd) (by fun_prop))
  rw [thOp_eq_conv]
  exact aestronglyMeasurable_conv hf hmeas

/-- The dilation identity for `∫⁻` along `y ↦ y / c`. -/
lemma lintegral_comp_div (c : ℝ) (hc : 0 < c) {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ y, F (y / c) = ENNReal.ofReal c * ∫⁻ u, F u := by
  have h := Sharp8.lintegral_comp_const_mul c⁻¹ (inv_ne_zero hc.ne') hF
  have h1 : ∀ y : ℝ, c⁻¹ * y = y / c := fun y => by rw [inv_mul_eq_div]
  simp only [h1] at h
  rwa [inv_inv, abs_of_pos hc] at h

/-- **The maximal form of the radius rescaling.**  If the θ-form convolution maximal estimate
holds with the dyadic θ-radii `2^{-(j:ℝ)-1}` and arbitrary centres `λ`, then it holds with the
rescaled θ-radii `c · 2^{-(j:ℝ)-1}` and rescaled centres `c · λ`, with the same constant: apply
the hypothesis to `f (·/c)` (whose `L²` norm is `c` times that of `f`), transport the supremum
with `thOp_scale`, and let the two factors of `c` cancel. -/
theorem conv_form_scaling
    (hconv : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ),
      MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) f x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (hc : 0 < c) (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ),
      MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := hconv
  refine ⟨C, hCpos, ?_⟩
  intro c hc K lam f hf
  set g : ℝ → ℂ := fun y => f (y / c) with hgdef
  -- the `L²` facts for `g`
  have hgasm : AEStronglyMeasurable g (volume : Measure ℝ) := by
    have hq : Measure.QuasiMeasurePreserving (fun y : ℝ => y / c) volume volume := by
      have h2 : (fun y : ℝ => y / c) = fun y => c⁻¹ • y := by
        funext y; simp [div_eq_inv_mul]
      rw [h2]
      exact Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hc.ne')
    exact hf.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  have hglin : ∫⁻ y, ‖g y‖ₑ ^ (2:ℝ) = ENNReal.ofReal c * ∫⁻ u, ‖f u‖ₑ ^ (2:ℝ) := by
    rw [hgdef]
    simp only []
    exact lintegral_comp_div c hc (hf.aestronglyMeasurable.enorm.pow_const (2:ℝ))
  have hflt : ∫⁻ u, ‖f u‖ₑ ^ (2:ℝ) < ⊤ :=
    lintegral_enorm_sq_lt_top_of_memLp hf
  have hgmem : MemLp g 2 (volume : Measure ℝ) :=
    memLp_two_of_lintegral_enorm_lt_top hgasm (by rw [hglin]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hflt)
  -- the hypothesis applied to `g`
  have hmain := hC K lam g hgmem
  -- pointwise transport
  have hpt : ∀ j : ℕ, ∀ u : ℝ,
      thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) g u
        = thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f (u / c) := by
    intro j u
    have h := thOp_scale lam ((2:ℝ) ^ (-(j : ℝ) - 1)) c hc f (u / c)
    rw [mul_div_cancel₀ u hc.ne'] at h
    exact h.symm
  -- transport the lintegral
  have hLHS : ∫⁻ u, (⨆ j : ℕ, ‖thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) g u‖ₑ) ^ (2:ℝ)
      = ENNReal.ofReal c
        * ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ) := by
    have h1 : ∀ u : ℝ, (⨆ j : ℕ, ‖thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) g u‖ₑ)
        = (⨆ j : ℕ, ‖thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f (u / c)‖ₑ) := by
      intro u
      exact iSup_congr (fun j => by rw [hpt j u])
    rw [lintegral_congr (fun u => by rw [h1 u])]
    exact lintegral_comp_div c hc
      ((AEMeasurable.iSup (fun j : ℕ => AEMeasurable.enorm ((aestronglyMeasurable_thOp
        (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) hf).aemeasurable))).pow_const (2:ℝ))
  -- combine
  rw [hLHS] at hmain
  rw [hglin] at hmain
  -- `ofReal c * X ≤ K * (ofReal c * Y)` gives `X ≤ K * Y`
  have hc0 : (ENNReal.ofReal c) ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hct : (ENNReal.ofReal c) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (ENNReal.mul_le_mul_iff_left hc0 hct).mp ?_
  calc (∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k)
          (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ)) * ENNReal.ofReal c
      = ENNReal.ofReal c * ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k)
          (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ) := mul_comm _ _
    _ ≤ ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2)
          * (ENNReal.ofReal c * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := hmain
    _ = (ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) * ENNReal.ofReal c := by
        rw [mul_comm (ENNReal.ofReal c) (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)), mul_assoc]





/-! ## `L²`-multiplier infrastructure (`BoundaryLayer`) used for the last-mile reduction

We work with `Lp ℂ 2 volume` and the multiplier operator
`BoundaryLayer.multiplier m hm F = 𝓕⁻ (mulLp m hm (𝓕 F))`, whose basic calculus
(`enorm_multiplier_sq`, `l2_multiplier_square_function`, `mulLp_coe`) lives in the commons file
`boundary_layer_l2`.  Here we add multiplicativity (composition) and the identification of the
multiplier by an indicator `1_C` with the pointwise band operator `bandOp C f`. -/

/-- `‖z‖ₑ ≤ 1` when `‖z‖ ≤ 1`. -/
lemma enorm_le_one_of_norm_le_one {z : ℂ} (h : ‖z‖ ≤ 1) : ‖z‖ₑ ≤ 1 := by
  rw [enorm_eq_ofReal_norm]
  simpa using ENNReal.ofReal_le_ofReal h

/-- The `L²` norm of a product with a function of pointwise norm `≤ 1`. -/
lemma enorm_mulLp_le (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmbd : ∀ ξ, ‖m ξ‖ ≤ 1) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.mulLp m hm g‖ₑ ≤ ‖g‖ₑ := by
  rw [BoundaryLayer.enorm_mulLp]
  have hle : ∀ ξ, ‖m ξ‖ₑ ^ (2:ℝ) ≤ 1 := by
    intro ξ
    calc ‖m ξ‖ₑ ^ (2:ℝ) ≤ 1 ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (enorm_le_one_of_norm_le_one (hmbd ξ)) (by norm_num)
      _ = 1 := by rw [ENNReal.one_rpow]
  calc (∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ)
      ≤ (∫⁻ ξ, 1 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        apply lintegral_mono; intro ξ
        have h2 : (0:ℝ≥0∞) ≤ ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ) := bot_le
        exact mul_le_mul_of_nonneg_right (hle ξ) h2
    _ = ‖g‖ₑ := by
        simp only [one_mul]
        rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral g, ← ENNReal.rpow_mul]
        norm_num

/-- `mulLp` is multiplicative. -/
lemma mulLp_mul (m m' : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hm' : MemLp m' ⊤ (volume : Measure ℝ))
    (hmm' : MemLp (m * m') ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.mulLp m hm (BoundaryLayer.mulLp m' hm' g)
      = BoundaryLayer.mulLp (m * m') hmm' g := by
  apply Lp.ext
  filter_upwards [BoundaryLayer.mulLp_coe m hm (BoundaryLayer.mulLp m' hm' g),
    BoundaryLayer.mulLp_coe m' hm' g, BoundaryLayer.mulLp_coe (m * m') hmm' g]
    with ξ h1 h2 h3
  simp only [Pi.mul_apply] at h1 h2 h3 ⊢
  rw [h1, h3, h2]
  ring

/-- **Composition of multiplier operators.** -/
lemma multiplier_comp (m m' : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hm' : MemLp m' ⊤ (volume : Measure ℝ))
    (hmm' : MemLp (m * m') ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm (BoundaryLayer.multiplier m' hm' g)
      = BoundaryLayer.multiplier (m * m') hmm' g := by
  unfold BoundaryLayer.multiplier
  have h1 : 𝓕 (𝓕⁻ (BoundaryLayer.mulLp m' hm' (𝓕 g)))
      = BoundaryLayer.mulLp m' hm' (𝓕 g) := FourierInvPair.fourier_fourierInv_eq _
  rw [h1, mulLp_mul m m' hm hm' hmm' (𝓕 g)]

/-- `Set.indicator C (𝓕 f) = (C.indicator 1) * 𝓕 f` pointwise. -/
lemma indicator_mul_fourier (C : Set ℝ) (f : ℝ → ℂ) :
    Set.indicator C (𝓕 f) = (Set.indicator C (fun _ => (1:ℂ))) * (𝓕 f) := by
  funext ξ
  simp only [Pi.mul_apply]
  by_cases h : ξ ∈ C <;> simp [Set.indicator_apply, h]

/-- **The bridge: the `L²` multiplier by `1_C`, applied to the `L²` class of `f`, is a.e. the
pointwise band operator `bandOp C f`.**  For `f ∈ L¹ ∩ L²` and a measurable set `C` of finite
measure. -/
theorem multiplier_indicator_ae_eq_bandOp {C : Set ℝ} (hC : MeasurableSet C)
    (hCfin : volume C < ⊤)
    (hm_top : MemLp (Set.indicator C (fun _ => (1:ℂ))) ⊤ (volume : Measure ℝ))
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((BoundaryLayer.multiplier (Set.indicator C (fun _ => (1:ℂ))) hm_top (hf2.toLp f) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] bandOp C f := by
  set m : ℝ → ℂ := Set.indicator C (fun _ => (1:ℂ)) with hmdef
  have hm1 : MemLp m 1 (volume : Measure ℝ) :=
    memLp_indicator_const 1 hC (1:ℂ) (Or.inr hCfin.ne)
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 hC (1:ℂ) (Or.inr hCfin.ne)
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  have hfour : ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
    Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp hf1 hf2
  have hFTtop : MemLp (𝓕 f) ⊤ (volume : Measure ℝ) := by
    refine memLp_top_of_bound
      (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier hf1).aestronglyMeasurable
      (∫ x, ‖f x‖) ?_
    filter_upwards with ξ
    exact Commons.Analysis.Fourier.norm_fourier_le f ξ
  have hFT2 : MemLp (𝓕 f) 2 (volume : Measure ℝ) :=
    Commons.Analysis.Fourier.memLp_fourier hfi hf2
  have hprod1' : MemLp (fun x => 𝓕 f x * m x) 1 (volume : Measure ℝ) := hFTtop.mul' hm1
  have hprod2' : MemLp (fun x => 𝓕 f x * m x) 2 (volume : Measure ℝ) := hFT2.mul' hm_top
  have hprod1 : MemLp (m * 𝓕 f) 1 (volume : Measure ℝ) :=
    MemLp.ae_eq (Filter.Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]; ring)) hprod1'
  have hprod2 : MemLp (m * 𝓕 f) 2 (volume : Measure ℝ) :=
    MemLp.ae_eq (Filter.Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]; ring)) hprod2'
  have hFcoe : (BoundaryLayer.mulLp m hm_top (𝓕 (hf2.toLp f)) : ℝ → ℂ)
      =ᵐ[volume] m * 𝓕 f := by
    filter_upwards [BoundaryLayer.mulLp_coe m hm_top (𝓕 (hf2.toLp f)), hfour] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hFeq : BoundaryLayer.mulLp m hm_top (𝓕 (hf2.toLp f))
      = MemLp.toLp (m * 𝓕 f) hprod2 := by
    apply Lp.ext
    filter_upwards [hFcoe, MemLp.coeFn_toLp hprod2] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have key : ((BoundaryLayer.multiplier m hm_top (hf2.toLp f) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ (m * 𝓕 f) := by
    change ((𝓕⁻ (BoundaryLayer.mulLp m hm_top (𝓕 (hf2.toLp f))) :
      Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ (m * 𝓕 f)
    rw [hFeq]
    exact Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hprod1 hprod2
  refine key.trans ?_
  have hband : bandOp C f = 𝓕⁻ (m * 𝓕 f) := by
    funext x
    simp only [hmdef, bandOp]
    rw [indicator_mul_fourier]
  rw [hband]


/-! ## The last mile: the target from the multiplier form of the convolution maximal estimate

The single clean input left is `MaximalMultiplierBound` below: the arbitrary-centre,
dyadic-radius (`2^{-j-1}`) convolution maximal estimate stated for `L²` classes with the
`L²` multiplier calculus of `BoundaryLayer`.  It is what the commons chain

    `SmoothWindowMaximal` ⟹ `separated_maximal_of_smooth_window` (1-separated sharp θ-form)
      ⟹ `neighborhood_maximal_arbitrary_of_separated` (arbitrary λ, θ-radii `2^{-j-1}`)

produces after (i) the radius-scaling `c = 2π` (the θ-form is invariant under
`λ ↦ cλ`, `ρ ↦ cρ` together with `f ↦ f(·/c)`) and (ii) the θ-form↔multiplier bridge
(`∫ y, f y · bandKernel m (x-y) = 2π 𝓕⁻ (m(-2π·) 𝓕 f) x` for `f ∈ L¹∩L²`, extended to `L²`
by truncation).  Everything below is unconditional. -/

/-- The `r`-neighbourhood of a finite set of frequencies. -/
def nbhdSet (s : Finset ℝ) (j : ℕ) : Set ℝ :=
  {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}

lemma nbhdSet_eq_freqNeigh (s : Finset ℝ) (j : ℕ) :
    nbhdSet s j = BandLift.freqNeigh s j := rfl

/-- The indicator symbol of `nbhdSet s j`. -/
noncomputable def nbhdInd (s : Finset ℝ) (j : ℕ) : ℝ → ℂ := Set.indicator (nbhdSet s j) (fun _ => (1:ℂ))

lemma memLp_nbhdInd (s : Finset ℝ) (j : ℕ) : MemLp (nbhdInd s j) ⊤ (volume : Measure ℝ) := by
  have := BandLift.measurableSet_freqNeigh s j
  have hfin : volume (nbhdSet s j) < ⊤ := by
    have hb := BandLift.isBounded_freqNeigh s j
    rw [nbhdSet_eq_freqNeigh]
    exact hb.measure_lt_top
  exact memLp_indicator_const ⊤ this (1:ℂ) (Or.inr hfin.ne)

lemma norm_nbhdInd_le (s : Finset ℝ) (j : ℕ) (ξ : ℝ) : ‖nbhdInd s j ξ‖ ≤ 1 := by
  by_cases h : ξ ∈ nbhdSet s j
  · rw [nbhdInd, Set.indicator_of_mem h]; simp
  · rw [nbhdInd, Set.indicator_of_notMem h]; simp

/-- θ-form band operator with the θ-symbol a union of equal intervals. -/
def MaximalMultiplierBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (F : Lp ℂ 2 (volume : Measure ℝ)),
    ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
        Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2 : ℝ)
      ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖F‖ₑ ^ (2 : ℝ)

/-- The fundamental-domain indicator is an `L^∞` symbol. -/
lemma memLp_domInd :
    MemLp (Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ))) ⊤
      (volume : Measure ℝ) :=
  memLp_indicator_const ⊤ measurableSet_Icc (1:ℂ)
    (Or.inr (ne_of_lt (isCompact_Icc.measure_lt_top (μ := volume))))

lemma norm_domInd_le (ξ : ℝ) :
    ‖Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ)) ξ‖ ≤ 1 := by
  by_cases h : ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

/-- On the fundamental domain, `nbhdSet s j ∩ dom = freqNeigh s j ∩ dom`. -/
lemma nbhdInterDom_eq (s : Finset ℝ) (j : ℕ) :
    nbhdSet s j ∩ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
      = BandLift.freqNeigh s j ∩ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
  rw [nbhdSet_eq_freqNeigh]

/-- **θ-form/multiplier bridge, `L¹ ∩ L²` case.**  For a bounded compactly supported symbol `m`
and `g ∈ L¹ ∩ L²`, the θ-form convolution `∫ y, g y · bandKernel m (x-y)` is a.e. `2π` times the
`L²` multiplier with symbol `m (-2π ·)` applied to the `L²` class of `g`. -/
theorem theta_form_eq_multiplier_of_memLp_one {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1) (hsupp : HasCompactSupport m)
    (hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ))
    {g : ℝ → ℂ} (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    (fun x : ℝ => ∫ y : ℝ, g y * bandKernel m (x - y))
      =ᵐ[volume] fun x : ℝ => (2 * Real.pi : ℂ) *
        ((BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x := by
  have hm1 : MemLp m 1 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hmbd)
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hmbd)
  -- pointwise formula for the θ-form operator
  have hpoint : ∀ x : ℝ, (∫ y : ℝ, g y * bandKernel m (x - y))
      = (2 * Real.pi : ℂ) * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 g ξ) x := by
    intro x
    rw [bandOp_pointwise m g hmm hm1 hm2 hm hg1 hg2 x, twoPiC_coe]
    push_cast
    ring
  -- the multiplier side
  have hfm : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ) := hmc
  have hfour : ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 g :=
    fourier_toLp_ae_eq_fourier_of_memLp hg1 hg2
  have hFTtop : MemLp (𝓕 g) ⊤ (volume : Measure ℝ) :=
    memLp_top_of_bound (BoundaryLayer.measurable_fourier hg1).aestronglyMeasurable
      (∫ x, ‖g x‖) (Filter.Eventually.of_forall (fun ξ => norm_fourier_le g ξ))
  have hFT2 : MemLp (𝓕 g) 2 (volume : Measure ℝ) := memLp_fourier (memLp_one_iff_integrable.mp hg1) hg2
  have hsupp' : HasCompactSupport (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) :=
    hasCompactSupport_comp_mul m hsupp (-(2 * Real.pi))
      (by intro h; linarith [Real.pi_pos, h])
  have hm1' : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) 1 (volume : Measure ℝ) :=
    hsupp'.memLp_of_bound hmc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ξ => hmbd (-(2 * Real.pi) * ξ)))
  have hprod2 : MemLp ((fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) * 𝓕 g) 2 (volume : Measure ℝ) :=
    hmc.mul' hFT2
  have hprod1 : MemLp ((fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) * 𝓕 g) 1 (volume : Measure ℝ) :=
    hm1'.mul' hFTtop
  have hcoe : (BoundaryLayer.mulLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (𝓕 (hg2.toLp g)) :
        ℝ → ℂ)
      =ᵐ[volume] (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) * 𝓕 g := by
    filter_upwards [BoundaryLayer.mulLp_coe (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc
      (𝓕 (hg2.toLp g)), hfour] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have heq : BoundaryLayer.mulLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (𝓕 (hg2.toLp g))
      = MemLp.toLp _ hprod2 := by
    apply Lp.ext
    filter_upwards [hcoe, MemLp.coeFn_toLp hprod2] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2
    rw [h1, h2]
  have hmult : ((BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 g ξ) := by
    change ((𝓕⁻ (BoundaryLayer.mulLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc
      (𝓕 (hg2.toLp g))) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 g ξ)
    rw [heq]
    exact fourierInv_toLp_ae_eq_fourierInv hprod1 hprod2
  filter_upwards [hmult] with x hx
  rw [hpoint x, hx]

/-- **`mulLp` is additive in its `Lp` argument** — the argument-version companion of the
commons `BoundaryLayer.mulLp_sub` / `multiplier_sub`, which are the *symbol*-difference versions.
Here the two sides involve different functions (`m * ↑(g-h)` vs `m * ↑g - m * ↑h`), so the
a.e.-congruence is separated out first and `MemLp.toLp_sub` is applied with every argument pinned. -/
lemma mulLp_sub_arg {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (g h : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.mulLp m hm (g - h)
      = BoundaryLayer.mulLp m hm g - BoundaryLayer.mulLp m hm h := by
  have hmem_g : MemLp (m * (g : ℝ → ℂ)) 2 (volume : Measure ℝ) := hm.mul (Lp.memLp g)
  have hmem_h : MemLp (m * (h : ℝ → ℂ)) 2 (volume : Measure ℝ) := hm.mul (Lp.memLp h)
  have h₁ : BoundaryLayer.mulLp m hm (g - h)
      = MemLp.toLp (m * (g : ℝ → ℂ) - m * (h : ℝ → ℂ)) (hmem_g.sub hmem_h) := by
    rw [BoundaryLayer.mulLp]
    exact MemLp.toLp_congr (hm.mul (Lp.memLp (g - h))) (hmem_g.sub hmem_h)
      (by
        filter_upwards [MeasureTheory.Lp.coeFn_sub (μ := volume) g h] with x hx
        simp only [Pi.mul_apply, Pi.sub_apply]
        rw [hx]
        simp only [Pi.sub_apply]
        ring)
  have h₂ : MemLp.toLp (m * (g : ℝ → ℂ) - m * (h : ℝ → ℂ)) (hmem_g.sub hmem_h)
      = MemLp.toLp (m * (g : ℝ → ℂ)) hmem_g - MemLp.toLp (m * (h : ℝ → ℂ)) hmem_h :=
    MemLp.toLp_sub hmem_g hmem_h
  rw [h₁, h₂, BoundaryLayer.mulLp, BoundaryLayer.mulLp]

/-- The band kernel of a measurable symbol is measurable (as an integral of a measurable family). -/
lemma measurable_bandKernel {m : ℝ → ℂ} (hmm : Measurable m) : Measurable (bandKernel m) := by
  have h : bandKernel m
      = fun z : ℝ => ∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))) := rfl
  rw [h]
  refine StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right ?_)
  exact Measurable.stronglyMeasurable (Measurable.mul (hmm.comp measurable_snd) (by fun_prop))

/-- The θ-form convolution operator of an `L²` class is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_thetaOp {m : ℝ → ℂ} (hmm : Measurable m)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)) volume :=
  aestronglyMeasurable_conv (Lp.memLp G) (measurable_bandKernel hmm)

/-- **The θ-form convolution operator is bounded on `L²`.**  This is
`bandOp_l2_multiplier_bound` (commons) with the inner kernel written as `bandKernel`; the
constant `400` is inherited.  Together with `aestronglyMeasurable_thOp` this makes
`G ↦ (fun x => ∫ y, G y * bandKernel m (x - y)).toLp` a bounded linear map on `Lp ℂ 2 volume`. -/
lemma thetaOp_lintegral_le {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal 400 * ‖G‖ₑ ^ (2:ℝ) := by
  have h := bandOp_l2_multiplier_bound m hmm hmbd hsupp (G : ℝ → ℂ) (Lp.memLp G)
  rw [BoundaryLayer.lp_enorm_sq_eq_lintegral G]
  refine le_trans (le_of_eq ?_) h
  apply lintegral_congr
  intro x
  have hK : (fun y : ℝ => (G : ℝ → ℂ) y * bandKernel m (x - y))
      = fun y : ℝ => (G : ℝ → ℂ) y * (∫ θ, m θ *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := by
    funext y
    simp only [bandKernel]
  rw [hK]

/-- Multipliers with a.e. equal symbols agree. -/
lemma multiplier_congr_ae {m m' : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hm' : MemLp m' ⊤ (volume : Measure ℝ)) (h : m =ᵐ[volume] m')
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm F = BoundaryLayer.multiplier m' hm' F := by
  unfold BoundaryLayer.multiplier
  congr 1
  apply Lp.ext
  filter_upwards [BoundaryLayer.mulLp_coe m hm (𝓕 F), BoundaryLayer.mulLp_coe m' hm' (𝓕 F),
    h] with ξ h1 h2 h3
  simp only [Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2, h3]

/-- The intersection symbol is the product of the two indicators. -/
lemma nbhdInd_mul_domInd (s : Finset ℝ) (j : ℕ) :
    nbhdInd s j * Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ))
      = Set.indicator (nbhdSet s j ∩ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ)) := by
  funext ξ
  simp only [Pi.mul_apply, Set.indicator_apply, nbhdInd]
  by_cases h1 : ξ ∈ nbhdSet s j <;> by_cases h2 : ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) <;>
    simp_all [Set.mem_inter_iff]

/-- **The real-line band-pass maximal estimate follows from `MaximalMultiplierBound`.**

For `f ∈ L¹ ∩ L²` the route is: `bandPass (freqNeigh s j) f` is a.e. the `L²` multiplier by
`1_{nbhdSet s j ∩ dom}` applied to `hf2.toLp f` (the bridge `multiplier_indicator_ae_eq_bandOp`),
and by composition of multipliers this equals `multiplier (nbhdInd s j) (P F)` where
`P := multiplier 1_dom`, since `1_{nbhdSet s j} * 1_dom = 1_{nbhdSet s j ∩ dom}`.  The
hypothesis then bounds `⨆_j |multiplier (nbhdInd s j) (P F)|` by
`C log(#s+2)² ‖P F‖ₑ ≤ C log(#s+2)² ‖F‖ₑ = C log(#s+2)² (∫⁻ ‖f‖ₑ²)^{1/2}`.  For
`f ∉ L²` the right-hand side is infinite. -/
theorem realLineBandpassMaximal_of_multiplierBound (h : MaximalMultiplierBound) :
    BandLift.RealLineBandpassMaximal := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, ?_⟩
  intro s f hf1
  by_cases hf2 : MemLp f 2 (volume : Measure ℝ)
  · set F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hFdef
    set dom : Set ℝ := Set.Icc (-(1 / 2) : ℝ) (1 / 2) with hdomdef
    set mdom : ℝ → ℂ := Set.indicator dom (fun _ => (1:ℂ)) with hmdomdef
    have hmdtop : MemLp mdom ⊤ (volume : Measure ℝ) := memLp_domInd
    set P : Lp ℂ 2 (volume : Measure ℝ) := BoundaryLayer.multiplier mdom hmdtop F with hPdef
    have hf1' : MemLp f 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hf1
    -- the per-`j` identification of the two operators
    have key : ∀ j : ℕ,
        (fun x => BandLift.bandPass (BandLift.freqNeigh s j) f x)
          =ᵐ[volume]
        (fun x => (BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P :
          Lp ℂ 2 (volume : Measure ℝ)) x) := by
      intro j
      have hCmeas : MeasurableSet (nbhdSet s j ∩ dom) :=
        (BandLift.measurableSet_freqNeigh s j).inter measurableSet_Icc
      have hCfin : volume (nbhdSet s j ∩ dom) < ⊤ :=
        ((BandLift.isBounded_freqNeigh s j).subset Set.inter_subset_left).measure_lt_top
      have hmC : MemLp (Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ))) ⊤
          (volume : Measure ℝ) :=
        memLp_indicator_const ⊤ hCmeas (1:ℂ) (Or.inr hCfin.ne)
      have hsym : nbhdInd s j * mdom = Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ)) := by
        have h := nbhdInd_mul_domInd s j
        simp only [hdomdef, hmdomdef] at h ⊢
        exact h
      have hmul : MemLp (nbhdInd s j * mdom) ⊤ (volume : Measure ℝ) := hsym ▸ hmC
      -- (a) `bandPass` is the multiplier by the clipped indicator of the `L²` class of `f`
      have hbp : (fun x => BandLift.bandPass (BandLift.freqNeigh s j) f x)
          =ᵐ[volume]
          (fun x => (BoundaryLayer.multiplier
            (Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ))) hmC F :
              Lp ℂ 2 (volume : Measure ℝ)) x) := by
        filter_upwards [multiplier_indicator_ae_eq_bandOp hCmeas hCfin hmC hf1' hf2]
          with x hx
        rw [hx, BandLift.bandPass_eq_fourierInv f hf1 x]
        have hfun : (fun ξ => Set.indicator (BandLift.freqNeigh s j) (fun _ => (1:ℂ)) ξ
              * Set.indicator dom (fun _ => (1:ℂ)) ξ * (𝓕 f) ξ)
            = fun ξ => Set.indicator (nbhdSet s j ∩ dom) (𝓕 f) ξ := by
          funext ξ
          rw [← nbhdSet_eq_freqNeigh]
          simp only [Pi.mul_apply, Set.indicator_apply]
          by_cases h1 : ξ ∈ nbhdSet s j <;> by_cases h2 : ξ ∈ dom <;>
            simp_all [Set.mem_inter_iff]
        rw [hfun]
        rfl
      -- (b) composition of multipliers
      have hcomp : BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P
          = BoundaryLayer.multiplier (Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ)))
              hmC F := by
        rw [hPdef, multiplier_comp (nbhdInd s j) mdom (memLp_nbhdInd s j) hmdtop hmul F]
        exact multiplier_congr_ae hmul hmC
          (Filter.Eventually.of_forall (fun ξ => congrFun hsym ξ)) F
      rw [hcomp]
      exact hbp
    -- the pointwise supremum is the same almost everywhere
    have hLHS : ∫⁻ x, (⨆ j : ℕ, ‖BandLift.bandPass (BandLift.freqNeigh s j) f x‖ₑ) ^ (2:ℝ)
        = ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P :
            Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2:ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun j => key j)] with x hx
      congr 1
      exact iSup_congr (fun j => by rw [hx j])
    rw [hLHS]
    have hPnorm : ‖P‖ₑ ≤ ‖F‖ₑ := by
      rw [hPdef]
      calc ‖BoundaryLayer.multiplier mdom hmdtop F‖ₑ
          = ‖BoundaryLayer.mulLp mdom hmdtop (𝓕 F)‖ₑ := BoundaryLayer.enorm_fourierInv _
        _ ≤ ‖𝓕 F‖ₑ := enorm_mulLp_le mdom hmdtop (fun ξ => norm_domInd_le ξ) (𝓕 F)
        _ = ‖F‖ₑ := BoundaryLayer.enorm_fourier F
    have hFnorm : ‖F‖ₑ ^ (2:ℝ) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
      rw [BoundaryLayer.lp_enorm_sq_eq_lintegral F]
      apply lintegral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (μ := volume) hf2] with x hx
      rw [hx]
    calc ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P :
            Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖P‖ₑ ^ (2:ℝ) :=
          hC s P
      _ ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖F‖ₑ ^ (2:ℝ) := by
          exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hPnorm (by norm_num)) zero_le
      _ = ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2)
            * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by rw [hFnorm]
  · -- the `¬ L²` case: the right-hand side is infinite
    have htop : ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) = ⊤ := by
      by_contra hne
      exact hf2 (memLp_two_of_lintegral_enorm_lt_top hf1.aestronglyMeasurable
        (lt_top_iff_ne_top.mpr hne))
    have hne0 : (ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2)) ≠ 0 := by
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      refine pow_pos ?_ 2
      exact mul_pos hCpos (pow_pos (Real.log_pos (by
        have : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
        linarith)) 2)
    rw [htop, ENNReal.mul_top hne0]
    exact le_top

set_option maxHeartbeats 2000000

/-! ## The `L²` form of the θ↔multiplier bridge -/

private lemma fourier_sub_lp2 (f g : Lp ℂ 2 (volume : Measure ℝ)) : 𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ) (f - g)
    = (Lp.fourierTransformₗᵢ ℝ ℂ) f - (Lp.fourierTransformₗᵢ ℝ ℂ) g
  exact map_sub _ _ _

private lemma fourierInv_sub_lp2 (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    𝓕⁻ (f - g) = 𝓕⁻ f - 𝓕⁻ g := by
  change ((Lp.fourierTransformₗᵢ ℝ ℂ)).symm (f - g)
    = (Lp.fourierTransformₗᵢ ℝ ℂ).symm f - (Lp.fourierTransformₗᵢ ℝ ℂ).symm g
  exact map_sub _ _ _

lemma multiplier_sub_arg {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (F G : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm (F - G)
      = BoundaryLayer.multiplier m hm F - BoundaryLayer.multiplier m hm G := by
  simp only [BoundaryLayer.multiplier]
  rw [fourier_sub_lp2, mulLp_sub_arg hm]
  exact fourierInv_sub_lp2 _ _

private lemma enorm_sq_eq_aux (z : ℂ) : ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [BoundaryLayer.enorm_eq_ofReal_norm,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (norm_nonneg z)]

private lemma ofReal_sq_rpow_aux (B : ℝ) (hB : 0 ≤ B) :
    (ENNReal.ofReal B) ^ (2:ℝ) = ENNReal.ofReal (B ^ 2) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hB]

private lemma enorm_toReal_aux (x : Lp ℂ 2 (volume : Measure ℝ)) : (‖x‖ₑ).toReal = ‖x‖ := by
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Operator-norm bound for the multiplier with a symbol bounded by `B`. -/
lemma enorm_multiplier_le {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f‖ₑ ≤ ENNReal.ofReal B * ‖f‖ₑ := by
  have hb : ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by
    calc ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ ξ, ENNReal.ofReal (B ^ 2) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          refine lintegral_mono (fun ξ => mul_le_mul' ?_ le_rfl)
          rw [enorm_sq_eq_aux]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hB ξ) 2)
      _ = ENNReal.ofReal (B ^ 2) * ∫⁻ ξ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (B ^ 2) * ‖𝓕 f‖ₑ ^ (2:ℝ) := by
          rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral (𝓕 f)]
      _ = ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by rw [BoundaryLayer.enorm_fourier]
  have hsq : ‖BoundaryLayer.multiplier m hm f‖ₑ ^ (2:ℝ)
      ≤ (ENNReal.ofReal B * ‖f‖ₑ) ^ (2:ℝ) := by
    rw [BoundaryLayer.enorm_multiplier_sq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ofReal_sq_rpow_aux B hBnn]
    exact hb
  have h2 := ENNReal.rpow_le_rpow hsq (show (0:ℝ) ≤ 1/2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one,
       ← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one] at h2

/-- The multiplier operator is `B`-Lipschitz on `L²`. -/
lemma norm_multiplier_sub_le {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f - BoundaryLayer.multiplier m hm g‖ ≤ B * ‖f - g‖ := by
  have h := enorm_multiplier_le hm B hBnn hB (f - g)
  rw [multiplier_sub_arg hm] at h
  have hfin : ENNReal.ofReal B * ‖f - g‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
  have hle := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hBnn, enorm_toReal_aux, enorm_toReal_aux] at hle
  exact hle

/-- The θ-form convolution of an `L²` class is square-integrable. -/
lemma memLp_thetaOp {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => ∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)) 2
      (volume : Measure ℝ) := by
  refine memLp_two_of_lintegral_enorm_lt_top (aestronglyMeasurable_thetaOp hmm G) ?_
  refine lt_of_le_of_lt (thetaOp_lintegral_le hmm hmbd hsupp G) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hG2 : ‖G‖ₑ ^ (2:ℝ) < ⊤ := by
    rw [BoundaryLayer.lp_enorm_sq_eq_lintegral]
    exact lintegral_enorm_sq_lt_top_of_memLp (Lp.memLp G)
  exact hG2

/-- The θ-form convolution operator as an endomorphism of `Lp ℂ 2 volume`. -/
noncomputable def thetaOpLp {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_thetaOp hmm hmbd hsupp G).toLp (fun x : ℝ => ∫ y : ℝ,
    (G : ℝ → ℂ) y * bandKernel m (x - y))

lemma thetaOpLp_coe {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    (thetaOpLp hmm hmbd hsupp G : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ => ∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y) :=
  MemLp.coeFn_toLp _

lemma thetaOpLp_sub {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G H : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaOpLp hmm hmbd hsupp (G - H)
      = thetaOpLp hmm hmbd hsupp G - thetaOpLp hmm hmbd hsupp H := by
  have hK : MemLp (bandKernel m) 2 (volume : Measure ℝ) :=
    bandKernel_memLp m hmm hmbd hsupp
  have hae : ((G - H : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      (G : ℝ → ℂ) - (H : ℝ → ℂ) := Lp.coeFn_sub G H
  apply Lp.ext
  filter_upwards [thetaOpLp_coe hmm hmbd hsupp (G - H),
    thetaOpLp_coe hmm hmbd hsupp G, thetaOpLp_coe hmm hmbd hsupp H,
    Lp.coeFn_sub (thetaOpLp hmm hmbd hsupp G) (thetaOpLp hmm hmbd hsupp H)] with x h1 h2 h3 h5
  simp only [Pi.sub_apply] at h5
  rw [h1, h5, h2, h3]
  have hKx : MemLp (fun y : ℝ => bandKernel m (x - y)) 2 (volume : Measure ℝ) :=
    hK.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)
  have hGint : Integrable (fun y : ℝ => (G : ℝ → ℂ) y * bandKernel m (x - y)) volume :=
    (Lp.memLp G).integrable_mul hKx
  have hHint : Integrable (fun y : ℝ => (H : ℝ → ℂ) y * bandKernel m (x - y)) volume :=
    (Lp.memLp H).integrable_mul hKx
  have hstep1 : ∫ y : ℝ, ((G - H : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y
        * bandKernel m (x - y)
      = ∫ y : ℝ, (((G : ℝ → ℂ) y - (H : ℝ → ℂ) y) * bandKernel m (x - y)) :=
    integral_congr_ae (hae.mono (fun y hy => by
      show ((G - H : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y * bandKernel m (x - y)
        = ((G : ℝ → ℂ) y - (H : ℝ → ℂ) y) * bandKernel m (x - y)
      rw [hy, Pi.sub_apply]))
  have hstep2 : ∫ y : ℝ, (((G : ℝ → ℂ) y - (H : ℝ → ℂ) y) * bandKernel m (x - y))
      = ∫ y : ℝ, ((G : ℝ → ℂ) y * bandKernel m (x - y)
          - (H : ℝ → ℂ) y * bandKernel m (x - y)) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  rw [hstep1, hstep2, integral_sub hGint hHint]

/-- The θ-form operator is bounded by `20` in operator norm on `L²`. -/
lemma enorm_thetaOpLp_le {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖thetaOpLp hmm hmbd hsupp G‖ₑ ≤ 20 * ‖G‖ₑ := by
  have h1 : ‖thetaOpLp hmm hmbd hsupp G‖ₑ ^ (2:ℝ)
      = ∫⁻ x : ℝ, ‖∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)‖ₑ ^ (2:ℝ) := by
    rw [BoundaryLayer.lp_enorm_sq_eq_lintegral]
    refine lintegral_congr_ae ?_
    filter_upwards [thetaOpLp_coe hmm hmbd hsupp G] with x hx
    rw [hx]
  have h2 : ∫⁻ x : ℝ, ‖∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal 400 * ‖G‖ₑ ^ (2:ℝ) := thetaOp_lintegral_le hmm hmbd hsupp G
  have h3 : ‖thetaOpLp hmm hmbd hsupp G‖ₑ ^ (2:ℝ) ≤ (20 * ‖G‖ₑ) ^ (2:ℝ) := by
    rw [h1]
    refine le_trans h2 (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    norm_num
  have h4 := ENNReal.rpow_le_rpow h3 (show (0:ℝ) ≤ 1/2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one,
       ← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one] at h4

lemma norm_thetaOpLp_sub_le {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G H : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖thetaOpLp hmm hmbd hsupp G - thetaOpLp hmm hmbd hsupp H‖ ≤ 20 * ‖G - H‖ := by
  have h := enorm_thetaOpLp_le hmm hmbd hsupp (G - H)
  rw [thetaOpLp_sub hmm hmbd hsupp G H] at h
  have hfin : (20:ℝ≥0∞) * ‖G - H‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
  have hle := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, enorm_toReal_aux, enorm_toReal_aux] at hle
  exact hle

/-- **The `L¹ ∩ L²` case of the θ↔multiplier bridge at the level of `Lp` classes.** -/
lemma thetaOpLp_eq_multiplier_of_memLp_one {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1) (hsupp : HasCompactSupport m)
    (hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ))
    {g : ℝ → ℂ} (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    thetaOpLp hmm hmbd hsupp (hg2.toLp g)
      = (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g) := by
  have hbase := theta_form_eq_multiplier_of_memLp_one hm hmm hmbd hsupp hmc hg1 hg2
  apply Lp.ext
  filter_upwards [thetaOpLp_coe hmm hmbd hsupp (hg2.toLp g), hbase,
    Lp.coeFn_smul (2 * Real.pi : ℂ)
      (BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g))]
    with x h1 h2 h3
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  rw [h1, h3]
  have hstep : ∫ y : ℝ, ((hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y
        * bandKernel m (x - y)
      = ∫ y : ℝ, g y * bandKernel m (x - y) :=
    integral_congr_ae ((MemLp.coeFn_toLp hg2).mono (fun y hy => by simp only [hy]))
  rw [hstep, h2]

/-- `L¹ ∩ L²` functions (as `L²` classes) are dense in `L²(ℝ)`. -/
theorem dense_range_memLp_one_two :
    Dense (Set.range (fun g : {g : ℝ → ℂ // MemLp g 1 (volume : Measure ℝ) ∧
        MemLp g 2 (volume : Measure ℝ)} => g.2.2.toLp g.1)) := by
  rw [Metric.dense_iff]
  intro F r hr
  have hε : (ENNReal.ofReal (r / 2)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  obtain ⟨g, hgε, hg1, hg2⟩ := MemLp.induction_dense (p := 2) (E := ℂ) (μ := volume)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞)
    (fun f : ℝ → ℂ => MemLp f 1 (volume : Measure ℝ) ∧ MemLp f 2 (volume : Measure ℝ))
    (by
      intro c s hs hμs ε hε'
      refine ⟨s.indicator (fun _ => c), ?_, memLp_indicator_const 1 hs c (Or.inr hμs.ne),
        memLp_indicator_const 2 hs c (Or.inr hμs.ne)⟩
      simp)
    (by intro f g hf hg; exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩)
    (Lp.memLp F) (ε := ENNReal.ofReal (r / 2)) hε
  have hcoe : (((F - hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
      =ᵐ[volume] (F : ℝ → ℂ) - g := by
    filter_upwards [Lp.coeFn_sub F (hg2.toLp g), MemLp.coeFn_toLp hg2] with x hx hy
    simp only [Pi.sub_apply, hx, hy]
  have hnorm : ‖F - hg2.toLp g‖ ≤ r / 2 := by
    rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith : (0:ℝ) ≤ r / 2) hgε
  refine ⟨hg2.toLp g, ?_, ⟨⟨g, hg1, hg2⟩, rfl⟩⟩
  have h2 : dist F (hg2.toLp g) ≤ r / 2 := by
    rw [dist_eq_norm]; exact hnorm
  rw [Metric.mem_ball, dist_comm]
  exact lt_of_le_of_lt h2 (by linarith)

/-- **θ-form/multiplier bridge, `L²` case.**  For a bounded compactly supported symbol `m`, the
θ-form convolution operator is `2π` times the `L²` multiplier with symbol `m (-2π ·)`, on all of
`L²`: the `L¹ ∩ L²` identity extends by density, using the additivity and boundedness of the two
operators. -/
theorem theta_form_eq_multiplier_L2 {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1) (hsupp : HasCompactSupport m)
    (hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ))
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaOpLp hmm hmbd hsupp G
      = (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc G := by
  have hcont1 : Continuous
      (fun F : Lp ℂ 2 (volume : Measure ℝ) => thetaOpLp hmm hmbd hsupp F) := by
    refine LipschitzWith.continuous (K := 20) (LipschitzWith.of_dist_le_mul ?_)
    intro F H
    rw [dist_eq_norm, dist_eq_norm]
    simpa using norm_thetaOpLp_sub_le hmm hmbd hsupp F H
  have hcont2 : Continuous (fun F : Lp ℂ 2 (volume : Measure ℝ) =>
      (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F) := by
    refine (LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul ?_)).const_smul
      (2 * Real.pi : ℂ)
    intro F H
    rw [dist_eq_norm, dist_eq_norm]
    have h := norm_multiplier_sub_le (m := fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc 1
      (by norm_num) (fun ξ => hmbd (-(2 * Real.pi) * ξ)) F H
    simpa using h
  have hclosed : IsClosed {F : Lp ℂ 2 (volume : Measure ℝ) |
      thetaOpLp hmm hmbd hsupp F - (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F = 0} :=
    isClosed_eq (hcont1.sub hcont2) continuous_const
  have hsub : Set.range (fun g : {g : ℝ → ℂ // MemLp g 1 (volume : Measure ℝ) ∧
      MemLp g 2 (volume : Measure ℝ)} => g.2.2.toLp g.1) ⊆
      {F : Lp ℂ 2 (volume : Measure ℝ) | thetaOpLp hmm hmbd hsupp F - (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F = 0} := by
    rintro F ⟨g, rfl⟩
    rw [Set.mem_ofPred_eq]
    rw [thetaOpLp_eq_multiplier_of_memLp_one hm hmm hmbd hsupp hmc g.2.1 g.2.2, sub_self]
  have hcl : closure (Set.range (fun g : {g : ℝ → ℂ // MemLp g 1 (volume : Measure ℝ) ∧
      MemLp g 2 (volume : Measure ℝ)} => g.2.2.toLp g.1)) ⊆
      {F : Lp ℂ 2 (volume : Measure ℝ) | thetaOpLp hmm hmbd hsupp F - (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F = 0} :=
    (closure_mono hsub).trans hclosed.closure_subset
  rw [dense_range_memLp_one_two.closure_eq] at hcl
  exact sub_eq_zero.mp (hcl (Set.mem_univ G))

private lemma enorm_le_enorm_two_pi_mul (z : ℂ) : ‖z‖ₑ ≤ ‖(2 * Real.pi : ℂ) * z‖ₑ := by
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    have h₁ : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h₁, show ‖(((2 * Real.pi : ℝ)) : ℂ)‖ = |2 * Real.pi| from by simp,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have h1 : (1 : ℝ≥0∞) ≤ ‖(2 * Real.pi : ℂ)‖ₑ := by
    rw [BoundaryLayer.enorm_eq_ofReal_norm, ENNReal.one_le_ofReal, hnorm]
    linarith [Real.pi_gt_three]
  calc ‖z‖ₑ = 1 * ‖z‖ₑ := (one_mul _).symm
    _ ≤ ‖(2 * Real.pi : ℂ)‖ₑ * ‖z‖ₑ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(2 * Real.pi : ℂ) * z‖ₑ := (enorm_mul _ _).symm

lemma multiplier_le_thOp {s : Finset ℝ} (F : Lp ℂ 2 (volume : Measure ℝ)) (j : ℕ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
          Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ
        ≤ ‖thOp (fun k : Fin s.card => 2 * Real.pi * (-(((s.equivFin.symm k : s) : ℝ))))
            (2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1)) (F : ℝ → ℂ) x‖ₑ := by
  classical
  set ν : Fin s.card → ℝ := fun k => ((s.equivFin.symm k : s) : ℝ) with hν
  set rho : ℝ := 2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1) with hrho
  set m : ℝ → ℂ := Set.indicator
    {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho} (fun _ => (1 : ℂ)) with hm
  have hset : MeasurableSet {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho} := by
    have : {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho}
        = ⋃ k : Fin s.card,
          Set.Icc (2 * Real.pi * (-(ν k)) - rho) (2 * Real.pi * (-(ν k)) + rho) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨k, h1, h2⟩; exact ⟨k, by linarith, by linarith⟩
      · rintro ⟨k, h1, h2⟩; exact ⟨k, by linarith, by linarith⟩
    rw [this]
    exact MeasurableSet.iUnion fun k => measurableSet_Icc
  have hmm : Measurable m := by
    rw [hm]; exact measurable_const.indicator hset
  have hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1 := by
    intro θ
    rw [hm]
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hsupp : HasCompactSupport m := by
    refine HasCompactSupport.intro (K := ⋃ k : Fin s.card,
      Set.Icc (2 * Real.pi * (-(ν k)) - rho) (2 * Real.pi * (-(ν k)) + rho))
      (isCompact_iUnion fun k => isCompact_Icc) ?_
    intro x hx
    rw [hm]
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hx (Set.mem_iUnion.mpr (by
      rcases hmem with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [Set.mem_Icc]
      obtain ⟨h1, h2⟩ := abs_le.mp hk
      constructor <;> linarith))
  have hmtop : MemLp m ⊤ (volume : Measure ℝ) :=
    memLp_top_of_bound hmm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hmbd)
  have hcomp : (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) = nbhdInd s j := by
    funext ξ
    rw [hm, nbhdInd, Set.indicator_apply, Set.indicator_apply]
    have hiff : (-(2 * Real.pi) * ξ ∈
          {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho})
        ↔ ξ ∈ nbhdSet s j := by
      rw [Set.mem_ofPred_eq, nbhdSet, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨ν k, ?_, ?_⟩
        · have hk' : ν k = ((s.equivFin.symm k : s) : ℝ) := by rw [hν]
          rw [hk']
          exact Finset.mem_coe.mpr (s.equivFin.symm k).property
        have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
        have h1 : |-(2 * Real.pi) * ξ - 2 * Real.pi * (-(ν k))|
            = 2 * Real.pi * |ν k - ξ| := by
          rw [show -(2 * Real.pi) * ξ - 2 * Real.pi * (-(ν k)) = 2 * Real.pi * (ν k - ξ)
              by ring, abs_mul, abs_of_pos htwopi]
        rw [h1, hrho] at hk
        have h2 := le_of_mul_le_mul_left hk htwopi
        rwa [abs_sub_comm] at h2
      · rintro ⟨a, ha, ha'⟩
        set k : Fin s.card := s.equivFin ⟨a, Finset.mem_coe.mp ha⟩ with hk
        refine ⟨k, ?_⟩
        have hνa : ν k = a := by
          rw [hν, hk]
          simp only [Equiv.symm_apply_apply]
        rw [hrho, hνa]
        have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
        calc |-(2 * Real.pi) * ξ - 2 * Real.pi * (-a)|
            = 2 * Real.pi * |a - ξ| := by
              rw [show -(2 * Real.pi) * ξ - 2 * Real.pi * (-a) = 2 * Real.pi * (a - ξ) by ring,
                  abs_mul, abs_of_pos htwopi]
          _ = 2 * Real.pi * |ξ - a| := by rw [abs_sub_comm]
          _ ≤ 2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1) :=
              mul_le_mul_of_nonneg_left ha' htwopi.le
    by_cases h : (-(2 * Real.pi) * ξ ∈
        {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho})
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ) := by
    rw [hcomp]; exact memLp_nbhdInd s j
  have hsym : ∀ ξ : ℝ, m (-(2 * Real.pi) * ξ) = nbhdInd s j ξ := fun ξ => congrFun hcomp ξ
  have hbridge : (2 * Real.pi : ℂ) •
      BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F
        = thetaOpLp hmm hmbd hsupp F := by
    rw [← multiplier_congr_ae hmc (memLp_nbhdInd s j)
      (Filter.Eventually.of_forall hsym) F]
    exact (theta_form_eq_multiplier_L2 hmtop hmm hmbd hsupp hmc F).symm
  have hth : ∀ x : ℝ, (∫ y : ℝ, (F : ℝ → ℂ) y * bandKernel m (x - y))
      = thOp (fun k : Fin s.card => 2 * Real.pi * (-(ν k))) rho (F : ℝ → ℂ) x := by
    intro x
    simp only [thOp_eq_conv, hm]
  filter_upwards [thetaOpLp_coe hmm hmbd hsupp F,
    Lp.coeFn_smul (2 * Real.pi : ℂ)
      (BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F)] with x h1 h2
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  have hcoe : ((thetaOpLp hmm hmbd hsupp F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      = ((2 * Real.pi : ℂ) •
          BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) :=
    congrArg (fun Y : Lp ℂ 2 (volume : Measure ℝ) => (Y : ℝ → ℂ)) hbridge.symm
  calc ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
          Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ
      = ‖(((BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ := rfl
    _ ≤ ‖(2 * Real.pi : ℂ) *
          ((BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ :=
        enorm_le_enorm_two_pi_mul _
    _ = ‖(((2 * Real.pi : ℂ) •
          BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ := by rw [h2]
    _ = ‖((thetaOpLp hmm hmbd hsupp F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ := by
        rw [hcoe]
    _ = ‖thOp (fun k : Fin s.card => 2 * Real.pi * (-(ν k))) rho (F : ℝ → ℂ) x‖ₑ := by
        rw [h1, hth]

/-- **`MaximalMultiplierBound` from the sharp 1-separated θ-form maximal (`hsep`).** -/
theorem maximalMultiplierBound_of_sepWinTarget (h : Commons.Analysis.Fourier.SepWin.TargetStatement) :
    MaximalMultiplierBound := by
  have hsep : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (mu : Fin K → ℝ),
      (∀ i j : Fin K, i ≠ j → 1 ≤ |mu i - mu j|) →
      ∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (mu k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(mu k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ≤ ENNReal.ofReal ((C * (Real.log ((K : ℝ) + 2)) ^ 2) ^ 2)
            * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
    obtain ⟨C, hCpos, hC⟩ := h
    refine ⟨C, hCpos, fun K mu hmu f hf => ?_⟩
    have := hC K mu hmu f hf
    simpa [Commons.Analysis.Fourier.SepWin.sharpOp, Commons.Analysis.Fourier.SepWin.innerSharp,
      Commons.Analysis.Fourier.SepWin.hJ] using this
  obtain ⟨C₁, hC₁pos, hC₁⟩ := neighborhood_maximal_arbitrary_of_separated hsep
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    conv_form_scaling ⟨C₁, hC₁pos, fun K lam f hf => hC₁ K lam f hf⟩
  refine ⟨C₂, hC₂pos, ?_⟩
  intro s F
  have hmain := hC₂ (2 * Real.pi) (by positivity) s.card
    (fun k : Fin s.card => -(((s.equivFin.symm k : s) : ℝ))) (F : ℝ → ℂ) (Lp.memLp F)
  rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral F] at hmain
  have hsup : ∀ᵐ x ∂(volume : Measure ℝ),
      (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
          Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ)
        ≤ (⨆ j : ℕ, ‖thOp
            (fun k : Fin s.card => 2 * Real.pi * (-(((s.equivFin.symm k : s) : ℝ))))
            (2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1)) (F : ℝ → ℂ) x‖ₑ) := by
    filter_upwards [ae_all_iff.mpr (fun j => multiplier_le_thOp F j)] with x hx
    exact iSup_mono (fun j => hx j)
  calc ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
        Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2 : ℝ)
      ≤ ∫⁻ x, (⨆ j : ℕ, ‖thOp
          (fun k : Fin s.card => 2 * Real.pi * (-(((s.equivFin.symm k : s) : ℝ))))
          (2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1)) (F : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) :=
        lintegral_mono_ae (hsup.mono (fun x hx => ENNReal.rpow_le_rpow hx (by norm_num)))
    _ ≤ ENNReal.ofReal ((C₂ * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖F‖ₑ ^ (2 : ℝ) := hmain

/-- **The real-line band-pass multiplier maximal from the sharp 1-separated θ-form maximal.** -/
theorem realLineMultiplierMaximal_of_sepWinTarget
    (h : Commons.Analysis.Fourier.SepWin.TargetStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (f : ℝ → ℂ), Integrable f →
      ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖∫ ξ in (-(1/2):ℝ)..(1/2),
          (𝓕 f) ξ *
          Set.indicator {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2:ℝ)^(-(j:ℝ)-1)} (fun _ => (1:ℂ)) ξ *
          Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))‖ₑ)^(2:ℝ) ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((s.card:ℝ)+2)^2)^2) * ∫⁻ x, ‖f x‖ₑ^(2:ℝ) ∂(volume : Measure ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := realLineBandpassMaximal_of_multiplierBound
    (maximalMultiplierBound_of_sepWinTarget h)
  refine ⟨C, hCpos, fun s f hf => ?_⟩
  have := hC s f hf
  simpa only [BandLift.bandPass, BandLift.freqNeigh] using this


end LThOp

/-- **The target from the windowed maximal estimate** (Bourgain's Lemma 4.13 / 4.26, the single
deep input).  This is the last reduction: `SmoothWindowMaximal` is the only remaining
hypothesis. -/
theorem quadratic_kernel_model_maximal_l2_of_smoothWindow
    (hSWM : Commons.Analysis.Fourier.SepWin.SmoothWindowMaximal) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
  quadratic_kernel_model_maximal_l2_of_multiplier_maximal
    (LThOp.realLineMultiplierMaximal_of_sepWinTarget
      (Commons.Analysis.Fourier.SepWin.target_of_components hSWM))

/-- **The target from the sharp `1`-separated θ-form maximal** (Bourgain's Lemma 4.1/4.11). -/
theorem quadratic_kernel_model_maximal_l2_of_targetStatement
    (h : Commons.Analysis.Fourier.SepWin.TargetStatement) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
  quadratic_kernel_model_maximal_l2_of_multiplier_maximal
    (LThOp.realLineMultiplierMaximal_of_sepWinTarget h)

namespace FWPortBump
open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology FourierTransform Convolution
open Commons.Analysis.Fourier

noncomputable section

/-- The `k`-th band symbol `1_{[λ-h,λ+h]}·φ((·-λ)/h)` as a complex-valued function. -/
def bandSym (φ : ℝ → ℝ) (lamk h : ℝ) : ℝ → ℂ :=
  (Set.Icc (lamk - h) (lamk + h)).indicator fun θ => (φ ((θ - lamk) / h) : ℂ)

lemma bandSym_apply (φ : ℝ → ℝ) (lamk h θ : ℝ) :
    bandSym φ lamk h θ =
      if θ ∈ Set.Icc (lamk - h) (lamk + h) then (φ ((θ - lamk) / h) : ℂ) else 0 :=
  Set.indicator_apply _ _ _

lemma bandSym_measurable {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (lamk h : ℝ) :
    Measurable (bandSym φ lamk h) := by
  refine Measurable.indicator ?_ measurableSet_Icc
  exact Complex.measurable_ofReal.comp ((hφ 1).continuous.measurable.comp (by fun_prop))

lemma bandSym_bound {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lamk h θ : ℝ) :
    ‖bandSym φ lamk h θ‖ ≤ 2 := by
  rw [bandSym_apply]
  split
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact hbd _
  · simp

/-- The total band symbol `∑_k bandSym φ (λ_k) h`. -/
def bandSumSym {K : ℕ} (φ : ℝ → ℝ) (lam : Fin K → ℝ) (h : ℝ) : ℝ → ℂ :=
  fun θ => ∑ k : Fin K, bandSym φ (lam k) h θ

lemma bandSumSym_measurable {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (lam : Fin K → ℝ) (h : ℝ) : Measurable (bandSumSym φ lam h) :=
  Finset.measurable_sum _ (fun k _ => bandSym_measurable hφ _ _)

lemma bandSumSym_bound {K : ℕ} {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, |φ x| ≤ 2)
    (lam : Fin K → ℝ) (h θ : ℝ) : ‖bandSumSym φ lam h θ‖ ≤ 2 * K := by
  calc ‖bandSumSym φ lam h θ‖ ≤ ∑ k : Fin K, ‖bandSym φ (lam k) h θ‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, (2:ℝ) := Finset.sum_le_sum (fun k _ => bandSym_bound hbd _ _ _)
    _ = 2 * K := by simp [mul_comm]

/-- A nonnegative bound for the `λ_k`. -/
lemma exists_abs_bound {K : ℕ} (lam : Fin K → ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ k : Fin K, |lam k| ≤ M := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    exact ⟨0, le_refl 0, fun k => absurd k.isLt (Nat.not_lt_zero k.val)⟩
  · haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    obtain ⟨k0, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin K))
      (fun k => |lam k|) Finset.univ_nonempty
    exact ⟨|lam k0|, abs_nonneg _, fun k => hmax k (Finset.mem_univ k)⟩

lemma bandSumSym_support_measure_ne_top {K : ℕ} {φ : ℝ → ℝ} (lam : Fin K → ℝ) (h : ℝ) :
    (volume : Measure ℝ) (Function.support (bandSumSym φ lam h)) ≠ ∞ := by
  obtain ⟨M, hMnn, hM⟩ := exists_abs_bound lam
  have hsub : Function.support (bandSumSym φ lam h) ⊆ Set.Icc (-(M + |h|)) (M + |h|) := by
    intro θ hθ
    by_contra hcon
    apply hθ
    rw [bandSumSym]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [bandSym_apply, if_neg]
    intro hmem
    simp only [Set.mem_Icc, not_and_or, not_le] at hcon hmem
    have hkle := abs_le.mp (hM k)
    rcases hcon with hc | hc
    · have h3 : lam k < -M := by linarith [hmem.1, hc, le_abs_self h]
      have : M < |lam k| := by
        rw [abs_of_neg (by linarith)]
        linarith
      linarith [hkle.2]
    · have h3 : M < lam k := by linarith [hmem.2, hc, le_abs_self h]
      have : M < |lam k| := by
        rw [abs_of_pos (by linarith)]
        linarith
      linarith [hkle.1]
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

lemma bandSumSym_memLp_one {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) 1 (volume : Measure ℝ) :=
  (memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))
    ).mono_exponent_of_measure_support_ne_top
      (s := Function.support (bandSumSym φ lam h)) (fun _ hx => Function.notMem_support.mp hx)
      (bandSumSym_support_measure_ne_top lam h) le_top

lemma bandSumSym_memLp_two {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) 2 (volume : Measure ℝ) :=
  (memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))
    ).mono_exponent_of_measure_support_ne_top
      (s := Function.support (bandSumSym φ lam h)) (fun _ hx => Function.notMem_support.mp hx)
      (bandSumSym_support_measure_ne_top lam h) le_top

lemma bandSumSym_memLp_top {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))

/-- **Identification of the smooth band sum with a single Fourier multiplier.**
For `f ∈ L¹ ∩ L²`, the target's double integral is the single multiplier
`ξ ↦ (∑_k φ(-(2πξ+λ_k)/h))` applied to `𝓕 f`, times `2π`. -/
theorem bandSum_eq_single_multiplier {K : ℕ} (lam : Fin K → ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hbd : ∀ x : ℝ, |φ x| ≤ 2)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {h : ℝ} (hh : 0 < h) {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    (∫ y, f y * (∑ k : Fin K, ∫ θ in (lam k - h)..(lam k + h),
        (φ ((θ - lam k) / h) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = 2 * Real.pi * FourierTransformInv.fourierInv
          (fun ξ : ℝ => (∑ k : Fin K, (φ (-((2 * Real.pi * ξ + lam k) / h)) : ℂ)) *
            FourierTransform.fourier f ξ) x := by

  have hcont : Continuous φ := (hφ 1).continuous
  have hsym : ∀ ξ : ℝ, bandSumSym φ lam h (-(2 * Real.pi) * ξ)
      = ∑ k : Fin K, (φ (-((2 * Real.pi * ξ + lam k) / h)) : ℂ) := by
    intro ξ
    rw [bandSumSym]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [bandSym_apply]
    by_cases hmem : -(2 * Real.pi) * ξ ∈ Set.Icc (lam k - h) (lam k + h)
    · rw [if_pos hmem]
      congr 1
      field_simp
      ring
    · rw [if_neg hmem]
      symm
      rw [Complex.ofReal_eq_zero]
      apply hsupp
      have hnot : ¬ ((-(2 * Real.pi) * ξ) ∈ Set.Icc (lam k - h) (lam k + h)) := hmem
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      have key : (1:ℝ) ≤ |(-((2 * Real.pi * ξ + lam k) / h))| := by
        rw [abs_neg, abs_div, abs_of_pos hh, le_div_iff₀ hh, one_mul]
        rcases hnot with h1 | h1
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_neg (by linarith)]; linarith
      exact key
  have hstep : ∀ y : ℝ,
      (∫ θ, bandSumSym φ lam h θ * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
      = ∑ k : Fin K, ∫ θ in (lam k - h)..(lam k + h),
          (φ ((θ - lam k) / h) : ℂ) * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))) := by
    intro y
    simp only [bandSumSym, Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [intervalIntegral.integral_of_le (by linarith : lam k - h ≤ lam k + h),
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with θ
      rw [bandSym_apply, Set.indicator_apply]
      by_cases hθ : θ ∈ Set.Icc (lam k - h) (lam k + h)
      · by_cases hθ' : θ ∈ Set.Ioc (lam k - h) (lam k + h)
        · simp [hθ, hθ']
        · have hθe : θ = lam k - h := by
            simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hθ'
            rcases hθ' with hc | hc
            · linarith [hθ.1, hc]
            · exfalso; linarith [hθ.2, hc]
          rw [if_pos hθ, if_neg hθ', hθe]
          have h1 : (lam k - h - lam k) / h = -1 := by
            field_simp
            ring
          rw [h1, hsupp (-1) (by norm_num : (1:ℝ) ≤ |(-1:ℝ)|)]
          simp
      · rw [if_neg hθ]
        by_cases hθ' : θ ∈ Set.Ioc (lam k - h) (lam k + h)
        · exact absurd (Set.Ioc_subset_Icc_self hθ') hθ
        · simp [hθ']
    · intro k _
      have hm : MeasurableSet (Set.Icc (lam k - h) (lam k + h)) := measurableSet_Icc
      have hint : IntegrableOn (fun θ : ℝ => (φ ((θ - lam k) / h) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
          (Set.Icc (lam k - h) (lam k + h)) volume :=
        ContinuousOn.integrableOn_compact isCompact_Icc
          ((Continuous.mul (Complex.continuous_ofReal.comp (hcont.comp (by fun_prop)))
            (Complex.continuous_exp.comp (by fun_prop))).continuousOn)
      have hI : Integrable ((Set.Icc (lam k - h) (lam k + h)).indicator
          (fun θ : ℝ => (φ ((θ - lam k) / h) : ℂ) *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))) volume :=
        hint.integrable_indicator hm
      have hfun : (fun θ : ℝ => bandSym φ (lam k) h θ *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
          = (Set.Icc (lam k - h) (lam k + h)).indicator (fun θ : ℝ =>
              (φ ((θ - lam k) / h) : ℂ) *
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := by
        funext θ
        rw [bandSym_apply, Set.indicator_apply]
        by_cases hθ : θ ∈ Set.Icc (lam k - h) (lam k + h) <;> simp [hθ]
      rw [hfun]
      exact hI
  have hLHS : (∫ y, f y * (∑ k : Fin K, ∫ θ in (lam k - h)..(lam k + h),
        (φ ((θ - lam k) / h) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = ∫ y, f y * (∫ θ, bandSumSym φ lam h θ *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hstep y]
  rw [hLHS, convolution_kernel_fubini (bandSumSym φ lam h) f (bandSumSym_measurable hφ lam h)
      (bandSumSym_memLp_one hφ hbd lam h) (bandSumSym_memLp_two hφ hbd lam h)
      (bandSumSym_memLp_top hφ hbd lam h) hf1 hf2 x]
  have hfun : (fun ξ : ℝ => bandSumSym φ lam h (-(2 * Real.pi) * ξ) *
      FourierTransform.fourier f ξ)
      = (fun ξ : ℝ => (∑ k : Fin K, (φ (-((2 * Real.pi * ξ + lam k) / h)) : ℂ)) *
          FourierTransform.fourier f ξ) := by
    funext ξ
    rw [hsym]
  rw [hfun]

end


open _root_.MeasureTheory Finset
open scoped BigOperators ENNReal FourierTransform

noncomputable section

/-! ### The fixed bump used to split the window, and the annulus (remainder) estimate

These are the two ingredients of the reduction `φ = A + g` explained in
`Submission/Work/Analysis/Fourier/SINGLE_MULTIPLIER_REDUCTION.md`: the *fixed* bump `winA`
and the *annulus* window `g = φ - winA`, whose band-sum maximal function is bounded on `L²`
by `(8π)²` **uniformly in the annulus profile** — no dependence on the number `K` of
frequencies or on `φ`. -/


/-- The *fixed* `C^∞` bump `A` used to split a window `φ` of the target's class as `φ = A + g`:
`A = 1` on `[-1/2,1/2]`, `A = 0` off `[-1,1]`, `0 ≤ A ≤ 1`. -/
def winA (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * x) * Real.smoothTransition (2 + 2 * x)

lemma winA_contDiff (n : ℕ) : ContDiff ℝ n winA := by
  unfold winA
  exact ContDiff.mul
    ((Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop))
    ((Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop))

lemma winA_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : winA x = 1 := by
  have h1 : (1 : ℝ) ≤ 2 - 2 * x := by
    have := (abs_le.mp hx).2; linarith
  have h2 : (1 : ℝ) ≤ 2 + 2 * x := by
    have := (abs_le.mp hx).1; linarith
  unfold winA
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

lemma winA_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : winA x = 0 := by
  rcases le_total 0 x with h | h
  · have h1 : 2 - 2 * x ≤ 0 := by
      have := (abs_of_nonneg h) ▸ hx; linarith
    unfold winA
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  · have h2 : 2 + 2 * x ≤ 0 := by
      have hx' : 1 ≤ -x := by rw [abs_of_nonpos h] at hx; linarith
      linarith
    unfold winA
    rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]

lemma winA_nonneg (x : ℝ) : 0 ≤ winA x := by
  unfold winA
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma winA_le_one (x : ℝ) : winA x ≤ 1 := by
  unfold winA
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/-- For a window `φ` of the target's class, the annulus profile `g = φ - A` vanishes on
`[-1/2,1/2]` and off `[-1,1]`, and is bounded by `2`. -/
lemma winA_sub_supp {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (x : ℝ) :
    ¬ ((1 : ℝ) / 2 < |x| ∧ |x| ≤ 1) → φ x - winA x = 0 := by
  intro hx
  rcases not_and_or.mp hx with h | h
  · have : |x| ≤ 1 / 2 := le_of_not_gt h
    rw [h1 x this, winA_eq_one this, sub_self]
  · have : 1 ≤ |x| := le_of_not_ge h
    rw [h0 x this, winA_eq_zero this, sub_self]

lemma winA_sub_bound {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (x : ℝ) :
    ‖φ x - winA x‖ ≤ 2 := by
  have h1 := hbd x
  have h2 := winA_nonneg x
  have h3 := winA_le_one x
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- The dyadic scale `t_j = 2^{j+1}`. -/
def scaleT (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1)

lemma scaleT_pos (j : ℕ) : 0 < scaleT j := by
  rw [scaleT]; positivity

lemma scaleT_ge_two (j : ℕ) : 2 ≤ scaleT j := by
  rw [scaleT]
  calc (2:ℝ) = 2 ^ (1:ℕ) := by norm_num
    _ ≤ 2 ^ (j + 1) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)

/-- At most two `1`-separated points of `ℝ` can lie in an interval of length `≤ 1`. -/
lemma card_le_two_separated {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {c r : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1) :
    (Finset.univ.filter (fun k : Fin K => |lam k - c| ≤ r)).card ≤ 2 := by
  classical
  set S : Finset (Fin K) := Finset.univ.filter (fun k : Fin K => |lam k - c| ≤ r) with hS
  have hmem : ∀ k : Fin K, k ∈ S ↔ |lam k - c| ≤ r := by intro k; rw [hS]; simp
  have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |lam x - c| = r := by
    intro x hx y hy hxy
    have h1 : 1 ≤ |lam x - lam y| := hsep x y hxy
    have h3 : |lam x - lam y| ≤ |lam x - c| + |lam y - c| := by
      calc |lam x - lam y| = |(lam x - c) - (lam y - c)| := by congr 1; ring
        _ ≤ |lam x - c| + |lam y - c| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (lam x - c) 0 (lam y - c)
    have h4 : |lam x - c| ≤ r := (hmem x).mp hx
    have h5 : |lam y - c| ≤ r := (hmem y).mp hy
    have h6 := abs_nonneg (lam x - c)
    have h7 := abs_nonneg (lam y - c)
    nlinarith [h1, h3, h4, h5, h6, h7]
  by_cases h : S.card ≤ 2
  · exact h
  · simp only [not_le] at h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have hall : ∀ x ∈ S, |lam x - c| = r := by
      intro x hx
      rcases eq_or_ne x a with h' | h'
      · rw [h']; exact key a ha b hb hab
      · exact key x hx a ha h'
    have hinj : Set.InjOn lam (↑S : Set (Fin K)) := by
      intro u hu v hv huv
      by_contra hne'
      have h1 : 1 ≤ |lam u - lam v| := hsep u v hne'
      rw [huv, sub_self, abs_zero] at h1
      linarith
    have himg : (S.image lam).card = S.card := Finset.card_image_of_injOn hinj
    have hsub : S.image lam ⊆ ({c - r, c + r} : Finset ℝ) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have := hall x hx
      rcases (abs_eq (le_of_lt hr)).mp this with h' | h'
      · simp [show lam x = c + r by linarith]
      · simp [show lam x = c - r by linarith]
    have hcard := Finset.card_le_card hsub
    have h2 : ({c - r, c + r} : Finset ℝ).card ≤ 2 := by
      rcases eq_or_ne (c - r) (c + r) with h' | h'
      · rw [h']; simp
      · rw [Finset.card_insert_of_notMem (by simp [h'])]; simp
    omega

/-- The annulus multiplier `M_j^g(η) = 2π ∑_k g(-t_j(η+λ_k))`. -/
def annulusMul {K : ℕ} (g : ℝ → ℂ) (lam : Fin K → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun η => 2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (η + lam k)))

/-- Pointwise bound for the annulus multiplier. -/
lemma annulusMul_bound {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (η : ℝ) (j : ℕ) :
    ‖annulusMul g lam j η‖ ≤ 8 * Real.pi := by
  rw [annulusMul]
  have hS : (Finset.univ.filter
      (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card ≤ 2 := by
    have hr : (0:ℝ) < (scaleT j)⁻¹ := inv_pos.mpr (scaleT_pos j)
    have hr2 : 2 * (scaleT j)⁻¹ ≤ 1 := by
      have h2 := scaleT_ge_two j
      have h3 : (1:ℝ) / scaleT j ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
      rw [inv_eq_one_div]
      linarith
    exact card_le_two_separated hsep hr hr2
  have hzero : ∀ k : Fin K, ¬ (|lam k - (-η)| ≤ (scaleT j)⁻¹) →
      g (-(scaleT j * (η + lam k))) = 0 := by
    intro k hk
    apply hg_supp
    intro hcon
    apply hk
    have h1 : scaleT j * |η + lam k| ≤ 1 := by
      have := hcon.2
      rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos j)] at this
      exact this
    rw [sub_neg_eq_add, show lam k + η = η + lam k by ring, inv_eq_one_div,
      le_div_iff₀ (scaleT_pos j), mul_comm]
    exact h1
  have hsum : ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖ ≤ 4 := by
    calc ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖
        ≤ ∑ k : Fin K, ‖g (-(scaleT j * (η + lam k)))‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)),
            ‖g (-(scaleT j * (η + lam k)))‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hzero k hk, norm_zero]
      _ ≤ ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)),
            (2:ℝ) := by
          refine Finset.sum_le_sum (fun k _ => hg_bd _)
      _ = 2 * ((Finset.univ.filter
            (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * 2 := by
          have hcast : ((Finset.univ.filter
              (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card : ℝ) ≤ 2 := by
            exact_mod_cast hS
          linarith
      _ = 4 := by norm_num
  have hZ : (2:ℂ) * (Real.pi:ℂ) * (∑ k : Fin K, g (-(scaleT j * (η + lam k))))
      = ((2 * Real.pi : ℝ) : ℂ) * (∑ k : Fin K, g (-(scaleT j * (η + lam k)))) := by
    push_cast; ring
  calc ‖2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖
      = 2 * Real.pi * ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖ := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 * Real.pi * 4 := by
        have h2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hsum h2
    _ = 8 * Real.pi := by ring



lemma scaleT_mono {j j' : ℕ} (h : j ≤ j') : scaleT j ≤ scaleT j' := by
  rw [scaleT, scaleT]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

lemma scaleT_two_mul_le {j j' : ℕ} (h : j < j') : 2 * scaleT j ≤ scaleT j' := by
  have h2 : (2:ℝ) * 2 ^ (j+1) = 2 ^ (j+2) := by rw [pow_succ]; ring
  rw [scaleT, scaleT, h2]
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  omega

lemma scaleT_inv_le_half (j : ℕ) : (scaleT j)⁻¹ ≤ 1/2 := by
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) (scaleT_ge_two j)

/-- At most one dyadic scale `j` contributes to the annulus multiplier at a given frequency. -/
lemma at_most_one_scale {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (η : ℝ) {j j' : ℕ} (hj : ∃ k : Fin K, g (-(scaleT j * (η + lam k))) ≠ 0)
    (hj' : ∃ k : Fin K, g (-(scaleT j' * (η + lam k))) ≠ 0) : j = j' := by
  obtain ⟨k, hk⟩ := hj
  obtain ⟨k', hk'⟩ := hj'
  have hb : ∀ (m : ℕ) (l : Fin K), g (-(scaleT m * (η + lam l))) ≠ 0 →
      1/2 < scaleT m * |η + lam l| ∧ scaleT m * |η + lam l| ≤ 1 := by
    intro m l hl
    have hcon : 1/2 < |(-(scaleT m * (η + lam l)))| ∧
        |(-(scaleT m * (η + lam l)))| ≤ 1 := by
      by_contra hc
      exact hl (hg_supp _ hc)
    rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos m)] at hcon
    exact hcon
  obtain ⟨hk1, hk2⟩ := hb j k hk
  obtain ⟨hk1', hk2'⟩ := hb j' k' hk'
  have htj : (0:ℝ) < scaleT j := scaleT_pos j
  have htj' : (0:ℝ) < scaleT j' := scaleT_pos j'
  -- one-sided bounds
  have hu2 : |η + lam k| ≤ (scaleT j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj, mul_comm]; exact hk2
  have hu2' : |η + lam k'| ≤ (scaleT j')⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj', mul_comm]; exact hk2'
  have hu1 : (scaleT j)⁻¹ / 2 < |η + lam k| := by
    have h := mul_lt_mul_of_pos_left hk1 (inv_pos.mpr htj)
    have h' : (scaleT j)⁻¹ * (scaleT j * |η + lam k|) = |η + lam k| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj.ne', one_mul]
    rw [h'] at h
    calc (scaleT j)⁻¹ / 2 = (scaleT j)⁻¹ * (1/2) := by ring
      _ < |η + lam k| := h
  have hu1' : (scaleT j')⁻¹ / 2 < |η + lam k'| := by
    have h := mul_lt_mul_of_pos_left hk1' (inv_pos.mpr htj')
    have h' : (scaleT j')⁻¹ * (scaleT j' * |η + lam k'|) = |η + lam k'| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj'.ne', one_mul]
    rw [h'] at h
    calc (scaleT j')⁻¹ / 2 = (scaleT j')⁻¹ * (1/2) := by ring
      _ < |η + lam k'| := h
  rcases eq_or_ne k k' with hkk | hkk
  · subst hkk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h2 : (scaleT j')⁻¹ ≤ (scaleT j)⁻¹ / 2 := by
        have hge := scaleT_two_mul_le hlt
        have h4 : (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) := h4
          _ = (scaleT j)⁻¹/2 := by rw [inv_eq_one_div]; ring
      linarith [hu1, hu2']
    · have h2 : (scaleT j)⁻¹ ≤ (scaleT j')⁻¹ / 2 := by
        have hge := scaleT_two_mul_le hlt
        have h4 : (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') := h4
          _ = (scaleT j')⁻¹/2 := by rw [inv_eq_one_div]; ring
      linarith [hu1', hu2]
  · -- different indices
    have h1 : (1:ℝ) ≤ |lam k - lam k'| := hsep k k' hkk
    have h2 : |lam k - lam k'| ≤ |η + lam k| + |η + lam k'| := by
      calc |lam k - lam k'| = |(η + lam k) - (η + lam k')| := by congr 1; ring
        _ ≤ |η + lam k| + |η + lam k'| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (η + lam k) 0 (η + lam k')
    have h3 : |η + lam k| + |η + lam k'| ≤ (scaleT j)⁻¹ + (scaleT j')⁻¹ := by linarith
    have h4 : (scaleT j)⁻¹ + (scaleT j')⁻¹ ≤ 1 := by
      linarith [scaleT_inv_le_half j, scaleT_inv_le_half j']
    have hsum1 : (scaleT j)⁻¹ + (scaleT j')⁻¹ = 1 := by linarith
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exfalso
      have hge := scaleT_two_mul_le hlt
      have h5 : (scaleT j')⁻¹ ≤ (scaleT j)⁻¹ / 2 := by
        have h6 : (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) := h6
          _ = (scaleT j)⁻¹/2 := by rw [inv_eq_one_div]; ring
      have h7 : (scaleT j)⁻¹ ≤ 1/2 := scaleT_inv_le_half j
      linarith
    · exact heq
    · exfalso
      have hge := scaleT_two_mul_le hgt
      have h5 : (scaleT j)⁻¹ ≤ (scaleT j')⁻¹ / 2 := by
        have h6 : (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') := h6
          _ = (scaleT j')⁻¹/2 := by rw [inv_eq_one_div]; ring
      have h7 : (scaleT j')⁻¹ ≤ 1/2 := scaleT_inv_le_half j'
      linarith



lemma annulusMul_ne_zero_imp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} {j : ℕ} {η : ℝ}
    (h : annulusMul g lam j η ≠ 0) : ∃ k : Fin K, g (-(scaleT j * (η + lam k))) ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by rw [annulusMul, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const_zero,
    mul_zero])

lemma annulusMul_memLp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) :
    MemLp (annulusMul g lam j) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (8 * Real.pi) ?_
  · exact (Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
      hg.comp (by fun_prop : Measurable (fun η : ℝ => -(scaleT j * (η + lam k)))))) _).aestronglyMeasurable
  · filter_upwards with η
    exact annulusMul_bound hsep hg_supp hg_bd η j

lemma annulusMul_tsum_le {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (η : ℝ) :
    (∑' j : ℕ, ‖annulusMul g lam j η‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
  by_cases h : ∃ j : ℕ, annulusMul g lam j η ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hzero : ∀ j : ℕ, j ≠ j0 → annulusMul g lam j η = 0 := by
      intro j hj
      by_contra hc
      exact hj (at_most_one_scale (j := j) (j' := j0) hsep hg_supp η
        (annulusMul_ne_zero_imp hc) (annulusMul_ne_zero_imp hj0))
    rw [tsum_eq_single j0 (fun j hj => by rw [hzero j hj]; simp)]
    have hb : ‖annulusMul g lam j0 η‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
      have h1 : ‖annulusMul g lam j0 η‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) := by
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (annulusMul_bound hsep hg_supp hg_bd η j0)
      calc ‖annulusMul g lam j0 η‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (8 * Real.pi)) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((8 * Real.pi)^2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    exact hb
  · push Not at h
    simp [h]

/-- The annulus multiplier operator. -/
def annulusOp (K : ℕ) (lam : Fin K → ℝ) {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  Commons.Analysis.Fourier.BoundaryLayer.multiplier (annulusMul g lam j)
    (annulusMul_memLp hg hsep hg_supp hg_bd j) f

/-- **The annulus part of the smooth window: the maximal band-sum is `L²`-bounded, uniformly
in the annulus profile `g`** (with `C = (8π)²`). -/
theorem annulus_multiplier_bandSum_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ (g : ℝ → ℂ) (hg : Measurable g)
        (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
        (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2),
      ∀ (f : Lp ℂ 2 (volume : Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ‖(annulusOp K lam hg hsep hg_supp hg_bd j f
            : ℝ → ℂ) x‖ₑ) ^ (2:ℝ) ≤
          ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := by
  refine ⟨(8 * Real.pi)^2, by positivity, ?_⟩
  intro K lam hsep g hg hg_supp hg_bd f
  have hmemLp := fun j => annulusMul_memLp (K := K) hg hsep hg_supp hg_bd j
  have hmain := l2_multiplier_sum_square_function (ι := ℕ) (fun j => annulusMul g lam j)
    hmemLp f (8 * Real.pi) (fun η => annulusMul_tsum_le hg hsep hg_supp hg_bd η)
  have hfun : ∀ j : ℕ, annulusOp K lam hg hsep hg_supp hg_bd j f
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (annulusMul g lam j) (hmemLp j) f :=
    fun j => rfl
  calc ∫⁻ x, (⨆ j : ℕ, ‖(annulusOp K lam hg hsep hg_supp hg_bd j f
          : ℝ → ℂ) x‖ₑ) ^ (2:ℝ)
      = ∫⁻ x, (⨆ j : ℕ, ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (annulusMul g lam j) (hmemLp j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) := by
        apply lintegral_congr; intro x
        rw [iSup_rpow_two]
        simp only [hfun]
    _ ≤ ∫⁻ x, ∑' j : ℕ, ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (annulusMul g lam j) (hmemLp j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro x
        exact iSup_le (fun j => ENNReal.le_tsum (f := fun j => ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (annulusMul g lam j) (hmemLp j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) j)
    _ ≤ ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := hmain


open SepWin

/-! ### The remainder term in the identification's frequency variable

`xiMul g lam j ξ = 2π ∑_k g(-t_j(2πξ+λ_k))` (with `t_j = 2^{j+1}`) is the annulus symbol in
the frequency variable `ξ` of `bandSum_eq_single_multiplier`.  For a profile `g` supported in the
annulus `{1/2 < |·| ≤ 1}` and bounded by `2`, at most one dyadic scale contributes at each `ξ`, so
`∑'_j ‖xiMul g lam j ξ‖² ≤ (8π)²` and the maximal multiplier is `L²`-bounded by `(8π)²`
**uniformly in `g`, `K` and the frequencies** — the elementary disjointness estimate that handles
the `φ - A` part of the window split, with no entropy input. -/

def xiMul {K : ℕ} (g : ℝ → ℂ) (lam : Fin K → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun ξ => 2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))

lemma xiMul_bound {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (ξ : ℝ) (j : ℕ) :
    ‖xiMul g lam j ξ‖ ≤ 8 * Real.pi := by
  rw [xiMul]
  have hS : (Finset.univ.filter
      (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card ≤ 2 := by
    have hr : (0:ℝ) < (scaleT j)⁻¹ := inv_pos.mpr (scaleT_pos j)
    have hr2 : 2 * (scaleT j)⁻¹ ≤ 1 := by
      have h2 := scaleT_ge_two j
      have h3 : (1:ℝ) / scaleT j ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
      rw [inv_eq_one_div]
      linarith
    exact card_le_two_separated hsep hr hr2
  have hzero : ∀ k : Fin K, ¬ (|lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹) →
      g (-(scaleT j * (2 * Real.pi * ξ + lam k))) = 0 := by
    intro k hk
    apply hg_supp
    intro hcon
    apply hk
    have h1 : scaleT j * |2 * Real.pi * ξ + lam k| ≤ 1 := by
      have := hcon.2
      rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos j)] at this
      exact this
    rw [show lam k - (-(2 * Real.pi * ξ)) = 2 * Real.pi * ξ + lam k by ring,
      inv_eq_one_div, le_div_iff₀ (scaleT_pos j)]
    linarith [h1]
  have hsum : ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ ≤ 4 := by
    calc ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖
        ≤ ∑ k : Fin K, ‖g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)),
            ‖g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hzero k hk, norm_zero]
      _ ≤ ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)),
            (2:ℝ) := by
          refine Finset.sum_le_sum (fun k _ => hg_bd _)
      _ = 2 * ((Finset.univ.filter
            (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * 2 := by
          have hcast : ((Finset.univ.filter
              (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card : ℝ) ≤ 2 := by
            exact_mod_cast hS
          linarith
      _ = 4 := by norm_num
  have hZ : (2:ℂ) * (Real.pi:ℂ) * (∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))))
      = ((2 * Real.pi : ℝ) : ℂ) * (∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))) := by
    push_cast; ring
  calc ‖2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖
      = 2 * Real.pi * ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    _ ≤ 2 * Real.pi * 4 := by
        have h2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hsum h2
    _ = 8 * Real.pi := by ring

lemma xiMul_memLp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) :
    MemLp (xiMul g lam j) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (8 * Real.pi) ?_
  · exact (Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
      hg.comp (by fun_prop : Measurable (fun ξ : ℝ => -(scaleT j * (2 * Real.pi * ξ + lam k)))))) _).aestronglyMeasurable
  · filter_upwards with ξ
    exact xiMul_bound hsep hg_supp hg_bd ξ j

/-- At most one dyadic scale contributes at a given frequency `ξ`. -/
lemma xi_at_most_one_scale {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (ξ : ℝ) {j j' : ℕ}
    (hj : ∃ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))) ≠ 0)
    (hj' : ∃ k : Fin K, g (-(scaleT j' * (2 * Real.pi * ξ + lam k))) ≠ 0) : j = j' := by
  have hsm : StrictMono (fun n : ℕ => (2:ℝ)^n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n)
  obtain ⟨k, hk⟩ := hj
  obtain ⟨k', hk'⟩ := hj'
  have hb : ∀ (m : ℕ) (l : Fin K), g (-(scaleT m * (2 * Real.pi * ξ + lam l))) ≠ 0 →
      1/2 < scaleT m * |2 * Real.pi * ξ + lam l| ∧ scaleT m * |2 * Real.pi * ξ + lam l| ≤ 1 := by
    intro m l hl
    have hcon : 1/2 < |(-(scaleT m * (2 * Real.pi * ξ + lam l)))| ∧
        |(-(scaleT m * (2 * Real.pi * ξ + lam l)))| ≤ 1 := by
      by_contra hc
      exact hl (hg_supp _ hc)
    rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos m)] at hcon
    exact hcon
  obtain ⟨hk1, hk2⟩ := hb j k hk
  obtain ⟨hk1', hk2'⟩ := hb j' k' hk'
  have htj : (0:ℝ) < scaleT j := scaleT_pos j
  have htj' : (0:ℝ) < scaleT j' := scaleT_pos j'
  have hu2 : |2 * Real.pi * ξ + lam k| ≤ (scaleT j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj]; nlinarith [hk2]
  have hu2' : |2 * Real.pi * ξ + lam k'| ≤ (scaleT j')⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj']; nlinarith [hk2']
  have hu1 : (scaleT j)⁻¹ / 2 < |2 * Real.pi * ξ + lam k| := by
    have h := mul_lt_mul_of_pos_left hk1 (inv_pos.mpr htj)
    have h' : (scaleT j)⁻¹ * (scaleT j * |2 * Real.pi * ξ + lam k|) = |2 * Real.pi * ξ + lam k| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj.ne', one_mul]
    rw [h'] at h
    calc (scaleT j)⁻¹ / 2 = (scaleT j)⁻¹ * (1/2) := by ring
      _ < |2 * Real.pi * ξ + lam k| := h
  have hu1' : (scaleT j')⁻¹ / 2 < |2 * Real.pi * ξ + lam k'| := by
    have h := mul_lt_mul_of_pos_left hk1' (inv_pos.mpr htj')
    have h' : (scaleT j')⁻¹ * (scaleT j' * |2 * Real.pi * ξ + lam k'|) = |2 * Real.pi * ξ + lam k'| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj'.ne', one_mul]
    rw [h'] at h
    calc (scaleT j')⁻¹ / 2 = (scaleT j')⁻¹ * (1/2) := by ring
      _ < |2 * Real.pi * ξ + lam k'| := h
  rcases eq_or_ne k k' with hkk | hkk
  · -- same frequency: `t_j/2 < t_{j'} < 2 t_j`, and both are powers of `2` `≥ 2`
    subst hkk
    have hlt : (scaleT j)⁻¹ / 2 < (scaleT j')⁻¹ := by linarith [hu1, hu2']
    have hlt2 : (scaleT j')⁻¹ / 2 < (scaleT j)⁻¹ := by linarith [hu1', hu2]
    have hA : scaleT j' < 2 * scaleT j := by
      have h : (2 * scaleT j)⁻¹ < (scaleT j')⁻¹ := by
        rw [show (2 * scaleT j)⁻¹ = (scaleT j)⁻¹ / 2 by field_simp]
        exact hlt
      exact (inv_lt_inv₀ (a := 2 * scaleT j) (b := scaleT j') (by positivity) (scaleT_pos j')).mp h
    have hB : scaleT j < 2 * scaleT j' := by
      have h : (2 * scaleT j')⁻¹ < (scaleT j)⁻¹ := by
        rw [show (2 * scaleT j')⁻¹ = (scaleT j')⁻¹ / 2 by field_simp]
        exact hlt2
      exact (inv_lt_inv₀ (a := 2 * scaleT j') (b := scaleT j) (by positivity) (scaleT_pos j)).mp h
    have hA' : (2:ℝ)^(j'+1) < (2:ℝ)^(j+1+1) := by
      have h2 : (2:ℝ)^(j+1+1) = 2 * scaleT j := by rw [scaleT, pow_succ]; ring
      rw [h2]; exact hA
    have hB' : (2:ℝ)^(j+1) < (2:ℝ)^(j'+1+1) := by
      have h2 : (2:ℝ)^(j'+1+1) = 2 * scaleT j' := by rw [scaleT, pow_succ]; ring
      rw [h2]; exact hB
    have h1 : j' + 1 < j + 1 + 1 := hsm.lt_iff_lt.mp hA'
    have h2 : j + 1 < j' + 1 + 1 := hsm.lt_iff_lt.mp hB'
    omega
  · -- different frequencies: `t_j = t_{j'} = 2`
    have h1 : (1:ℝ) ≤ |lam k - lam k'| := hsep k k' hkk
    have h2 : |lam k - lam k'| ≤ |2 * Real.pi * ξ + lam k| + |2 * Real.pi * ξ + lam k'| := by
      have h := abs_sub_le (2 * Real.pi * ξ + lam k) 0 (2 * Real.pi * ξ + lam k')
      simp only [sub_zero, zero_sub, abs_neg] at h
      have heq : (2 * Real.pi * ξ + lam k) - (2 * Real.pi * ξ + lam k') = lam k - lam k' := by ring
      rw [heq] at h
      exact h
    have h4 : (scaleT j)⁻¹ ≤ 1/2 := scaleT_inv_le_half j
    have h5 : (scaleT j')⁻¹ ≤ 1/2 := scaleT_inv_le_half j'
    have h3 : (scaleT j)⁻¹ + (scaleT j')⁻¹ ≤ 1 := by linarith
    have h6 : (1:ℝ) ≤ (scaleT j)⁻¹ + (scaleT j')⁻¹ := by linarith [h1, h2, hu2, hu2']
    have h7 : (scaleT j)⁻¹ = 1/2 := by linarith
    have h8 : (scaleT j')⁻¹ = 1/2 := by linarith
    have hj2 : scaleT j = 2 := by
      rw [← inv_inv (scaleT j), h7]; norm_num
    have hj'2 : scaleT j' = 2 := by
      rw [← inv_inv (scaleT j'), h8]; norm_num
    have : j + 1 = j' + 1 := hsm.injective (by rw [← scaleT, ← scaleT]; rw [hj2, hj'2])
    omega

lemma xiMul_tsum_le {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ} (hg : Measurable g)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (ξ : ℝ) :
    (∑' j : ℕ, ‖xiMul g lam j ξ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
  by_cases h : ∃ j : ℕ, xiMul g lam j ξ ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hne : ∃ k : Fin K, g (-(scaleT j0 * (2 * Real.pi * ξ + lam k))) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (by rw [xiMul, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const_zero, mul_zero])
    have hzero : ∀ j : ℕ, j ≠ j0 → xiMul g lam j ξ = 0 := by
      intro j hj
      by_contra hc
      have hk : ∃ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))) ≠ 0 := by
        by_contra hcc
        push Not at hcc
        exact hc (by rw [xiMul, Finset.sum_congr rfl (fun k _ => hcc k), Finset.sum_const_zero, mul_zero])
      exact hj (xi_at_most_one_scale hsep hg_supp ξ hk hne)
    rw [tsum_eq_single j0 (fun j hj => by rw [hzero j hj]; simp)]
    have hb : ‖xiMul g lam j0 ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
      have h1 : ‖xiMul g lam j0 ξ‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) := by
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (xiMul_bound hsep hg_supp hg_bd ξ j0)
      calc ‖xiMul g lam j0 ξ‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (8 * Real.pi)) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((8 * Real.pi)^2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    exact hb
  · push Not at h
    simp [h]

/-- The annulus (remainder) part of the smooth-window maximal estimate, in the identification's
frequency variable: the maximal band-sum is `L²`-bounded with the absolute constant `(8π)²`,
uniformly in the annulus profile `g`, the number `K` and the frequencies. -/
theorem xi_multiplier_maximal_l2 {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {g : ℝ → ℂ} (hg : Measurable g)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) :
    ∀ (f : Lp ℂ 2 (volume : Measure ℝ)),
      ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ) ^ (2:ℝ) ≤
        ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := by
  intro f
  have hmain := l2_multiplier_sum_square_function (ι := ℕ) (fun j => xiMul g lam j)
    (fun j => xiMul_memLp hg hsep hg_supp hg_bd j) f (8 * Real.pi)
    (fun ξ => xiMul_tsum_le hsep hg hg_supp hg_bd ξ)
  calc ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ) ^ (2:ℝ)
      = ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) := by
        apply lintegral_congr; intro x
        rw [iSup_rpow_two]
    _ ≤ ∫⁻ x, ∑' j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro x
        exact iSup_le (fun j => ENNReal.le_tsum (f := fun j => ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) j)
    _ ≤ ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := hmain


/-- Integrability of `y ↦ f y · k (x - y)` for `f, k ∈ L²` (Cauchy–Schwarz). -/
lemma integrable_mul_comp_sub {f k : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hk : MemLp k 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun y : ℝ => f y * k (x - y)) (volume : Measure ℝ) := by
  have hk' : MemLp (fun y : ℝ => k (x - y)) 2 (volume : Measure ℝ) :=
    hk.comp_measurePreserving (BoundaryLayer.mpSub x)
  exact hf.integrable_mul hk'

/-- Kernel splitting: `innerSmooth φ = innerSmooth A + innerBound A - innerBound φ`. -/
lemma innerSmooth_split {K : ℕ} (lam : Fin K → ℝ) (A φ : ℝ → ℝ)
    (hφ : Continuous φ) (hA : Continuous A) (j : ℕ) (z : ℝ) :
    innerSmooth φ K lam j z
      = innerSmooth A K lam j z + innerBound A K lam j z - innerBound φ K lam j z := by
  have hk : ∀ k : Fin K, (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        (φ ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        (A ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      + (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - A ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      - (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - φ ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))) := by
    intro k
    rw [← intervalIntegral.integral_add, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr (fun θ _ => ?_)
      push_cast; ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  simp only [innerSmooth, innerBound]
  trans (∑ k : Fin K, ((∫ θ in (lam k - hJ j)..(lam k + hJ j),
        (A ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      + (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - A ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      - (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - φ ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))))
  · exact Finset.sum_congr rfl (fun k _ => hk k)
  · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Operator splitting: `smoothOp φ f = smoothOp A f + boundOp A f - boundOp φ f`. -/
lemma smoothOp_split {K : ℕ} (lam : Fin K → ℝ) (A φ : ℝ → ℝ)
    (hφ : Continuous φ) (hA : Continuous A) (hφbd : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hAbd : ∀ x, 0 ≤ A x ∧ A x ≤ 1)
    (hφm : Measurable φ) (hAm : Measurable A)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) (j : ℕ) (x : ℝ) :
    smoothOp φ K lam f j x
      = smoothOp A K lam f j x + boundOp A K lam f j x - boundOp φ K lam f j x := by
  have h1 := integrable_mul_comp_sub hf (memLp_innerSmooth A hAm hAbd K lam j) x
  have h2 := integrable_mul_comp_sub hf (memLp_innerBound A hAm hAbd K lam j) x
  have h3 := integrable_mul_comp_sub hf (memLp_innerBound φ hφm hφbd K lam j) x
  have hfun : (fun y : ℝ => f y * innerSmooth φ K lam j (x - y))
      = (fun a : ℝ => ((fun y : ℝ => f y * innerSmooth A K lam j (x - y))
          + (fun y : ℝ => f y * innerBound A K lam j (x - y))) a
            - (fun y : ℝ => f y * innerBound φ K lam j (x - y)) a) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [innerSmooth_split lam A φ hφ hA j (x - y)]
    ring
  simp only [smoothOp, boundOp]
  rw [hfun, integral_sub (h1.add h2) h3]
  simp only [Pi.add_apply]
  rw [integral_add h1 h2]

/-- `smoothOp` is the target's double integral. -/
lemma smoothOp_eq_target (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    smoothOp φ K lam f j x = ∫ y : ℝ, f y * (∑ k : Fin K,
      ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
        (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := rfl

/-- A.e. measurability of the maximal function of `smoothOp`. -/
lemma aemeasurable_iSup_smoothOp (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)) volume := by
  refine AEMeasurable.pow_const ?_ 2
  refine AEMeasurable.iSup (fun j => ?_)
  exact (Commons.Analysis.Fourier.aestronglyMeasurable_conv hf (measurable_innerSmooth φ hφm hbd K lam j)).aemeasurable.enorm

/-- A.e. measurability of the maximal function of `boundOp`. -/
lemma aemeasurable_iSup_boundOp (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ)) volume := by
  refine AEMeasurable.pow_const ?_ 2
  refine AEMeasurable.iSup (fun j => ?_)
  exact (Commons.Analysis.Fourier.aestronglyMeasurable_conv hf (measurable_innerBound φ hφm hbd K lam j)).aemeasurable.enorm

/-- **The target reduces to the fixed-window (`A = bump`) estimate plus the boundary layer.**
Split `φ = A + (1-A) - (1-φ)` at the level of the convolution kernels; use the fixed-window
estimate for the `A`-part and the published `boundary_layer_l2` for the two boundary layers. -/
theorem smooth_window_of_fixed_bump
    (hcrux : ∃ CA : ℝ, 0 < CA ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
        (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * (∑ k : Fin K,
            ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
              (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ))
          ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
  obtain ⟨CA, hCApos, hcrux⟩ := hcrux
  obtain ⟨Cb, hCbpos, hbl⟩ := boundary_layer_l2
  refine ⟨Real.sqrt (16 * CA^2 + 20 * Cb^2 / ((Real.log 2)^2)^2) + 1, by positivity, ?_⟩
  intro K lam hsep φ hφφ h1 h0 hbd f hf
  have hφc : Continuous φ := (hφφ 1).continuous
  have hφm : Measurable φ := hφc.measurable
  have hbc : Continuous bump := (bump_contDiff 1).continuous
  have hbm : Measurable bump := hbc.measurable
  -- pointwise bound
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)
      ≤ 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
        + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))
        + 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ)) := by
    intro x
    set A := ⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ with hA
    set B := ⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ with hB
    set Cc := ⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ with hC
    have hle : (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ≤ A + B + Cc := by
      refine iSup_le (fun j => ?_)
      rw [smoothOp_split lam bump φ hφc hbc hbd bump_bounds hφm hbm hf j x]
      calc ‖smoothOp bump K lam f j x + boundOp bump K lam f j x - boundOp φ K lam f j x‖ₑ
          ≤ ‖smoothOp bump K lam f j x + boundOp bump K lam f j x‖ₑ
            + ‖boundOp φ K lam f j x‖ₑ := by
              simpa using Commons.Analysis.Fourier.enorm_sub_le
                (smoothOp bump K lam f j x + boundOp bump K lam f j x)
                (boundOp φ K lam f j x)
        _ ≤ (‖smoothOp bump K lam f j x‖ₑ + ‖boundOp bump K lam f j x‖ₑ)
            + ‖boundOp φ K lam f j x‖ₑ := add_le_add_left (Commons.Analysis.Fourier.enorm_add_le _ _) _
        _ ≤ A + B + Cc :=
            add_le_add (add_le_add
              (le_iSup (fun j => ‖smoothOp bump K lam f j x‖ₑ) j)
              (le_iSup (fun j => ‖boundOp bump K lam f j x‖ₑ) j))
              (le_iSup (fun j => ‖boundOp φ K lam f j x‖ₑ) j)
    calc (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)
        ≤ (A + B + Cc) ^ (2:ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
      _ ≤ 16 * A ^ (2:ℝ) + 16 * B ^ (2:ℝ) + 4 * Cc ^ (2:ℝ) := by
          refine le_trans (add_rpow_two_le (A + B) Cc) ?_
          refine le_trans (mul_le_mul_right (add_le_add_left
            (add_rpow_two_le A B) (Cc ^ (2:ℝ))) 4) ?_
          exact le_of_eq (by ring)
  -- integrate
  have hInt : (∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ))
      ≤ (16 * (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (16 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (4 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := by
    have ha := aemeasurable_iSup_smoothOp bump K lam hbm bump_bounds hf
    have hb := aemeasurable_iSup_boundOp bump K lam hbm bump_bounds hf
    have hc := aemeasurable_iSup_boundOp φ K lam hφm hbd hf
    calc ∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x, (16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
            + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))
            + 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := lintegral_mono hpt
      _ = (16 * (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
            + (16 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
            + (4 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := by
          rw [show (fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                + 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ)))
              = (fun a : ℝ =>
                  ((fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                      + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))) a)
                  + ((fun x : ℝ => 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) a))
              from by funext a; rfl]
          rw [lintegral_add_left' (show AEMeasurable (fun x : ℝ =>
                16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))) volume from
              (ha.const_mul 16).add (hb.const_mul 16))]
          rw [show (fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                  + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
              = (fun a : ℝ =>
                  ((fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))) a)
                  + ((fun x : ℝ => 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))) a))
              from by funext a; rfl]
          rw [lintegral_add_left' (show AEMeasurable (fun x : ℝ =>
                16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))) volume from ha.const_mul 16)]
          rw [lintegral_const_mul'' 16 ha, lintegral_const_mul'' 16 hb, lintegral_const_mul'' 4 hc]
  have hcruxK := hcrux K lam hsep f hf
  -- the boundary layer bounds
  have hbnd : ∀ (ψ : ℝ → ℝ), (∀ x : ℝ, |x| ≤ 1 / 2 → ψ x = 1) →
      (∀ x : ℝ, 1 ≤ |x| → ψ x = 0) → (∀ x : ℝ, 0 ≤ ψ x ∧ ψ x ≤ 1) → Measurable ψ →
      (∫⁻ x, (⨆ j : ℕ, ‖boundOp ψ K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
    intro ψ hψ1 hψ0 hψbd hψm
    have hψ := hbl K lam hsep ψ hψ1 hψ0 hψbd f hf
    calc ∫⁻ x, (⨆ j : ℕ, ‖boundOp ψ K lam f j x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x, ∑' j : ℕ, ‖boundOp ψ K lam f j x‖ₑ ^ (2:ℝ) := by
            apply lintegral_mono; intro x
            show (⨆ j : ℕ, ‖boundOp ψ K lam f j x‖ₑ) ^ (2:ℝ)
              ≤ ∑' j : ℕ, ‖boundOp ψ K lam f j x‖ₑ ^ (2:ℝ)
            rw [iSup_rpow_two]
            exact iSup_le (fun j => ENNReal.le_tsum (f := fun j => ‖boundOp ψ K lam f j x‖ₑ ^ (2:ℝ)) j)
      _ = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖boundOp ψ K lam f j x‖ ^ (2:ℝ) := by
            apply lintegral_congr; intro x
            exact tsum_congr (fun j => by rw [BoundaryLayer.enorm_eq_ofReal_norm])
      _ ≤ ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
            refine le_trans hψ (mul_le_mul_right ?_ (ENNReal.ofReal (Cb^2)))
            rw [show (∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ)) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) from
              lintegral_congr (fun x => by rw [BoundaryLayer.enorm_eq_ofReal_norm])]
  have hLhs_eq : (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * (∑ k : Fin K,
            ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
              (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ))
      = (∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)) := rfl
  rw [hLhs_eq]
  have hLpos : (0:ℝ) < Real.log ((K:ℝ) + 2) :=
    Real.log_pos (by linarith [(show (0:ℝ) ≤ (K:ℝ) by positivity)])
  have h2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLge : Real.log 2 ≤ Real.log ((K:ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(show (0:ℝ) ≤ (K:ℝ) by positivity)])
  have hsq : ((Real.log 2)^2)^2 ≤ ((Real.log ((K:ℝ)+2))^2)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact pow_le_pow_left₀ h2pos.le hLge 2
  set C0 := Real.sqrt (16 * CA^2 + 20 * Cb^2 / ((Real.log 2)^2)^2) with hC0
  have hC0nonneg : 0 ≤ C0 := Real.sqrt_nonneg _
  have hC0sq : (16 * CA^2 + 20 * Cb^2 / ((Real.log 2)^2)^2) ≤ C0^2 := by
    rw [hC0, Real.sq_sqrt (by positivity)]
  have hCsq : (16 * CA^2 + 20 * Cb^2 / ((Real.log ((K:ℝ)+2))^2)^2) ≤ (C0 + 1)^2 := by
    have h1' : 20 * Cb^2 / ((Real.log ((K:ℝ)+2))^2)^2 ≤ 20 * Cb^2 / ((Real.log 2)^2)^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    nlinarith [hC0sq, h1']
  calc (∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ))
      ≤ (16 * (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (16 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (4 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := hInt
    _ ≤ (16 * (ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ))))
        + (16 * (ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ))))
        + (4 * (ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)))) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_right hcruxK 16
          · exact mul_le_mul_right (hbnd bump bump_one bump_zero bump_bounds hbm) 16
          · exact mul_le_mul_right (hbnd φ h1 h0 hbd hφm) 4
    _ = ((16:ℝ≥0∞) * ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2)
          + 16 * ENNReal.ofReal (Cb^2) + 4 * ENNReal.ofReal (Cb^2))
        * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← add_mul, ← add_mul]
    _ ≤ ENNReal.ofReal (((C0 + 1) * (Real.log ((K:ℝ)+2))^2)^2)
          * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
          refine mul_le_mul_left ?_ (∫⁻ x, ‖f x‖ₑ^(2:ℝ))
          rw [show ((16:ℝ≥0∞) * ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2)
                + 16 * ENNReal.ofReal (Cb^2) + 4 * ENNReal.ofReal (Cb^2))
              = ENNReal.ofReal (16 * (CA * (Real.log ((K:ℝ)+2))^2)^2 + 16 * Cb^2 + 4 * Cb^2) from ?_]
          · apply ENNReal.ofReal_le_ofReal
            have hgoal : 16 * (CA * (Real.log ((K:ℝ)+2))^2)^2 + 16 * Cb^2 + 4 * Cb^2
                ≤ ((C0 + 1) * (Real.log ((K:ℝ)+2))^2)^2 := by
              have hL4 : (0:ℝ) < ((Real.log ((K:ℝ)+2))^2)^2 := by positivity
              have hkey := mul_le_mul_of_nonneg_right hCsq hL4.le
              have eI : (16 * CA^2 + 20 * Cb^2 / ((Real.log ((K:ℝ)+2))^2)^2)
                    * ((Real.log ((K:ℝ)+2))^2)^2 = 16 * CA^2 * ((Real.log ((K:ℝ)+2))^2)^2 + 20 * Cb^2 := by
                field_simp
              rw [eI] at hkey
              nlinarith [hkey]
            exact hgoal
          · rw [show (16:ℝ≥0∞) = ENNReal.ofReal 16 from by norm_num,
                show (4:ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num]
            rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
                ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
                ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]

end

end FWPortBump


/-- **The target from the fixed-bump smooth-window maximal estimate.**  `hcrux` is the windowed
maximal estimate (Bourgain Lemma 4.13) for the *single* fixed bump
`x ↦ smoothTransition (2-2x) * smoothTransition (2+2x)`; it is the only remaining analytic
ingredient of the whole reduction (see `Submission/Work/Analysis/Fourier/
SINGLE_MULTIPLIER_REDUCTION.md`). -/
theorem quadratic_kernel_model_maximal_l2_of_fixed_bump
    (hcrux : ∃ CA : ℝ, 0 < CA ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        (∫⁻ x, (⨆ j : ℕ, ‖Commons.Analysis.Fourier.SepWin.smoothOp
            Commons.Analysis.Fourier.SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
          ≤ ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2)
            * (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ))) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
  quadratic_kernel_model_maximal_l2_of_smoothWindow
    (Commons.Analysis.Fourier.SepWin.smoothWindowMaximal_of_inline (by
      obtain ⟨C, hCpos, hC⟩ := FWPortBump.smooth_window_of_fixed_bump hcrux
      refine ⟨C, hCpos, fun K lam hlam φ hφ h1 h0 hbd f hf => ?_⟩
      have := hC K lam hlam φ hφ h1 h0 hbd f hf
      simpa only [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm] using this))

end Commons.Analysis.ExponentialSums

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/UniformChain.lean ====

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ESU

open MeasureTheory Finset
open Commons.Analysis.Fourier
open scoped BigOperators ENNReal

noncomputable section

/-- A single `K`-free constant from the near-orthogonality of separated exponentials,
used to make the chain bound below uniform in the frequency family. -/
noncomputable def cSep : ℝ := Classical.choose separated_exponentials_near_orthogonal

lemma cSep_pos : 0 < cSep :=
  (Classical.choose_spec separated_exponentials_near_orthogonal).1

lemma cSep_spec (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) (a : Fin K → ℂ) :
    ∫ u in (0:ℝ)..1, ‖∑ k : Fin K, a k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2
      ≤ cSep * ∑ k : Fin K, ‖a k‖ ^ 2 :=
  (Classical.choose_spec separated_exponentials_near_orthogonal).2 K lam hsep a

/-- The (uniform in the frequency family) constant of the chain bound. -/
noncomputable def cChain : ℝ := 200 * (cSep + cSep + 1)

lemma cChain_pos : 0 < cChain := by
  unfold cChain
  have := cSep_pos
  linarith

private lemma uc_iSup_finset_nonneg {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : 0 ≤ (⨆ a ∈ B, u a) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · subst hB
    simp
  · obtain ⟨a₀, ha₀⟩ := hB
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ B), u a)) := by
      refine ⟨∑ a ∈ B, u a, ?_⟩
      rintro _ ⟨a, rfl⟩
      change (⨆ (_ : a ∈ B), u a) ≤ ∑ a ∈ B, u a
      by_cases ha : a ∈ B
      · rw [show (⨆ (_ : a ∈ B), u a) = u a from ciSup_pos (f := fun _ => u a) ha]
        exact Finset.single_le_sum (fun i _ => h i) ha
      · rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u a) ha, Real.sSup_empty]
        exact Finset.sum_nonneg (fun _ _ => h _)
    have h1 : u a₀ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := by
      calc u a₀ = ⨆ (_ : a₀ ∈ B), u a₀ := (ciSup_pos (f := fun _ => u a₀) ha₀).symm
        _ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := le_ciSup hbdd a₀
    exact le_trans (h a₀) h1

/-- For a finite family of nonnegative reals the square of the supremum is at most the sum of
the squares (a consequence of `(sup u)² ≤ ∑ u²`, i.e. of the fact that a maximum of
nonnegative numbers is dominated in square by the sum of all squares). -/
private lemma uc_iSup_finset_sq_le_sum {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : (⨆ a ∈ B, u a) ^ 2 ≤ ∑ a ∈ B, (u a) ^ 2 := by
  have hnn : 0 ≤ (⨆ a ∈ B, u a) := uc_iSup_finset_nonneg B u h
  have h1 : (⨆ a ∈ B, u a) ≤ Real.sqrt (∑ a ∈ B, (u a) ^ 2) := by
    rcases isEmpty_or_nonempty α with hα | hα
    · have hB : B = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun hne => hne.elim fun a _ => isEmptyElim a)
      rw [show (⨆ a : α, ⨆ (_ : a ∈ B), u a) = (⨆ a : α, (0 : ℝ)) from by
            apply iSup_congr; intro a
            rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
              ciSup_neg (f := fun _ => u a) (by rw [hB]; simp)]
            exact Real.sSup_empty]
      rw [Real.iSup_of_isEmpty]
      simp [hB]
    · apply ciSup_le
      intro b
      by_cases hb : b ∈ B
      · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
        rw [← Real.sqrt_sq (h b)]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) hb)
      · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u b) hb, Real.sSup_empty]
        exact Real.sqrt_nonneg _
  calc (⨆ a ∈ B, u a) ^ 2 ≤ (Real.sqrt (∑ a ∈ B, (u a) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hnn h1 2
    _ = ∑ a ∈ B, (u a) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **The maximal exponential sum over a finite class of coefficient vectors, mean-square bound.**
Let `lam : Fin K → ℝ` be `1`-separated, and let `B` be a finite set of coefficient vectors with
`∑ k, ‖b k‖ ^ 2 ≤ R ^ 2` for every `b ∈ B`.  Then the mean square over `y ∈ [0,1]` of the maximal
exponential sum `sup_{b ∈ B} ‖∑ k, b k * exp(I * lam k * y)‖` is at most `C * R ^ 2 * #B`.

This is the per-level estimate (4.24)–(4.25) in Bourgain's proof of his Lemma 4.13: the
near-orthogonality of `1`-separated exponentials
(`Commons.Analysis.Fourier.separated_exponentials_near_orthogonal`) controls the mean square of
each individual exponential sum, and the maximum over the *finite* set `B` is controlled by the
sum over `B` through the pointwise inequality `(sup_{b ∈ B} u b) ^ 2 ≤ ∑_{b ∈ B} (u b) ^ 2`.  The
integral is a Lebesgue integral over `[0,1]` in `ℝ≥0∞`, so no measurability of the pointwise
supremum is needed. -/
theorem max_finset_exp_sum_l2_const (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∀ (B : Finset (Fin K → ℂ)) (R : ℝ), 0 ≤ R →
      (∀ b ∈ B, ∑ k : Fin K, ‖b k‖ ^ 2 ≤ R ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (⨆ b ∈ B, ‖∑ k : Fin K,
            b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ 2
        ≤ ENNReal.ofReal (cSep * R ^ 2 * (B.card : ℝ)) := by
  classical
  have hcSeppos : 0 < cSep := cSep_pos
  have hcSepC : ∀ (K' : ℕ) (lam' : Fin K' → ℝ),
      (∀ k l : Fin K', k ≠ l → 1 ≤ |lam' k - lam' l|) → ∀ (a : Fin K' → ℂ),
      ∫ u in (0:ℝ)..1, ‖∑ k : Fin K', a k * Complex.exp (Complex.I * (lam' k : ℂ) * (u : ℂ))‖ ^ 2
        ≤ cSep * ∑ k : Fin K', ‖a k‖ ^ 2 := fun K' lam' hsep' a => cSep_spec K' lam' hsep' a
  intro B R hR hB
  set U : (Fin K → ℂ) → ℝ → ℝ :=
    fun b y => ‖∑ k : Fin K, b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ with hU
  have hUcont : ∀ b, Continuous (U b) := by
    intro b
    have : Continuous fun y : ℝ => ∑ k : Fin K, b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) :=
      continuous_finsetSum _ (fun k _ => by fun_prop)
    simpa only [hU] using this.norm
  have hUnn : ∀ b y, 0 ≤ U b y := fun b y => norm_nonneg _
  have hpt : ∀ y : ℝ,
      ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2 ≤ ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
    intro y
    have hsup := uc_iSup_finset_sq_le_sum B (fun b => U b y) (fun b => hUnn b y)
    have hnn : 0 ≤ (⨆ b ∈ B, U b y) := uc_iSup_finset_nonneg B (fun b => U b y) (fun b => hUnn b y)
    calc ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
        = ENNReal.ofReal ((⨆ b ∈ B, U b y) ^ 2) := (ENNReal.ofReal_pow hnn 2).symm
      _ ≤ ENNReal.ofReal (∑ b ∈ B, (U b y) ^ 2) := ENNReal.ofReal_le_ofReal hsup
      _ = ∑ b ∈ B, ENNReal.ofReal ((U b y) ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _)
      _ = ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
            apply Finset.sum_congr rfl; intro b _
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
  have hmeas : ∀ b ∈ B, Measurable (fun y : ℝ => ENNReal.ofReal (U b y) ^ 2) := by
    intro b _
    exact ((hUcont b).measurable.ennreal_ofReal.pow_const 2)
  have hint : ∀ b ∈ B, Integrable (fun y : ℝ => (U b y) ^ 2)
      (volume.restrict (Set.Ioc 0 1)) := by
    intro b _
    have hcont : Continuous (fun y : ℝ => (U b y) ^ 2) := (hUcont b).pow 2
    exact (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  calc ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0 : ℝ) 1, ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := lintegral_mono hpt
    _ = ∑ b ∈ B, ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2 := by
          rw [lintegral_finsetSum]
          intro b hb; exact hmeas b hb
    _ = ∑ b ∈ B, ENNReal.ofReal (∫ y in (0 : ℝ)..1, (U b y) ^ 2) := by
          apply Finset.sum_congr rfl; intro b hb
          have h1 : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2
              = ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((U b y) ^ 2) := by
            apply lintegral_congr; intro y
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
          rw [h1]
          have h2 := ofReal_integral_eq_lintegral_ofReal (hint b hb)
            (ae_of_all _ (fun y => sq_nonneg (U b y)))
          rw [← h2]
          congr 1
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ ≤ ∑ b ∈ B, ENNReal.ofReal (cSep * R ^ 2) := by
          apply Finset.sum_le_sum; intro b hb
          apply ENNReal.ofReal_le_ofReal
          have hc := hcSepC K lam hsep b
          calc ∫ y in (0 : ℝ)..1, (U b y) ^ 2
              ≤ cSep * ∑ k : Fin K, ‖b k‖ ^ 2 := by
                rw [hU]; exact hc
            _ ≤ cSep * R ^ 2 :=
                mul_le_mul_of_nonneg_left (hB b hb) (le_of_lt hcSeppos)
    _ = ENNReal.ofReal (cSep * R ^ 2 * (B.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast (B.card),
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((B.card : ℕ) : ℝ) by positivity)]
          ring_nf


private lemma uc_norm_cexp_lin (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (lam : ℂ) * (y : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.mul_re]; simp
  rw [h, Real.exp_zero]

/-- Cauchy–Schwarz: `∑ ‖d k‖ ≤ √K · √(∑ ‖d k‖²)`. -/
private lemma uc_sum_norm_le_sqrt_card_mul_sqrt_sum_sq {K : ℕ} (d : Fin K → ℂ) :
    ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
  have h1 : (∑ k : Fin K, ‖d k‖ * 1) ^ 2
      ≤ (∑ k : Fin K, ‖d k‖ ^ 2) * (∑ _ : Fin K, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖d k‖) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have h3 : 0 ≤ ∑ k : Fin K, ‖d k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt ((∑ k : Fin K, ‖d k‖ ^ 2) * (K : ℝ)) := by
        rw [← Real.sqrt_sq h3]; exact Real.sqrt_le_sqrt h1
    _ = Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), mul_comm]

/-- A member of a finite family of nonnegative reals is at most the finite supremum. -/
private lemma uc_le_iSup_finset {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a)
    {a : α} (ha : a ∈ B) : u a ≤ ⨆ b ∈ B, u b := by
  have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ B), u b)) := by
    refine ⟨∑ b ∈ B, u b, ?_⟩
    rintro _ ⟨b, rfl⟩
    change (⨆ (_ : b ∈ B), u b) ≤ ∑ b ∈ B, u b
    by_cases hb : b ∈ B
    · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
      exact Finset.single_le_sum (fun i _ => h i) hb
    · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
        Real.sSup_empty]
      exact Finset.sum_nonneg (fun _ _ => h _)
  calc u a = ⨆ (_ : a ∈ B), u a := (ciSup_pos (f := fun _ => u a) ha).symm
    _ ≤ ⨆ b, ⨆ (_ : b ∈ B), u b := le_ciSup hbdd a

/-- For a nonempty finset, the bi-supremum of a nonnegative family equals its `sup'`. -/
private lemma uc_iSup_finset_eq_sup {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (⨆ i ∈ F, f i) = F.sup' hF f := by
  have hFne : F.Nonempty := hF
  obtain ⟨i₀, hi₀⟩ := hFne
  haveI : Nonempty ι := ⟨i₀⟩
  have hsupnn : 0 ≤ F.sup' hF f := le_trans (hf i₀) (Finset.le_sup' f hi₀)
  refine le_antisymm ?_ (Finset.sup'_le hF f (fun i hi => uc_le_iSup_finset F f hf hi))
  refine ciSup_le (fun i => ?_)
  by_cases hi : i ∈ F
  · rw [ciSup_pos (f := fun _ => f i) hi]
    exact Finset.le_sup' f hi
  · rw [ciSup_neg (f := fun _ => f i) hi, Real.sSup_empty]
    exact hsupnn

/-- **The entropy chain bound for a finite family.**  Let `lam : Fin K → ℝ` be `1`-separated and
`a : Fin (N+1) → (Fin K → ℂ)` a family of coefficient vectors that is approximately constant along
each net `σ t` at the dyadic accuracy `2·2^{-t}`.  Then the `L²` norm over `[0,1]` of the maximal
exponential sum `sup_i ‖∑ k, a i k · e^{I λ_k y}‖` is bounded by the square of
`√(∑ ‖a (σ 0 0) k‖²) + ∑_{t ≤ S} 2^{-t} √(min (K, M t + 1))`.

This is the entropy/chaining estimate (4.24)–(4.26) in Bourgain's proof of Lemma 4.13: the
telescoping along a dyadic chain of nets decomposes the family into at most `M t` classes at level
`t`, each class is handled by the mean-square bound for a maximal exponential sum
(`Commons.Analysis.Fourier.max_finset_exponential_sum_l2`), the `√K` term is Cauchy–Schwarz, and
the classes are then recombined with the abstract `L²` class bound
(`Commons.Analysis.Fourier.lintegral_sq_sum_le_of_class_bounds`). -/
theorem chain_exp_sum_le_entropy_const (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ), 1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      (N+1) ≤ M S →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
          (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((200 * (cSep + cSep + 1) * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    intro N S a σ M hS hconst hNM hcard hnet2
    have hz : (fun y : ℝ => ENNReal.ofReal
        (⨆ i : Fin (N+1), ‖∑ k : Fin 0,
          a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) := by
      funext y
      simp
    rw [hz, lintegral_zero]
    exact bot_le
  have hcSeppos : 0 < cSep := cSep_pos
  have hcSepB : ∀ (B : Finset (Fin K → ℂ)) (R : ℝ), 0 ≤ R →
      (∀ b ∈ B, ∑ k : Fin K, ‖b k‖ ^ 2 ≤ R ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (⨆ b ∈ B, ‖∑ k : Fin K,
            b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ 2
        ≤ ENNReal.ofReal (cSep * R ^ 2 * (B.card : ℝ)) :=
    max_finset_exp_sum_l2_const K lam hsep
  have hcSepA : ∀ (K' : ℕ) (lam' : Fin K' → ℝ),
      (∀ k l : Fin K', k ≠ l → 1 ≤ |lam' k - lam' l|) → ∀ (a : Fin K' → ℂ),
      ∫ u in (0:ℝ)..1, ‖∑ k : Fin K', a k * Complex.exp (Complex.I * (lam' k : ℂ) * (u : ℂ))‖ ^ 2
        ≤ cSep * ∑ k : Fin K', ‖a k‖ ^ 2 := fun K' lam' hsep' a => cSep_spec K' lam' hsep' a
  intro N S a σ M hS hconst hNM hcard hnet2
  -- Convert the `ℓ²` hypothesis into a uniform norm bound.
  have hnet : ∀ t, t ≤ S → ∀ i : Fin (N+1), ‖a i - a (σ t i)‖ ≤ 2 * (1/2:ℝ)^t := by
    intro t ht i
    have h2 := hnet2 t ht i
    have hsqrt : Real.sqrt (∑ k : Fin K, ‖a i k - a (σ t i) k‖^2) ≤ 2 * (1/2:ℝ)^t := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (1/2:ℝ)^t)]
      exact Real.sqrt_le_sqrt h2
    refine le_trans ?_ hsqrt
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro m
    calc ‖(a i - a (σ t i)) m‖ = ‖a i m - a (σ t i) m‖ := by rw [Pi.sub_apply]
      _ = Real.sqrt (‖a i m - a (σ t i) m‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ x : Fin K, ‖a i x - a (σ t i) x‖^2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum
            (fun x (_ : x ∈ Finset.univ) => sq_nonneg (‖a i x - a (σ t i) x‖))
            (Finset.mem_univ m))
  -- The dyadic chain and the finite difference classes.
  let q : ℕ → Fin (N+1) → Fin (N+1) := dyadicChain (N+1) S σ
  let B : ℕ → Finset (Fin K → ℂ) := dyadicDiff (N+1) S a σ
  have hqmem : ∀ k, 1 ≤ k → k ≤ S → ∀ i, q k i ∈ Finset.univ.image (σ (S - k)) := by
    intro k hk _ i
    exact dyadicChain_mem_image (N+1) S σ hk i
  have hqdiff : ∀ k, k < S → ∀ i, a (q k i) - a (q (k+1) i) ∈ B k := by
    intro k _ i
    have hqsucc : q (k+1) i = σ (S - k - 1) (q k i) := dyadicChain_succ_apply (N+1) S σ k i
    rw [hqsucc]
    simp only [B]
    refine Finset.mem_image.mpr ⟨q k i, ?_, rfl⟩
    by_cases hk0 : k = 0
    · subst hk0; simp [dyadicDiff_def]
    · rw [if_neg hk0]
      exact dyadicChain_mem_image (N+1) S σ (by omega) i
  have hqcard : ∀ k, 1 ≤ k → k < S →
      (B k).card ≤ (Finset.univ.image (σ (S - k))).card := by
    intro k hk1 _
    have hk0 : k ≠ 0 := by omega
    simp only [B]
    rw [dyadicDiff_def, if_neg hk0]
    exact Finset.card_image_le
  have hqcard0 : (B 0).card ≤ N+1 := by
    simp only [B]
    rw [dyadicDiff_def, if_pos rfl]
    calc (Finset.univ.image (fun v => a v - a (σ (S - 0 - 1) v))).card
        ≤ (Finset.univ : Finset (Fin (N+1))).card := Finset.card_image_le
      _ = N+1 := by simp
  have hqnorm : ∀ k, k < S → ∀ b ∈ B k, ‖b‖ ≤ 2 * (1/2:ℝ)^(S-k-1) := by
    intro k _ b hb
    simp only [B] at hb
    rw [dyadicDiff_def] at hb
    rw [Finset.mem_image] at hb
    obtain ⟨v, _, hv⟩ := hb
    rw [← hv]
    exact hnet (S - k - 1) (by omega) v
  have hqdecomp : ∀ i, a i = a (q S i) + ∑ k ∈ Finset.range S, (a (q k i) - a (q (k+1) i)) := by
    intro i
    have hsum := Finset.sum_range_sub' (fun k => a (q k i)) S
    rw [hsum]
    rw [show q 0 i = i from dyadicChain_zero_apply (N+1) S σ i]
    exact (add_sub_cancel (a (q S i)) (a i)).symm
  have hqS : ∀ i : Fin (N+1), q S i = σ 0 0 := by
    intro i
    have hmem := hqmem S hS le_rfl i
    rw [Nat.sub_self] at hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    rw [← hj, hconst j]
  let p : Fin K → ℂ := a (σ 0 0)
  let D : ℝ := Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2)
  let Φ : ℝ → (Fin K → ℂ) → ℂ :=
    fun y v => ∑ k : Fin K, v k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))
  have hΦadd : ∀ y (u v : Fin K → ℂ), Φ y (u + v) = Φ y u + Φ y v := by
    intro y u v
    simp only [Φ, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hΦsum : ∀ y (s : Finset ℕ) (u : ℕ → Fin K → ℂ),
      Φ y (∑ k ∈ s, u k) = ∑ k ∈ s, Φ y (u k) := by
    intro y s u
    simp only [Φ, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hΦcont : ∀ b : Fin K → ℂ, Continuous (fun y : ℝ => Φ y b) := by
    intro b
    simp only [Φ]
    exact continuous_finsetSum _ (fun k _ => by fun_prop)
  have hB_ne : ∀ k, k < S → (B k).Nonempty := fun k hk => ⟨_, hqdiff k hk 0⟩
  let cls : ℕ → Finset (Fin K → ℂ) := fun j => if j < S then B j else {p}
  have hcls_ne : ∀ j, (cls j).Nonempty := by
    intro j
    by_cases hj : j < S
    · have h1 : cls j = B j := by simp [cls, hj]
      rw [h1]
      exact hB_ne j hj
    · have h1 : cls j = {p} := by simp [cls, hj]
      rw [h1]
      exact ⟨p, Finset.mem_singleton_self p⟩
  have hclsS : cls S = {p} := by simp [cls]
  have hclsj : ∀ j, j < S → cls j = B j := fun j hj => by simp [cls, hj]
  let Acls : ℕ → ℝ → ℝ := fun j y => (cls j).sup' (hcls_ne j) (fun b => ‖Φ y b‖)
  have hAcls_cont : ∀ j, Continuous (Acls j) := by
    intro j
    exact Continuous.finset_sup'_apply (hcls_ne j) (fun b _ => (hΦcont b).norm)
  have hAcls_nn : ∀ j y, 0 ≤ Acls j y := by
    intro j y
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖Φ y b‖) (hcls_ne j).choose_spec)
  have hAeqS : ∀ y, Acls S y = (⨆ b ∈ cls S, ‖Φ y b‖) := by
    intro y
    simp only [Acls]
    exact (uc_iSup_finset_eq_sup (cls S) (hcls_ne S) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqk : ∀ k, k < S → ∀ y, Acls k y = (⨆ b ∈ B k, ‖Φ y b‖) := by
    intro k hk y
    simp only [Acls, hclsj k hk]
    exact (uc_iSup_finset_eq_sup (B k) (hB_ne k hk) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqS' : ∀ y, Acls S y = ‖Φ y p‖ := by
    intro y
    simp only [Acls, hclsS]
    rw [Finset.sup'_singleton]
  have hper : ∀ y i, ‖Φ y (a i)‖ ≤ Acls S y + ∑ k ∈ Finset.range S, Acls k y := by
    intro y i
    have hsumk : ∑ k ∈ Finset.range S, Acls k y
        = ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) :=
      Finset.sum_congr rfl (fun k hk => hAeqk k (Finset.mem_range.mp hk) y)
    rw [hAeqS y, hsumk]
    have hsplit2 : Φ y (a i) = Φ y (a (q S i))
        + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i)) := by
      conv_lhs => rw [hqdecomp i]
      rw [hΦadd, hΦsum]
    calc ‖Φ y (a i)‖
        = ‖Φ y (a (q S i)) + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := by
          rw [hsplit2]
      _ ≤ ‖Φ y (a (q S i))‖
            + ‖∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := norm_add_le _ _
      _ ≤ (⨆ b ∈ cls S, ‖Φ y b‖) + ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) := by
          apply add_le_add
          · refine uc_le_iSup_finset (cls S) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _) ?_
            rw [hqS i, hclsS]
            exact Finset.mem_singleton_self p
          · refine (norm_sum_le _ _).trans ?_
            apply Finset.sum_le_sum; intro k hk
            exact uc_le_iSup_finset (B k) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)
              (hqdiff k (Finset.mem_range.mp hk) i)
  have hdom : ∀ y, (⨆ i : Fin (N+1), ‖Φ y (a i)‖) ≤ ∑ j ∈ Finset.range (S+1), Acls j y := by
    intro y
    rw [Finset.sum_range_succ]
    exact ciSup_le (fun i => (hper y i).trans (le_of_eq (add_comm _ _)))
  have hsup0 : ∀ y, (0:ℝ) ≤ ⨆ i : Fin (N+1), ‖Φ y (a i)‖ := by
    intro y
    have hbdd : BddAbove (Set.range (fun i : Fin (N+1) => ‖Φ y (a i)‖)) := by
      refine ⟨Acls S y + ∑ k ∈ Finset.range S, Acls k y, ?_⟩
      rintro z ⟨i, rfl⟩
      exact hper y i
    exact le_trans (norm_nonneg _) (le_ciSup hbdd 0)
  -- Per-class mean-square bounds.
  have hcls_bound : ∀ k, k < S →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal ((2 * (1/2:ℝ)^(S-k-1)) ^ 2
            * min (K:ℝ) (cSep * ((B k).card : ℝ) + 1)) := by
    intro k hk
    set R : ℝ := 2 * (1/2:ℝ)^(S-k-1) with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hmemB : ∀ b ∈ B k, ∑ j : Fin K, ‖b j‖ ^ 2 ≤ R ^ 2 := by
      intro b hb
      simp only [B] at hb
      rw [dyadicDiff_def] at hb
      rw [Finset.mem_image] at hb
      obtain ⟨v, _, hv⟩ := hb
      rw [← hv, hRdef]
      exact hnet2 (S-k-1) (by omega) v
    have hpt : ∀ y, Acls k y ≤ Real.sqrt (K:ℝ) * R := by
      intro y
      have hsup : Acls k y = (B k).sup' (hB_ne k hk) (fun b => ‖Φ y b‖) := by
        simp only [Acls, hclsj k hk]
      rw [hsup]
      refine Finset.sup'_le (hB_ne k hk) (fun b => ‖Φ y b‖) (fun b hb => ?_)
      have hb2 := hmemB b hb
      have hnorm : ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := by
        have h1 : ‖Φ y b‖ ≤ ∑ j : Fin K, ‖b j‖ := by
          calc ‖Φ y b‖
              = ‖∑ j : Fin K, b j * Complex.exp (Complex.I * (lam j:ℂ) * (y:ℂ))‖ := rfl
            _ ≤ ∑ j : Fin K, ‖b j * Complex.exp (Complex.I * (lam j:ℂ) * (y:ℂ))‖ :=
                norm_sum_le _ _
            _ = ∑ j : Fin K, ‖b j‖ := by
                apply Finset.sum_congr rfl; intro j _
                rw [norm_mul, uc_norm_cexp_lin, mul_one]
        exact h1.trans (uc_sum_norm_le_sqrt_card_mul_sqrt_sum_sq b)
      calc ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := hnorm
        _ ≤ Real.sqrt (K:ℝ) * Real.sqrt (R^2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _)
        _ = Real.sqrt (K:ℝ) * R := by rw [Real.sqrt_sq hRpos.le]
    have hpt_int : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (K * R^2) := by
      have hstep : ∀ y : ℝ, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 := by
        intro y
        rw [← ENNReal.ofReal_pow (hAcls_nn k y) 2,
          ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hAcls_nn k y) (hpt y) 2)
      calc ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 :=
            lintegral_mono hstep
        _ = ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 * volume (Set.Ioc (0:ℝ) 1) := by
            rw [setLIntegral_const]
        _ = ENNReal.ofReal (K * R^2) := by
            rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
            rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
            congr 1
            rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (K:ℝ))]
    have hlev : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (cSep * R^2 * ((B k).card : ℝ)) := by
      have hAeq : Acls k = fun y => (⨆ b ∈ B k, ‖Φ y b‖) := funext (fun y => hAeqk k hk y)
      rw [hAeq]
      exact hcSepB (B k) R hRpos.le hmemB
    refine le_trans (le_min hpt_int hlev) ?_
    rw [← ENNReal.ofReal_min]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (K:ℝ) (cSep * ((B k).card : ℝ) + 1) with hle | hle
    · rw [min_eq_left hle]
      calc min (K * R^2) (cSep * R^2 * ((B k).card : ℝ)) ≤ K * R^2 := min_le_left _ _
        _ = R^2 * K := by ring
    · rw [min_eq_right hle]
      have h2 : cSep * R^2 * ((B k).card : ℝ) ≤ R^2 * (cSep * ((B k).card : ℝ) + 1) := by
        nlinarith [hRpos, sq_nonneg R, (Nat.cast_nonneg ((B k).card) : (0:ℝ) ≤ ((B k).card : ℝ)),
          mul_pos hcSeppos hRpos]
      calc min (K * R^2) (cSep * R^2 * ((B k).card : ℝ)) ≤ cSep * R^2 * ((B k).card : ℝ) :=
            min_le_right _ _
        _ ≤ R^2 * (cSep * ((B k).card : ℝ) + 1) := h2
  -- Top class bound.
  have htop_bound : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls S y) ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt cSep * D) ^ 2) := by
    have hAeq : Acls S = fun y => ‖Φ y p‖ := funext hAeqS'
    rw [hAeq]
    have hcont : Continuous (fun y : ℝ => (‖Φ y p‖) ^ 2) := (hΦcont p).norm.pow 2
    have hint : Integrable (fun y : ℝ => (‖Φ y p‖) ^ 2)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hrepr : (fun y : ℝ => ENNReal.ofReal (‖Φ y p‖) ^ 2)
        = fun y : ℝ => ENNReal.ofReal ((‖Φ y p‖) ^ 2) := by
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [hrepr]
    have h2 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun y : ℝ => (‖Φ y p‖) ^ 2) hint (ae_of_all _ (fun y => sq_nonneg _))
    rw [← h2]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply ENNReal.ofReal_le_ofReal
    have hc1 := hcSepA K lam hsep p
    have hD2 : D ^ 2 = ∑ k : Fin K, ‖p k‖ ^ 2 := by
      rw [show D = Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2) from rfl,
        Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    calc ∫ u in (0:ℝ)..1, (‖Φ u p‖) ^ 2
        ≤ cSep * ∑ k : Fin K, ‖p k‖ ^ 2 := hc1
      _ = (Real.sqrt cSep * D) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hcSeppos.le, hD2]
  -- The weights.
  let X : ℕ → ℝ := fun t => Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))
  let Tsum : ℝ := ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t
  let w : ℕ → ℝ := fun j => if j < S
      then (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1))
      else Real.sqrt cSep * D
  let uu : ℕ → ℝ := fun j => w j + (1/2:ℝ)^(j+1)
  have hXnn : ∀ t, 0 ≤ X t := fun t => Real.sqrt_nonneg _
  have hwnn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j < S
    · have h1 : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1)) := by
        simp only [w]; rw [if_pos hj]
      rw [h1]
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · have h1 : w j = Real.sqrt cSep * D := by simp only [w]; rw [if_neg hj]
      rw [h1]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have huun : ∀ j, 0 ≤ uu j := fun j =>
    add_nonneg (hwnn j) (by positivity)
  have huu_pos : ∀ j ∈ Finset.range (S+1), 0 < uu j := by
    intro j _
    have h1 : 0 < (1/2:ℝ)^(j+1) := by positivity
    have h2 : 0 ≤ w j := hwnn j
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_left h2)
  have hminKnn : ∀ j, (0:ℝ) ≤ min (K:ℝ) (cSep * ((B j).card : ℝ) + 1) := fun j =>
    le_min (by positivity) (add_nonneg (mul_nonneg hcSeppos.le (Nat.cast_nonneg _)) zero_le_one)
  have huu_bound : ∀ j ∈ Finset.range (S+1),
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls j y) ^ 2
        ≤ ENNReal.ofReal ((uu j) ^ 2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
    · have h1 : uu j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1)) + (1/2:ℝ)^(j+1) := by
        have hwj : w j = (2 * (1/2:ℝ)^(S-j-1))
            * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1)) := by
          dsimp only [w]
          rw [if_pos hlt]
        show w j + (1/2:ℝ)^(j+1) = _
        rw [hwj]
      rw [h1]
      refine (hcls_bound j hlt).trans (ENNReal.ofReal_le_ofReal ?_)
      have hb : 0 ≤ (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hsq : ((2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1))) ^ 2
          = (2 * (1/2:ℝ)^(S-j-1)) ^ 2 * min (K:ℝ) (cSep * ((B j).card : ℝ) + 1) := by
        rw [mul_pow, Real.sq_sqrt (hminKnn j)]
      rw [← hsq]
      exact pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 2
    · rw [heq]
      have h1 : uu S = Real.sqrt cSep * D + (1/2:ℝ)^(S+1) := by
        have hwS : w S = Real.sqrt cSep * D := by
          dsimp only [w]
          rw [if_neg (lt_irrefl S)]
        show w S + (1/2:ℝ)^(S+1) = _
        rw [hwS]
      rw [h1]
      refine htop_bound.trans ?_
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (le_add_of_nonneg_right (by positivity)) 2
  obtain hmain := lintegral_sq_sum_le_of_class_bounds (Finset.range (S+1)) Acls uu huu_pos
    (fun j _ y => hAcls_nn j y)
    (fun j _ => ((hAcls_cont j).measurable.ennreal_ofReal.pow_const 2).aemeasurable)
    huu_bound
  have hstep1 : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
      (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (∑ j ∈ Finset.range (S+1), Acls j y) ^ 2 := by
    apply lintegral_mono
    intro y
    simp only
    have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (S+1), Acls j y :=
      Finset.sum_nonneg (fun j _ => hAcls_nn j y)
    rw [← ENNReal.ofReal_pow hsum0 2, ← ENNReal.ofReal_pow (hsup0 y) 2]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hsup0 y) (hdom y) 2)
  refine le_trans hstep1 (le_trans hmain ?_)
  apply ENNReal.ofReal_le_ofReal
  -- Numerical bound on `(∑ uu)²`.
  have hDnn : 0 ≤ D := Real.sqrt_nonneg _
  have hTsum_ge_one : 1 ≤ Tsum := by
    have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
    have hX0 : 1 ≤ X 0 := by
      have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
      have hM1 : 1 ≤ M 0 := by
        have h1 : 1 ≤ (Finset.univ.image (σ 0)).card :=
          Finset.card_pos.mpr (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)
        exact le_trans h1 (hcard 0 (by omega))
      have hM01 : (1:ℝ) ≤ (M 0 : ℝ) := by exact_mod_cast hM1
      have hmin1 : (1:ℝ) ≤ min (K:ℝ) ((M 0 : ℝ) + 1) := le_min hK1 (by linarith)
      show (1:ℝ) ≤ Real.sqrt (min (K:ℝ) ((M 0 : ℝ) + 1))
      rw [Real.le_sqrt (by norm_num) (by linarith [hmin1])]
      simpa using hmin1
    calc (1:ℝ) ≤ X 0 := hX0
      _ = (1/2:ℝ)^0 * X 0 := by rw [pow_zero, one_mul]
      _ ≤ Tsum := Finset.single_le_sum (f := fun t => (1/2:ℝ)^t * X t)
          (fun t _ => mul_nonneg (by positivity) (hXnn t)) hmem
  have hgeom2 : ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) ≤ 1 := by
    rw [show (∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1))
        = (1/2:ℝ) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          rw [pow_succ]; ring]
    have hgs : ∑ j ∈ Finset.range S, (1/2:ℝ)^j ≤ 2 := by
      have h1 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1)) = 1 - (1/2:ℝ)^S := by
        have h3 := Finset.sum_range_sub (fun j => (1/2:ℝ)^j) S
        rw [pow_zero] at h3
        have h4 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
            = -∑ j ∈ Finset.range S, ((1/2:ℝ)^(j+1) - (1/2:ℝ)^j) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [h4, h3]; ring
      have h2 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
          = (1/2) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_succ]; ring
      rw [h2] at h1
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) S]
    linarith
  have hBcard_le : ∀ j, j < S → (B j).card ≤ M (S-j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [Nat.sub_zero]
      exact le_trans hqcard0 hNM
    · exact le_trans (hqcard j hjpos hj) (hcard (S-j) (by omega))
  have hwbound : ∑ j ∈ Finset.range S, w j ≤ 4 * Real.sqrt (cSep + 1) * Tsum := by
    have hterm : ∀ j ∈ Finset.range S, w j
        ≤ 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (cSep+1) * X (S-j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hweq : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1)) := by
        dsimp only [w]; rw [if_pos hj]
      rw [hweq]
      have h1 : Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1))
          ≤ Real.sqrt (cSep+1) * X (S-j) := by
        have h4 : ((B j).card : ℝ) ≤ (M (S-j) : ℝ) := by exact_mod_cast hBcard_le j hj
        have hx : cSep * ((B j).card : ℝ) + 1 ≤ (cSep+1) * ((M (S-j) : ℝ) + 1) := by
          have hM' : (0:ℝ) ≤ (M (S-j) : ℝ) := Nat.cast_nonneg _
          have h5 := mul_le_mul_of_nonneg_left h4 hcSeppos.le
          nlinarith [h5, hM', hcSeppos]
        have hmin : min (K:ℝ) (cSep * ((B j).card : ℝ) + 1)
            ≤ (cSep+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1) := by
          rcases le_total ((M (S-j) : ℝ) + 1) (K:ℝ) with hle | hle
          · rw [min_eq_right hle]
            exact le_trans (min_le_right _ _) hx
          · rw [min_eq_left hle]
            calc min (K:ℝ) (cSep * ((B j).card : ℝ) + 1) ≤ (K:ℝ) := min_le_left _ _
              _ ≤ (cSep+1) * K := by nlinarith [mul_nonneg hcSeppos.le (Nat.cast_nonneg K)]
        calc Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1))
            ≤ Real.sqrt ((cSep+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1)) := Real.sqrt_le_sqrt hmin
          _ = Real.sqrt (cSep+1) * X (S-j) := by
              rw [Real.sqrt_mul (show (0:ℝ) ≤ cSep+1 by linarith)]
      calc (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (cSep * ((B j).card : ℝ) + 1))
          ≤ (2 * (1/2:ℝ)^(S-j-1)) * (Real.sqrt (cSep+1) * X (S-j)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (cSep+1) * X (S-j) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcongr : (∑ j ∈ Finset.range S,
          2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (cSep+1) * X (S-j))
        = ∑ j ∈ Finset.range S,
            2 * (1/2:ℝ)^(S-1-j) * Real.sqrt (cSep+1) * X (S-1-j+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have h4 : S - j - 1 = S - 1 - j := tsub_right_comm
      have h5 : S - j = S - 1 - j + 1 := by
        rw [← h4, Nat.sub_add_cancel (by omega : 1 ≤ S - j)]
      rw [h4, h5]
    have hrefl : (∑ j ∈ Finset.range S,
          2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (cSep+1) * X (S-j))
        = ∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (cSep+1) * X (i+1) := by
      rw [hcongr]
      exact Finset.sum_range_reflect
        (fun i => 2 * (1/2:ℝ)^i * Real.sqrt (cSep+1) * X (i+1)) S
    rw [hrefl]
    have himg : (∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (cSep+1) * X (i+1))
        = 4 * Real.sqrt (cSep+1)
          * ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [pow_succ]; ring
    rw [himg]
    have hsubset : (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t := by
      rw [Finset.sum_range_succ']
      have h0 : 0 ≤ (1/2:ℝ)^0 * X 0 := mul_nonneg (by norm_num) (hXnn 0)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hXnn (i+1)))
      linarith [h0, hsum0]
    calc 4 * Real.sqrt (cSep+1) * (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ 4 * Real.sqrt (cSep+1) * Tsum := by
          apply mul_le_mul_of_nonneg_left hsubset (by positivity)
      _ = 4 * Real.sqrt (cSep+1) * Tsum := rfl
  have hsum_uu : ∑ j ∈ Finset.range (S+1), uu j ≤ 100 * (cSep + cSep + 1) * (D + Tsum) := by
    rw [Finset.sum_range_succ]
    have hfirst : ∑ j ∈ Finset.range S, uu j ≤ 4 * Real.sqrt (cSep+1) * Tsum + 1 := by
      have h2 : ∑ j ∈ Finset.range S, uu j
          ≤ ∑ j ∈ Finset.range S, w j + ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) := by
        have h2' : ∑ j ∈ Finset.range S, uu j
            = ∑ j ∈ Finset.range S, (w j + (1/2:ℝ)^(j+1)) := rfl
        rw [h2', Finset.sum_add_distrib]
      linarith [h2, hwbound, hgeom2]
    have hlast : uu S ≤ Real.sqrt cSep * D + 1 := by
      have h1 : uu S = w S + (1/2:ℝ)^(S+1) := rfl
      have hwS : w S = Real.sqrt cSep * D := by
        dsimp only [w]; rw [if_neg (lt_irrefl S)]
      rw [h1, hwS]
      have : (1/2:ℝ)^(S+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hsqrtc01 : Real.sqrt (cSep+1) ≤ cSep + 1 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ cSep+1), Real.sqrt_nonneg (cSep+1),
        sq_nonneg (Real.sqrt (cSep+1) - 1)]
    have hsqrtc1 : Real.sqrt cSep ≤ cSep + 1 := by
      nlinarith [Real.sq_sqrt hcSeppos.le, Real.sqrt_nonneg cSep, sq_nonneg (Real.sqrt cSep - 1)]
    have hDsum : 1 ≤ D + Tsum := le_trans hTsum_ge_one (le_add_of_nonneg_left hDnn)
    have hTnn : 0 ≤ Tsum := Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity) (hXnn t))
    have hTle : Tsum ≤ D + Tsum := le_add_of_nonneg_left hDnn
    have hDle : D ≤ D + Tsum := le_add_of_nonneg_right hTnn
    nlinarith [hfirst, hlast, hsqrtc01, hsqrtc1, hDsum, hDle, hTle, hDnn, hTnn,
      Real.sqrt_nonneg (cSep+1), Real.sqrt_nonneg cSep, mul_nonneg hcSeppos.le hTnn,
      mul_nonneg (Real.sqrt_nonneg (cSep+1)) hTnn]
  have hnn : 0 ≤ ∑ j ∈ Finset.range (S+1), uu j := Finset.sum_nonneg (fun j hj => (huu_pos j hj).le)
  calc (∑ j ∈ Finset.range (S+1), uu j) ^ 2
      ≤ (100 * (cSep + cSep + 1) * (D + Tsum)) ^ 2 := pow_le_pow_left₀ hnn hsum_uu 2
    _ ≤ (200 * (cSep + cSep + 1) * (D + Tsum)) ^ 2 := by
        have hDsum0 : 0 ≤ D + Tsum :=
          le_trans (le_trans zero_le_one hTsum_ge_one) (le_add_of_nonneg_left hDnn)
        have hnn1 : 0 ≤ 100 * (cSep + cSep + 1) * (D + Tsum) :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hDsum0
        have hle2 : 100 * (cSep + cSep + 1) * (D + Tsum) ≤ 200 * (cSep + cSep + 1) * (D + Tsum) := by
          nlinarith [hcSeppos, hcSeppos, hDsum0]
        exact pow_le_pow_left₀ hnn1 hle2 2

end

end ESU

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/Frame.lean ====
set_option autoImplicit false
set_option maxHeartbeats 2000000

open _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators _root_.ENNReal _root_.Interval _root_.FourierTransform

namespace OldSWM
open Commons.Analysis.Fourier


open _root_.MeasureTheory Finset
open scoped BigOperators ENNReal Interval FourierTransform

/-!
# Bourgain's smooth-window maximal estimate (Lemma 4.13)

Status of this file: the target theorem `bourgain_smooth_window_maximal_l2` at the bottom is still
`sorry`; **everything else in the file is proved and sorry-free**.

## What is proved here (Bourgain 1989, §4, the entropy argument)

* `BourgainSmoothWindow.iSup_finset_nonneg`, `iSup_finset_sq_le_sum`, `le_iSup_finset`,
  `iSup_finset_eq_sup'`, `sum_norm_le_sqrt_card_mul_sqrt_sum_sq`, `weighted_cs`,
  `BourgainSmoothWindow.lintegral_sq_sum_le_of_class_bounds` — elementary auxiliary facts about finite suprema,
  Cauchy–Schwarz, and `∫⁻` of sums of squares.
* `BourgainSmoothWindow.exists_dyadic_chain_decomposition` — (4.21)–(4.23): a bounded family
  with dyadic nets `σ s` (radius `2·2^{-s}`) admits a *chain* `q` and finite classes `B k` with
  `#B k ≤ #(range (σ (S-k)))`, `‖b‖ ≤ 2·2^{-(S-k-1)}` on `B k`, and
  `a i = a (q S i) + ∑_{k<S}(a (q k i) - a (q (k+1) i))`.
* `max_finset_exponential_sum_l2` — the per-level estimate of (4.24)–(4.25) (published to the
  commons).
* `sup_exp_sum_le_of_net` — (4.24)–(4.25) at one scale.
* `slices_l2_le` — `∑_j ‖𝓕⁻(ξ ↦ 𝓕f(ξ+λ_j)ψ(ξ))‖² ≤ ‖f‖²` for `supp ψ ⊆ [-r,r]`, `r < 1/2`
  (the frequency-slice step, via Plancherel).
* `sup_exp_sum_le_entropy_sum` — the full reduction of the maximal estimate to Bourgain's
  entropy sum `D√(N+1) + ∑_{t≤S} 2^{-t}√(M t + N + 1)` (his (4.25)).

## Session 8 additions: the entropy chain and its interfaces

* `BourgainChain.chain_exp_sum_le_entropy` — **the per-level/per-class entropy chain for a finite
  family** (Bourgain (4.24)–(4.25) in the form the assembly needs): for a family `a : Fin (N+1) →
  Fin K → ℂ`, nets `σ t` of radii `2·2^{-t}`, a constant coarsest net (`σ 0`), a finest net that
  resolves the family (`N+1 ≤ M S`), and cardinality bounds `#(range (σ t)) ≤ M t`,
  `∫⁻_{y ∈ (0,1)} ofReal (⨆_i ‖Σ_k a i k e^{I λ_k y}‖)² ≤ ofReal ((C (D + Σ_{t≤S} 2^{-t}
  min(K, M t + 1)^{1/2}))²)` with `D = √(Σ_k ‖a (σ 0 0) k‖²)` the base point.
* `BourgainChain.chain_curve_le_entropy` — the same with the base point replaced by any `x₀` in a
  `ℓ²`-ball of radius `2` containing the family (this is the form usable for the curve).
* `winCovers`, `winCovered`, `winEntropy_antitone`, `exists_cover_of_winEntropy` — the interface
  between the `⨅`-defined entropy numbers `winEntropy` (of the deep input) and explicit covering
  `Finset`s needed to build the nets (`winEntropy ≠ ⊤` gives a covering of cardinality
  `≤ winEntropy + 1`).
* `BourgainEntropy.exists_netmap_of_cover` — curve-point nets from arbitrary covers.
* Published in the commons this session: `lintegral_translate_sub_sq_le_of_fourier_support` (E1),
  `maximal_dilation_convolution_l2` (E2), `net_selfmap_of_cover`,
  `Commons.Analysis.Real.sum_range_mul_le_lintegral_of_antitone`,
  `Commons.Analysis.Real.ofReal_sum_dyadic_le_lintegral_entropy`.

## The remaining gap

The target follows from the above together with

* (i) the **u-averaging reduction** (4.16)–(4.19), which replaces the *pointwise-in-`x`, sup over
  scales* by an `L²_y`-average of the *phase*-expanded sum (this is what makes the entropy chain,
  which is only an a.e.-in-`y` estimate, applicable); the iteration scheme that eliminates the
  a priori constant is spelled out in `BOURGAIN_SMOOTH_WINDOW_ROADMAP.md`, session 7 (C4), and
* (ii) the **deep entropy input** — Bourgain's Lemmas 3.30 + 3.33: the `𝕃²`-norm of
  `∫_0^∞ min(√K, M_r(x)^{1/2}) dr`, with `M_r(x)` the covering number of the curve
  `t ↦ ((f_k*φ_t)(x))_k ⊂ ℂ^K`, is `≤ C M (log (K+2))² ‖(∑_k|f_k|²)^{1/2}‖₂`, where `M` bounds
  the window (`‖Ψ‖_∞ ≤ M`).
  **The `M`-dependence is forced by scaling** (session 7): `Ψ ↦ cΨ` multiplies the entropy
  integral by `c` and leaves the `f`-side unchanged, so a window-independent constant would be
  false.  For the target's windows `Ψ = \hatφ` one has `‖\hatφ‖_∞ = ‖φ‖_1 ≤ 2`, uniformly over
  the class of `φ` in the statement.

(ii) rests on Lépingle's martingale variation inequality with the sharp constant `(s-2)^{-1}`
(Bourgain's Lemma 3.3) plus the Poisson-semigroup transfer (3.11)–(3.29); none of this is in
Mathlib.  See `BOURGAIN_SMOOTH_WINDOW_ROADMAP.md` for the precise statements and the full route.
-/

/-- The exponential character `y ↦ e^{i·λ·y}`. -/
noncomputable def expChar (lam y : ℝ) : ℂ := Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))

namespace BourgainSmoothWindow

/-- **Nonnegativity of a finite supremum of nonnegative reals.** -/
theorem iSup_finset_nonneg {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a) :
    0 ≤ (⨆ a ∈ B, u a) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · subst hB
    simp
  · obtain ⟨a₀, ha₀⟩ := hB
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ B), u a)) := by
      refine ⟨∑ a ∈ B, u a, ?_⟩
      rintro _ ⟨a, rfl⟩
      change (⨆ (_ : a ∈ B), u a) ≤ ∑ a ∈ B, u a
      by_cases ha : a ∈ B
      · rw [show (⨆ (_ : a ∈ B), u a) = u a from ciSup_pos (f := fun _ => u a) ha]
        exact Finset.single_le_sum (fun i _ => h i) ha
      · rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u a) ha,
          Real.sSup_empty]
        exact Finset.sum_nonneg (fun _ _ => h _)
    have h1 : u a₀ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := by
      calc u a₀ = ⨆ (_ : a₀ ∈ B), u a₀ := (ciSup_pos (f := fun _ => u a₀) ha₀).symm
        _ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := le_ciSup hbdd a₀
    exact le_trans (h a₀) h1

/-- **Elementary pointwise inequality.**  For a finite family of nonnegative reals, the square of
the supremum is at most the sum of the squares.  (The supremum is expressed with the
`⨆ a ∈ B, ·` notation, which for `ℝ` ranges over all `a` but assigns `0` to `a ∉ B`.) -/
theorem iSup_finset_sq_le_sum {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a) :
    (⨆ a ∈ B, u a) ^ 2 ≤ ∑ a ∈ B, (u a) ^ 2 := by
  have hnn : 0 ≤ (⨆ a ∈ B, u a) := iSup_finset_nonneg B u h
  have h1 : (⨆ a ∈ B, u a) ≤ Real.sqrt (∑ a ∈ B, (u a) ^ 2) := by
    rcases isEmpty_or_nonempty α with hα | hα
    · have hB : B = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun hne => hne.elim fun a _ => isEmptyElim a)
      rw [show (⨆ a : α, ⨆ (_ : a ∈ B), u a) = (⨆ a : α, (0 : ℝ)) from by
            apply iSup_congr; intro a
            rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
              ciSup_neg (f := fun _ => u a) (by rw [hB]; simp)]
            exact Real.sSup_empty]
      rw [Real.iSup_of_isEmpty]
      simp [hB]
    · apply ciSup_le
      intro b
      by_cases hb : b ∈ B
      · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
        rw [← Real.sqrt_sq (h b)]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) hb)
      · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
          Real.sSup_empty]
        exact Real.sqrt_nonneg _
  calc (⨆ a ∈ B, u a) ^ 2 ≤ (Real.sqrt (∑ a ∈ B, (u a) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hnn h1 2
    _ = ∑ a ∈ B, (u a) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **A member of a finite family of nonnegative reals is at most the supremum.** -/
theorem le_iSup_finset {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a)
    {a : α} (ha : a ∈ B) : u a ≤ ⨆ b ∈ B, u b := by
  have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ B), u b)) := by
    refine ⟨∑ b ∈ B, u b, ?_⟩
    rintro _ ⟨b, rfl⟩
    change (⨆ (_ : b ∈ B), u b) ≤ ∑ b ∈ B, u b
    by_cases hb : b ∈ B
    · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
      exact Finset.single_le_sum (fun i _ => h i) hb
    · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
        Real.sSup_empty]
      exact Finset.sum_nonneg (fun _ _ => h _)
  calc u a = ⨆ (_ : a ∈ B), u a := (ciSup_pos (f := fun _ => u a) ha).symm
    _ ≤ ⨆ b, ⨆ (_ : b ∈ B), u b := le_ciSup hbdd a

/-- **Cauchy-Schwarz in the form used for the net estimates:** for `d : Fin K → ℂ`,
`∑ k, ‖d k‖ ≤ √K · √(∑ k, ‖d k‖²)`. -/
theorem sum_norm_le_sqrt_card_mul_sqrt_sum_sq {K : ℕ} (d : Fin K → ℂ) :
    ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
  have h1 : (∑ k : Fin K, ‖d k‖ * 1) ^ 2
      ≤ (∑ k : Fin K, ‖d k‖ ^ 2) * (∑ _ : Fin K, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖d k‖) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have h3 : 0 ≤ ∑ k : Fin K, ‖d k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt ((∑ k : Fin K, ‖d k‖ ^ 2) * (K : ℝ)) := by
        rw [← Real.sqrt_sq h3]; exact Real.sqrt_le_sqrt h1
    _ = Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), mul_comm]

/-- **Dyadic chain decomposition of a bounded family with prescribed nets** (the combinatorial
content of Bourgain's entropy decomposition, (4.21)–(4.23) of *Pointwise ergodic theorems for
arithmetic sets*).

Let `a : Fin N → E` be a finite family in a normed group `E`, and for every scale `s ≤ S` let
`σ s : Fin N → Fin N` be a "net map": `a (σ s i)` is within `2 · 2^{-s}` of `a i`, so that the
range of `σ s` is a `2 · 2^{-s}`-net for the family, of cardinality at most `#(range (σ s))`.

Then there is a *chain* `q : ℕ → Fin N → Fin N` with `q k i ∈ range (σ (S - k))` for `k ≥ 1`,
such that every family value decomposes as
`a i = a (q S i) + ∑_{k < S} (a (q k i) - a (q (k+1) i))`,
where each difference lies in a finite set `B k` with `#(B k) ≤ #(range (σ (S - k)))` (for `k ≥ 1`;
`#(B 0) ≤ N`) and `‖b‖ ≤ 2 · 2^{-(S-k-1)}` for `b ∈ B k`.

The point of the *chain* (each `q (k+1) i` depends only on `q k i`, rather than the two nets being
chosen independently) is that `B k` has at most `#(range (σ (S-k)))` elements rather than the
product of the two cardinalities — this is what makes the resulting entropy sum match Bourgain's
`∫_0^∞ min(K, M_λ)^{1/2} dλ`. -/
theorem BourgainSmoothWindow.exists_dyadic_chain_decomposition
    {E : Type*} [NormedAddCommGroup E] [DecidableEq E]
    (N S : ℕ) (a : Fin N → E) (σ : ℕ → Fin N → Fin N)
    (hnet : ∀ s, s ≤ S → ∀ i : Fin N, ‖a i - a (σ s i)‖ ≤ 2 * (1 / 2 : ℝ) ^ s) :
    ∃ (q : ℕ → Fin N → Fin N) (B : ℕ → Finset E),
      (∀ k, 1 ≤ k → k ≤ S → ∀ i, q k i ∈ Finset.univ.image (σ (S - k))) ∧
      (∀ k, k < S → ∀ i, a (q k i) - a (q (k+1) i) ∈ B k) ∧
      (∀ k, B k = (Finset.univ.image (q k)).image (fun j => a j - a (σ (S - k - 1) j))) ∧
      (∀ k, 1 ≤ k → k < S → (B k).card ≤ (Finset.univ.image (σ (S - k))).card) ∧
      (B 0).card ≤ N ∧
      (B 0).card ≤ (Finset.univ.image (fun j : Fin N => a j - a (σ (S - 1) j))).card ∧
      (∀ k, k < S → ∀ b ∈ B k, ‖b‖ ≤ 2 * (1 / 2 : ℝ) ^ (S - k - 1)) ∧
      (∀ i, a i = a (q S i) + ∑ k ∈ Finset.range S, (a (q k i) - a (q (k+1) i))) := by
  classical
  let chain : ℕ → Fin N → Fin N := fun k i =>
    Nat.rec i (fun t j => if h : t < S then σ (S - t - 1) j else j) k
  have hchain_succ : ∀ k, chain (k+1) =
      (fun j => if h : k < S then σ (S - k - 1) j else j) ∘ chain k := fun k => rfl
  have hchain0 : ∀ i, chain 0 i = i := fun i => rfl
  -- the step identity at scale k
  have hstep : ∀ k, k < S → ∀ i, chain (k+1) i = σ (S - k - 1) (chain k i) := by
    intro k hk i
    have h := congrFun (hchain_succ k) i
    simp only [Function.comp_apply, dif_pos hk] at h
    exact h
  refine ⟨chain, fun k => (Finset.univ.image (chain k)).image
      (fun j => a j - a (σ (S - k - 1) j)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hkS i
    have hk : k - 1 < S := by omega
    have h := hstep (k-1) hk i
    have hidx : S - (k-1) - 1 = S - k := by omega
    rw [hidx, show k - 1 + 1 = k from by omega] at h
    rw [h]
    exact Finset.mem_image.mpr ⟨chain (k-1) i, Finset.mem_univ _, rfl⟩
  · intro k hk i
    refine Finset.mem_image.mpr ⟨chain k i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hstep k hk i]
  · intro k
    rfl
  · intro k hk1 hk
    refine Finset.card_image_le.trans ?_
    apply Finset.card_le_card
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    have hk' : k - 1 < S := by omega
    have h := hstep (k-1) hk' i
    have hidx : S - (k-1) - 1 = S - k := by omega
    rw [hidx, show k - 1 + 1 = k from by omega] at h
    rw [h]
    exact Finset.mem_image.mpr ⟨chain (k-1) i, Finset.mem_univ _, rfl⟩
  · refine Finset.card_image_le.trans (Finset.card_image_le.trans ?_)
    simp
  · dsimp only
    have h0 : (Finset.univ.image (chain 0)).image (fun j => a j - a (σ (S - 0 - 1) j))
        = Finset.univ.image (fun j : Fin N => a j - a (σ (S - 1) j)) := by
      rw [show chain 0 = id from funext hchain0, Nat.sub_zero, Finset.image_id]
    rw [h0]
  · intro k hk b hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact hnet (S-k-1) (by omega) j
  · intro i
    have htel := Finset.sum_range_sub (fun k => a (chain k i)) S
    have hcongr : ∑ k ∈ Finset.range S, (a (chain k i) - a (chain (k+1) i))
        = -∑ k ∈ Finset.range S, (a (chain (k+1) i) - a (chain k i)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => by abel)
    rw [hcongr, htel, hchain0 i]
    abel


/-- **The finite supremum as a `Finset.sup'`.** -/
theorem iSup_finset_eq_sup' {α : Type*} (B : Finset α) (hB : B.Nonempty) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : (⨆ a ∈ B, u a) = B.sup' hB u := by
  haveI : Nonempty α := ⟨hB.choose⟩
  apply le_antisymm
  · apply ciSup_le
    intro b
    by_cases hb : b ∈ B
    · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
      exact Finset.le_sup' u hb
    · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
        Real.sSup_empty]
      exact le_trans (h _) (Finset.le_sup' u hB.choose_spec)
  · refine Finset.sup'_le hB u ?_
    intro b hb
    exact le_iSup_finset B u h hb

/-- **Weighted Cauchy-Schwarz.**  For positive weights `w`, `(∑ x)² ≤ (∑ w)(∑ x²/w)`. -/
theorem weighted_cs {ι : Type*} (s : Finset ι) (x w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, x i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, x i ^ 2 / w i) := by
  classical
  have hkey := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (if i ∈ s then w i else 0))
    (fun i => x i / Real.sqrt (if i ∈ s then w i else 0))
  have hL : ∑ i ∈ s, Real.sqrt (if i ∈ s then w i else 0) *
      (x i / Real.sqrt (if i ∈ s then w i else 0)) = ∑ i ∈ s, x i := by
    apply Finset.sum_congr rfl; intro i hi
    rw [if_pos hi]
    have hne : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hw i hi))
    field_simp
  have hR1 : ∑ i ∈ s, (Real.sqrt (if i ∈ s then w i else 0)) ^ 2 = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl; intro i hi
    rw [if_pos hi, Real.sq_sqrt (le_of_lt (hw i hi))]
  have hR2 : ∑ i ∈ s, (x i / Real.sqrt (if i ∈ s then w i else 0)) ^ 2 = ∑ i ∈ s, x i ^ 2 / w i := by
    apply Finset.sum_congr rfl; intro i hi
    rw [if_pos hi, div_pow, Real.sq_sqrt (le_of_lt (hw i hi))]
  rwa [hL, hR1, hR2] at hkey

/-- **Minkowski/Cauchy-Schwarz for a finite sum of nonnegative functions.**  If the squares of
`A i` have `∫⁻` bounded by `u i ^ 2`, then the square of the sum has `∫⁻` bounded by
`(∑ u i) ^ 2`; the proof is the pointwise weighted Cauchy-Schwarz followed by the fact that `∫⁻`
turns the constant factor outside. -/
theorem BourgainSmoothWindow.lintegral_sq_sum_le_of_class_bounds {ι : Type*} (s : Finset ι)
    (A : ι → ℝ → ℝ) (u : ι → ℝ) (hu : ∀ i ∈ s, 0 < u i)
    (hAnn : ∀ i ∈ s, ∀ y : ℝ, 0 ≤ A i y)
    (hmeas : ∀ i ∈ s, AEMeasurable (fun y => ENNReal.ofReal (A i y) ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hA : ∀ i ∈ s, ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (A i y) ^ 2
      ≤ ENNReal.ofReal ((u i) ^ 2)) :
    ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((∑ i ∈ s, A i y)) ^ 2
      ≤ ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by
  have hu0 : ∀ i ∈ s, 0 ≤ u i := fun i hi => (hu i hi).le
  have hsum_u0 : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg (fun i hi => hu0 i hi)
  have hpt : ∀ y : ℝ, ENNReal.ofReal ((∑ i ∈ s, A i y)) ^ 2
      ≤ (∑ i ∈ s, ENNReal.ofReal (u i)) *
        (∑ i ∈ s, ENNReal.ofReal (A i y) ^ 2 / ENNReal.ofReal (u i)) := by
    intro y
    have hcs := weighted_cs s (fun i => A i y) u (fun i hi => hu i hi)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hu0 i hi),
        ← ENNReal.ofReal_pow (Finset.sum_nonneg (fun i hi => hAnn i hi y)) 2]
    calc ENNReal.ofReal ((∑ i ∈ s, A i y) ^ 2)
        ≤ ENNReal.ofReal ((∑ i ∈ s, u i) * ∑ i ∈ s, A i y ^ 2 / u i) :=
            ENNReal.ofReal_le_ofReal hcs
      _ = ENNReal.ofReal (∑ i ∈ s, u i) * ENNReal.ofReal (∑ i ∈ s, A i y ^ 2 / u i) :=
            ENNReal.ofReal_mul hsum_u0
      _ = ENNReal.ofReal (∑ i ∈ s, u i) * (∑ i ∈ s, ENNReal.ofReal (A i y ^ 2 / u i)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => div_nonneg (sq_nonneg _) (hu0 i hi))]
      _ = ENNReal.ofReal (∑ i ∈ s, u i) *
            (∑ i ∈ s, ENNReal.ofReal (A i y) ^ 2 / ENNReal.ofReal (u i)) := by
            congr 1
            apply Finset.sum_congr rfl; intro i hi
            rw [ENNReal.ofReal_div_of_pos (hu i hi), ENNReal.ofReal_pow (hAnn i hi y) 2]
  calc ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((∑ i ∈ s, A i y)) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, (∑ i ∈ s, ENNReal.ofReal (u i)) *
          (∑ i ∈ s, ENNReal.ofReal (A i y) ^ 2 / ENNReal.ofReal (u i)) := lintegral_mono hpt
    _ = (∑ i ∈ s, ENNReal.ofReal (u i)) * ∫⁻ y in Set.Ioc (0:ℝ) 1,
          (∑ i ∈ s, ENNReal.ofReal (A i y) ^ 2 / ENNReal.ofReal (u i)) := by
          rw [lintegral_const_mul' _ _ (by
            rw [ENNReal.sum_ne_top]
            intro i hi
            exact ENNReal.ofReal_ne_top)]
    _ = (∑ i ∈ s, ENNReal.ofReal (u i)) * ∑ i ∈ s, ∫⁻ y in Set.Ioc (0:ℝ) 1,
          ENNReal.ofReal (A i y) ^ 2 / ENNReal.ofReal (u i) := by
          congr 1
          rw [lintegral_finsetSum']
          intro i hi
          exact ((hmeas i hi).div_const _)
    _ = (∑ i ∈ s, ENNReal.ofReal (u i)) *
          ∑ i ∈ s, (ENNReal.ofReal (u i))⁻¹ *
            (∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (A i y) ^ 2) := by
          congr 1
          apply Finset.sum_congr rfl; intro i hi
          have hdiv : (fun y : ℝ => ENNReal.ofReal (A i y) ^ 2 / ENNReal.ofReal (u i))
              = (fun y : ℝ => (ENNReal.ofReal (u i))⁻¹ * ENNReal.ofReal (A i y) ^ 2) := by
            funext y; rw [ENNReal.div_eq_inv_mul]
          rw [hdiv, lintegral_const_mul'' _ (hmeas i hi)]
    _ ≤ (∑ i ∈ s, ENNReal.ofReal (u i)) *
          ∑ i ∈ s, (ENNReal.ofReal (u i))⁻¹ * ENNReal.ofReal ((u i) ^ 2) := by
          gcongr with i hi
          exact hA i hi
    _ = (∑ i ∈ s, ENNReal.ofReal (u i)) * ∑ i ∈ s, ENNReal.ofReal (u i) := by
          congr 1
          apply Finset.sum_congr rfl; intro i hi
          have h1 : ENNReal.ofReal ((u i) ^ 2) = ENNReal.ofReal (u i) ^ 2 :=
            ENNReal.ofReal_pow (hu0 i hi) 2
          have hne : ENNReal.ofReal (u i) ≠ 0 := by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hu i hi
          have htop : ENNReal.ofReal (u i) ≠ ⊤ := ENNReal.ofReal_ne_top
          rw [h1]
          calc (ENNReal.ofReal (u i))⁻¹ * ENNReal.ofReal (u i) ^ 2
              = (ENNReal.ofReal (u i))⁻¹ * (ENNReal.ofReal (u i) * ENNReal.ofReal (u i)) := by
                rw [pow_two]
            _ = ((ENNReal.ofReal (u i))⁻¹ * ENNReal.ofReal (u i)) * ENNReal.ofReal (u i) := by
                rw [mul_assoc]
            _ = 1 * ENNReal.ofReal (u i) := by rw [ENNReal.inv_mul_cancel hne htop]
            _ = ENNReal.ofReal (u i) := one_mul _
    _ = ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hu0 i hi), ← sq,
              ← ENNReal.ofReal_pow hsum_u0 2]

end BourgainSmoothWindow

/-- **The sup over a finite entropy class of exponential sums.**  Let `λ : Fin K → ℝ` be
`1`-separated and let `B` be a finite set of coefficient vectors with `∑_k ‖b k‖² ≤ R²` for
every `b ∈ B`.  Then the mean square of the maximal exponential sum
`sup_{b ∈ B} |∑_k b_k e^{i λ_k y}|` over `y ∈ [0,1]` is at most `C R² #B`.

This is the per-level estimate (4.24)–(4.25) in Bourgain's proof of his Lemma 4.13: the
near-orthogonality of `1`-separated exponentials
(`Commons.Analysis.Fourier.separated_exponentials_near_orthogonal`) controls the mean square of
each individual exponential sum, and the maximal over the *finite* set `B` is controlled by the
sum over `B` through `(sup_b u_b)² ≤ ∑_b u_b²`.  The integrals are Lebesgue integrals over
`[0,1]` in `ℝ≥0∞`, so no measurability of the pointwise supremum is needed. -/
theorem max_finset_exponential_sum_l2 (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset (Fin K → ℂ)) (R : ℝ), 0 ≤ R →
      (∀ b ∈ B, ∑ k : Fin K, ‖b k‖ ^ 2 ≤ R ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (⨆ b ∈ B, ‖∑ k : Fin K, b k * expChar (lam k) y‖) ^ 2
        ≤ ENNReal.ofReal (C * R ^ 2 * (B.card : ℝ)) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := separated_exponentials_near_orthogonal
  refine ⟨C₀, hC₀pos, ?_⟩
  intro B R hR hB
  set U : (Fin K → ℂ) → ℝ → ℝ := fun b y => ‖∑ k : Fin K, b k * expChar (lam k) y‖ with hU
  have hUcont : ∀ b, Continuous (U b) := by
    intro b
    have : Continuous fun y : ℝ => ∑ k : Fin K, b k * expChar (lam k) y :=
      continuous_finsetSum _ (fun k _ => continuous_const.mul
        (by unfold expChar; fun_prop))
    simpa only [hU] using this.norm
  have hUnn : ∀ b y, 0 ≤ U b y := fun b y => norm_nonneg _
  have hpt : ∀ y : ℝ,
      ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2 ≤ ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
    intro y
    have hsup := BourgainSmoothWindow.iSup_finset_sq_le_sum B (fun b => U b y)
      (fun b => hUnn b y)
    have hnn : 0 ≤ (⨆ b ∈ B, U b y) := BourgainSmoothWindow.iSup_finset_nonneg B (fun b => U b y) (fun b => hUnn b y)
    calc ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
        = ENNReal.ofReal ((⨆ b ∈ B, U b y) ^ 2) := (ENNReal.ofReal_pow hnn 2).symm
      _ ≤ ENNReal.ofReal (∑ b ∈ B, (U b y) ^ 2) := ENNReal.ofReal_le_ofReal hsup
      _ = ∑ b ∈ B, ENNReal.ofReal ((U b y) ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _)
      _ = ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
            apply Finset.sum_congr rfl; intro b _
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
  have hmeas : ∀ b ∈ B, Measurable (fun y : ℝ => ENNReal.ofReal (U b y) ^ 2) := by
    intro b _
    exact ((hUcont b).measurable.ennreal_ofReal.pow_const 2)
  have hint : ∀ b ∈ B, Integrable (fun y : ℝ => (U b y) ^ 2) (volume.restrict (Set.Ioc 0 1)) := by
    intro b _
    have hcont : Continuous (fun y : ℝ => (U b y) ^ 2) := (hUcont b).pow 2
    exact (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  calc ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0 : ℝ) 1, ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := lintegral_mono hpt
    _ = ∑ b ∈ B, ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2 := by
          rw [lintegral_finsetSum]
          intro b hb; exact hmeas b hb
    _ = ∑ b ∈ B, ENNReal.ofReal (∫ y in (0 : ℝ)..1, (U b y) ^ 2) := by
          apply Finset.sum_congr rfl; intro b hb
          have h1 : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2
              = ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((U b y) ^ 2) := by
            apply lintegral_congr; intro y
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
          rw [h1]
          have h2 := ofReal_integral_eq_lintegral_ofReal (hint b hb)
            (ae_of_all _ (fun y => sq_nonneg (U b y)))
          rw [← h2]
          congr 1
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ ≤ ∑ b ∈ B, ENNReal.ofReal (C₀ * R ^ 2) := by
          apply Finset.sum_le_sum; intro b hb
          apply ENNReal.ofReal_le_ofReal
          have hc := hC₀ K lam hsep b
          calc ∫ y in (0 : ℝ)..1, (U b y) ^ 2
              ≤ C₀ * ∑ k : Fin K, ‖b k‖ ^ 2 := by
                rw [hU]; exact hc
            _ ≤ C₀ * R ^ 2 := by
                exact mul_le_mul_of_nonneg_left (hB b hb) (le_of_lt hC₀pos)
    _ = ENNReal.ofReal (C₀ * R ^ 2 * (B.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast (B.card),
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((B.card : ℕ) : ℝ) by positivity)]
          ring_nf

/-- **The entropy-net reduction (Bourgain's (4.24)–(4.25)).**  Let `lam : Fin K → ℝ` be
`1`-separated, let `c : Fin N → Fin K → ℂ` be a finite family of coefficient vectors, and suppose
`T` is a finite `μ`-net for the family `{c i}` in the `ℓ²` sense (`∀ i, ∃ t ∈ T,
∑ k, ‖c i k - t k‖² ≤ μ²`), all of whose members satisfy `∑ k, ‖t k‖² ≤ D²`.

Then the mean square over `y ∈ [0,1]` of the maximal exponential sum
`sup_i ‖∑ k, c i k · e^{i λ_k y}‖` is at most `C (K μ² + D² #T)`.

The point of the statement is the *shape*: the `K μ²` term comes from the trivial `ℓ¹` bound on
the difference `c i - t` (Cauchy–Schwarz in `Fin K`), and the `D² #T` term from the per-level
near-orthogonality estimate `max_finset_exponential_sum_l2` applied to the finite class `T`.  This
is the mechanism by which Bourgain's entropy decomposition of the pointwise family
`{(f_j * φ_{2^{-j-1}})(x)}` controls the maximal function. -/
theorem sup_exp_sum_le_of_net (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (c : Fin N → Fin K → ℂ)
        (T : Finset (Fin K → ℂ)) (μ D : ℝ), 0 ≤ μ → 0 ≤ D →
      (∀ i : Fin N, ∃ t ∈ T, ∑ k : Fin K, ‖c i k - t k‖ ^ 2 ≤ μ ^ 2) →
      (∀ t ∈ T, ∑ k : Fin K, ‖t k‖ ^ 2 ≤ D ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (⨆ i : Fin N,
            ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2
        ≤ ENNReal.ofReal (C * ((K : ℝ) * μ ^ 2 + D ^ 2 * (T.card : ℝ))) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := max_finset_exponential_sum_l2 K lam hsep
  refine ⟨max 2 (2 * C₀), lt_max_of_lt_left (by norm_num), ?_⟩
  intro N c T μ D hμ hD hnet hDbound
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hz : ∀ y : ℝ, (⨆ i : Fin 0, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) = 0 :=
      fun y => Real.iSup_of_isEmpty _
    rw [show (fun y : ℝ => ENNReal.ofReal
          (⨆ i : Fin 0, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) from funext (fun y => by rw [hz y]; simp)]
    simp
  · have hne : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    let W : (Fin K → ℂ) → ℝ → ℝ := fun t y => ‖∑ k : Fin K, t k * expChar (lam k) y‖
    have hWnn : ∀ t y, 0 ≤ W t y := fun t y => norm_nonneg _
    let rep : Fin N → Fin K → ℂ := fun i => Classical.choose (hnet i)
    have hrepT : ∀ i, rep i ∈ T := fun i => (Classical.choose_spec (hnet i)).1
    have hrepd : ∀ i, ∑ k : Fin K, ‖c i k - rep i k‖ ^ 2 ≤ μ ^ 2 :=
      fun i => (Classical.choose_spec (hnet i)).2
    have hpt : ∀ y : ℝ, ENNReal.ofReal
          (⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2
        ≤ ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2)
          + ENNReal.ofReal 2 * ENNReal.ofReal (⨆ t ∈ T, W t y) ^ 2 := by
      intro y
      have h1 : ∀ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖
          ≤ Real.sqrt K * μ + (⨆ t ∈ T, W t y) := by
        intro i
        have hdecomp : (∑ k : Fin K, c i k * expChar (lam k) y)
            = (∑ k : Fin K, (c i k - rep i k) * expChar (lam k) y)
              + (∑ k : Fin K, rep i k * expChar (lam k) y) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        have hWle : W (rep i) y ≤ ⨆ t ∈ T, W t y :=
          BourgainSmoothWindow.le_iSup_finset T (fun t => W t y) (fun t => hWnn t y) (hrepT i)
        have hCS : (∑ k : Fin K, ‖c i k - rep i k‖) ≤ Real.sqrt K * μ := by
          refine (BourgainSmoothWindow.sum_norm_le_sqrt_card_mul_sqrt_sum_sq
            (fun k => c i k - rep i k)).trans ?_
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg K)
          rw [← Real.sqrt_sq hμ]
          exact Real.sqrt_le_sqrt (hrepd i)
        calc ‖∑ k : Fin K, c i k * expChar (lam k) y‖
            = ‖(∑ k : Fin K, (c i k - rep i k) * expChar (lam k) y)
                + (∑ k : Fin K, rep i k * expChar (lam k) y)‖ := by rw [← hdecomp]
          _ ≤ ‖∑ k : Fin K, (c i k - rep i k) * expChar (lam k) y‖
                + ‖∑ k : Fin K, rep i k * expChar (lam k) y‖ := norm_add_le _ _
          _ ≤ (∑ k : Fin K, ‖c i k - rep i k‖) + (⨆ t ∈ T, W t y) := by
              refine add_le_add ?_ hWle
              refine (norm_sum_le _ _).trans (le_of_eq ?_)
              exact Finset.sum_congr rfl (fun k _ => by
                simp [expChar, Complex.norm_exp, Complex.mul_re])
          _ ≤ Real.sqrt K * μ + (⨆ t ∈ T, W t y) := by linarith
      have hsup : (⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖)
          ≤ Real.sqrt K * μ + (⨆ t ∈ T, W t y) := ciSup_le h1
      have hbdd : BddAbove (Set.range (fun i : Fin N =>
            ‖∑ k : Fin K, c i k * expChar (lam k) y‖)) :=
        ⟨Real.sqrt K * μ + (⨆ t ∈ T, W t y), by rintro _ ⟨i, rfl⟩; exact h1 i⟩
      have hLnn : 0 ≤ (⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) :=
        le_trans (norm_nonneg _) (le_ciSup hbdd (Classical.arbitrary (Fin N)))
      have hBTnn : 0 ≤ (⨆ t ∈ T, W t y) :=
        BourgainSmoothWindow.iSup_finset_nonneg T (fun t => W t y) (fun t => hWnn t y)
      have hsq : (⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2
          ≤ 2 * (K : ℝ) * μ ^ 2 + 2 * (⨆ t ∈ T, W t y) ^ 2 := by
        refine (pow_le_pow_left₀ hLnn hsup 2).trans ?_
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg K),
          sq_nonneg (Real.sqrt K * μ - (⨆ t ∈ T, W t y))]
      calc ENNReal.ofReal (⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2
          = ENNReal.ofReal ((⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2) :=
            (ENNReal.ofReal_pow hLnn 2).symm
        _ ≤ ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2 + 2 * (⨆ t ∈ T, W t y) ^ 2) :=
            ENNReal.ofReal_le_ofReal hsq
        _ = ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2) + ENNReal.ofReal (2 * (⨆ t ∈ T, W t y) ^ 2) :=
            ENNReal.ofReal_add (by positivity) (by positivity)
        _ = ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2)
              + ENNReal.ofReal 2 * ENNReal.ofReal (⨆ t ∈ T, W t y) ^ 2 := by
            congr 1
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow hBTnn 2]
    have hTbound := hC₀ T D hD hDbound
    have hper : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (⨆ t ∈ T, W t y) ^ 2
        ≤ ENNReal.ofReal (C₀ * D ^ 2 * (T.card : ℝ)) := hTbound
    calc ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
            (⨆ i : Fin N, ‖∑ k : Fin K, c i k * expChar (lam k) y‖) ^ 2
        ≤ ∫⁻ y in Set.Ioc (0 : ℝ) 1, (ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2)
            + ENNReal.ofReal 2 * ENNReal.ofReal (⨆ t ∈ T, W t y) ^ 2) := lintegral_mono hpt
      _ = ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2) * volume (Set.Ioc (0 : ℝ) 1)
            + ENNReal.ofReal 2 * ∫⁻ y in Set.Ioc (0 : ℝ) 1,
                ENNReal.ofReal (⨆ t ∈ T, W t y) ^ 2 := by
          rw [lintegral_add_left measurable_const]
          congr 1
          · rw [lintegral_const, Measure.restrict_apply_univ]
          · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2) * volume (Set.Ioc (0 : ℝ) 1)
            + ENNReal.ofReal 2 * ENNReal.ofReal (C₀ * D ^ 2 * (T.card : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2)
            + ENNReal.ofReal (2 * (C₀ * D ^ 2 * (T.card : ℝ))) := by
          rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal (2 * (K : ℝ) * μ ^ 2 + 2 * (C₀ * D ^ 2 * (T.card : ℝ))) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (max 2 (2 * C₀)
            * ((K : ℝ) * μ ^ 2 + D ^ 2 * (T.card : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have h2 : (2 : ℝ) ≤ max 2 (2 * C₀) := le_max_left _ _
          have h2C : 2 * C₀ ≤ max 2 (2 * C₀) := le_max_right _ _
          have hKm : 0 ≤ (K : ℝ) * μ ^ 2 := by positivity
          have hDm : 0 ≤ D ^ 2 * (T.card : ℝ) := by positivity
          nlinarith [hKm, hDm, mul_le_mul_of_nonneg_right h2 hKm,
            mul_le_mul_of_nonneg_right h2C hDm]

open BoundaryLayer in
/-- **Frequency slices are `L²`-bounded** (the first step of Bourgain's Lemma 4.13 and of
Krause's Proposition 2.5).

Let `lam : Fin K → ℝ` be `1`-separated, and let `ψ` be a bounded (`‖ψ‖ ≤ 1`) multiplier with
support in `[-r,r]` for some `r < 1/2`.  For `f ∈ L²(ℝ, ℂ)` put
`f_j := 𝓕⁻(ξ ↦ 𝓕f(ξ + λ_j) · ψ(ξ))`, i.e. the multiplier with symbol `ξ ↦ ψ(ξ - λ_j)` applied to
`f`.  Then `∑_j ‖f_j‖²_{L²} ≤ ‖f‖²_{L²}`.

The proof is Plancherel: `∑_j ‖f_j‖² = ∫_ξ (∑_j ‖ψ(ξ-λ_j)‖²)·‖𝓕f(ξ)‖² dξ`, and
`∑_j ‖ψ(ξ-λ_j)‖² ≤ 1` because the supports `λ_j + [-r,r]` are pairwise disjoint (the `λ_j` are
`1`-separated and `2r < 1`). -/
theorem slices_l2_le (K : ℕ) (lam : Fin K → ℝ) (r : ℝ) (hr : r < 1/2)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (ψ : ℝ → ℂ) (hψmeas : Measurable ψ)
    (hψsupp : ∀ x : ℝ, ψ x ≠ 0 → |x| ≤ r) (hψbd : ∀ x : ℝ, ‖ψ x‖ ≤ 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∑ j : Fin K, ‖multiplier (fun ξ => ψ (ξ - lam j)) (by
        exact memLp_top_of_bound ((hψmeas.comp (measurable_id.sub measurable_const)).aestronglyMeasurable)
          1 (Filter.Eventually.of_forall (fun ξ => hψbd (ξ - lam j)))) f‖ₑ ^ (2:ℝ)
      ≤ ‖f‖ₑ ^ (2:ℝ) := by
  have hmem : ∀ j : Fin K, MemLp (fun ξ : ℝ => ψ (ξ - lam j)) ⊤ (volume : Measure ℝ) := fun j =>
    memLp_top_of_bound ((hψmeas.comp (measurable_id.sub measurable_const)).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall (fun ξ => hψbd (ξ - lam j)))
  have hterm_le : ∀ (ξ : ℝ) (j : Fin K),
      ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ) ≤ if ψ (ξ - lam j) = 0 then 0 else 1 := by
    intro ξ j
    by_cases h : ψ (ξ - lam j) = 0
    · simp [h]
    · rw [if_neg h]
      have hbd := hψbd (ξ - lam j)
      have hx : (0:ℝ) ≤ ‖ψ (ξ - lam j)‖ := norm_nonneg _
      calc ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ)
          = ENNReal.ofReal ‖ψ (ξ - lam j)‖ ^ (2:ℝ) :=
            congrArg (· ^ (2:ℝ)) (BoundaryLayer.enorm_eq_ofReal_norm _)
        _ = ENNReal.ofReal (‖ψ (ξ - lam j)‖ ^ (2:ℝ)) :=
            (ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0:ℝ) ≤ 2))
        _ = ENNReal.ofReal (‖ψ (ξ - lam j)‖ ^ 2) := by rw [Real.rpow_two, pow_two]
        _ ≤ ENNReal.ofReal (1 ^ 2) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [hbd, hx])
        _ = 1 := by norm_num
  have hkey : ∀ ξ : ℝ, ∑ j : Fin K, ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ) ≤ 1 := by
    intro ξ
    by_cases hex : ∃ j : Fin K, ψ (ξ - lam j) ≠ 0
    · obtain ⟨j₀, hj₀⟩ := hex
      have hsingle : ∑ j : Fin K, ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ) = ‖ψ (ξ - lam j₀)‖ₑ ^ (2:ℝ) := by
        refine Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ j₀) ?_
        intro c _ hc
        by_contra hcne
        have hcψ : ψ (ξ - lam c) ≠ 0 := by
          intro hz; exact hcne (by rw [hz]; simp)
        have h1 : |ξ - lam c| ≤ r := hψsupp (ξ - lam c) hcψ
        have h2 : |ξ - lam j₀| ≤ r := hψsupp (ξ - lam j₀) hj₀
        have h3 : |lam c - ξ| ≤ r := by rw [abs_sub_comm]; exact h1
        have h4 : |lam c - lam j₀| ≤ |lam c - ξ| + |ξ - lam j₀| := abs_sub_le _ _ _
        linarith [hsep c j₀ hc, hr, h2, h3, h4]
      rw [hsingle]
      exact le_trans (hterm_le ξ j₀) (by rw [if_neg hj₀])
    · push Not at hex
      simp [hex]
  have hae : ∀ j : Fin K, AEMeasurable (fun ξ : ℝ =>
      ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)) (volume : Measure ℝ) := fun j =>
    AEMeasurable.mul (((hψmeas.comp (measurable_id.sub measurable_const)).enorm.pow_const _).aemeasurable)
      ((MeasureTheory.Lp.aestronglyMeasurable (𝓕 f)).enorm.pow_const _)
  calc ∑ j : Fin K, ‖multiplier (fun ξ => ψ (ξ - lam j)) (hmem j) f‖ₑ ^ (2:ℝ)
      = ∑ j : Fin K, ∫⁻ ξ, ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          apply Finset.sum_congr rfl; intro j _
          exact enorm_multiplier_sq _ _ _
    _ = ∫⁻ ξ, ∑ j : Fin K, ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          rw [lintegral_finsetSum']
          intro j _
          exact hae j
    _ = ∫⁻ ξ, (∑ j : Fin K, ‖ψ (ξ - lam j)‖ₑ ^ (2:ℝ)) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          apply lintegral_congr; intro ξ; rw [Finset.sum_mul]
    _ ≤ ∫⁻ ξ, 1 * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          apply lintegral_mono; intro ξ
          exact mul_le_mul_of_nonneg_right (hkey ξ)
            (bot_le : (⊥ : ℝ≥0∞) ≤ ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ))
    _ = ‖f‖ₑ ^ (2:ℝ) := by
          simp only [one_mul]
          rw [← enorm_fourier f]
          exact (lp_enorm_sq_eq_lintegral (𝓕 f)).symm

open BourgainSmoothWindow in
theorem sup_exp_sum_le_entropy_sum (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N S : ℕ) (a : Fin N → (Fin K → ℂ)) (σ : ℕ → Fin N → Fin N)
        (D : ℝ), 0 ≤ D →
      (∀ i : Fin N, ∑ k : Fin K, ‖a i k‖ ^ 2 ≤ D ^ 2) →
      (∀ s, s ≤ S → ∀ i : Fin N,
        ∑ k : Fin K, ‖a i k - a (σ s i) k‖ ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ s) ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (⨆ i : Fin N, ‖∑ k : Fin K, a i k * expChar (lam k) y‖) ^ 2
        ≤ ENNReal.ofReal (C * (D * Real.sqrt (N + 1) +
            ∑ t ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ t * Real.sqrt
              (((Finset.univ.image (σ t)).card : ℝ) + N + 1)) ^ 2) := by
  classical
  obtain ⟨c₀, hc₀pos, hc₀⟩ := max_finset_exponential_sum_l2 K lam hsep
  refine ⟨100 * (c₀ + 1), by positivity, ?_⟩
  intro N S a σ D hD hDa hnet2
  rcases Nat.eq_zero_or_pos N with hN | hNpos
  · subst hN
    have hz : ∀ y : ℝ, (⨆ i : Fin 0, ‖∑ k : Fin K, a i k * expChar (lam k) y‖) = 0 :=
      fun y => Real.iSup_of_isEmpty _
    rw [show (fun y : ℝ => ENNReal.ofReal
          (⨆ i : Fin 0, ‖∑ k : Fin K, a i k * expChar (lam k) y‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) from funext (fun y => by rw [hz y]; simp)]
    simp
  haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hnet : ∀ s, s ≤ S → ∀ i : Fin N, ‖a i - a (σ s i)‖ ≤ 2 * (1/2:ℝ)^s := by
    intro s hs i
    have h2 := hnet2 s hs i
    have hsqrt : Real.sqrt (∑ k : Fin K, ‖a i k - a (σ s i) k‖^2) ≤ 2 * (1/2:ℝ)^s := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (1/2:ℝ)^s)]
      exact Real.sqrt_le_sqrt h2
    refine le_trans ?_ hsqrt
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    calc ‖(a i - a (σ s i)) k‖ = ‖a i k - a (σ s i) k‖ := by rw [Pi.sub_apply]
      _ = Real.sqrt (‖a i k - a (σ s i) k‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ x : Fin K, ‖a i x - a (σ s i) x‖^2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum
            (fun x (_ : x ∈ Finset.univ) => sq_nonneg (‖a i x - a (σ s i) x‖))
            (Finset.mem_univ k))
  obtain ⟨q, B, hqsub, hqmem, hqBeq, hqcard, hqcard0, hqcard0diff, hqnorm, hqdecomp⟩ :=
    BourgainSmoothWindow.exists_dyadic_chain_decomposition N S a σ hnet
  let Φ : ℝ → (Fin K → ℂ) → ℂ := fun y v => ∑ k : Fin K, v k * expChar (lam k) y
  have hΦadd : ∀ y (u v : Fin K → ℂ), Φ y (u + v) = Φ y u + Φ y v := by
    intro y u v
    simp only [Φ, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hΦsum : ∀ y (s : Finset ℕ) (u : ℕ → Fin K → ℂ),
      Φ y (∑ k ∈ s, u k) = ∑ k ∈ s, Φ y (u k) := by
    intro y s u
    simp only [Φ, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hΦcont : ∀ b : Fin K → ℂ, Continuous (fun y : ℝ => Φ y b) := by
    intro b
    simp only [Φ]
    refine continuous_finsetSum _ (fun k _ => continuous_const.mul ?_)
    unfold expChar; fun_prop
  let Ctop : Finset (Fin K → ℂ) := (Finset.univ.image (q S)).image (fun i => a i)
  have hCtop_ne : Ctop.Nonempty :=
    ⟨a (q S ⟨0, hNpos⟩), Finset.mem_image.mpr ⟨q S ⟨0, hNpos⟩,
      Finset.mem_image.mpr ⟨⟨0, hNpos⟩, Finset.mem_univ _, rfl⟩, rfl⟩⟩
  have hB_ne : ∀ k, (B k).Nonempty := by
    intro k
    refine ⟨a (q k ⟨0, hNpos⟩) - a (σ (S - k - 1) (q k ⟨0, hNpos⟩)), ?_⟩
    rw [hqBeq k]
    exact Finset.mem_image.mpr ⟨q k ⟨0, hNpos⟩,
      Finset.mem_image.mpr ⟨⟨0, hNpos⟩, Finset.mem_univ _, rfl⟩, rfl⟩
  -- classes indexed so that `cls j = B j` for `j < S` and `cls S = Ctop`
  let cls : ℕ → Finset (Fin K → ℂ) := fun j => if j < S then B j else Ctop
  have hcls_ne : ∀ j, (cls j).Nonempty := by
    intro j
    by_cases hj : j < S
    · have h1 : cls j = B j := by
        show (if j < S then B j else Ctop) = B j
        rw [if_pos hj]
      rw [h1]; exact hB_ne j
    · have h1 : cls j = Ctop := by
        show (if j < S then B j else Ctop) = Ctop
        rw [if_neg hj]
      rw [h1]; exact hCtop_ne
  have hclsS : cls S = Ctop := by
    show (if S < S then B S else Ctop) = Ctop
    rw [if_neg (lt_irrefl S)]
  have hclsj : ∀ j, j < S → cls j = B j := by
    intro j hj
    show (if j < S then B j else Ctop) = B j
    rw [if_pos hj]
  let Acls : ℕ → ℝ → ℝ := fun j y => (cls j).sup' (hcls_ne j) (fun b => ‖Φ y b‖)
  have hAcls_cont : ∀ j, Continuous (Acls j) := fun j =>
    Continuous.finset_sup'_apply (hcls_ne j) (fun b _ => (hΦcont b).norm)
  have hAcls_nn : ∀ j y, 0 ≤ Acls j y := by
    intro j y
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖Φ y b‖) (hcls_ne j).choose_spec)
  have hper : ∀ y i, ‖Φ y (a i)‖ ≤ Acls S y + ∑ k ∈ Finset.range S, Acls k y := by
    intro y i
    have hA0 : Acls S y = (⨆ b ∈ Ctop, ‖Φ y b‖) := by
      simp only [Acls, hclsS]
      exact (iSup_finset_eq_sup' Ctop hCtop_ne (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)).symm
    have hAk : ∀ k, k < S → Acls k y = (⨆ b ∈ B k, ‖Φ y b‖) := by
      intro k hk
      simp only [Acls, hclsj k hk]
      exact (iSup_finset_eq_sup' (B k) (hB_ne k) (fun b => ‖Φ y b‖)
        (fun b => norm_nonneg _)).symm
    have hsumk : ∑ k ∈ Finset.range S, Acls k y
        = ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) :=
      Finset.sum_congr rfl (fun k hk => hAk k (Finset.mem_range.mp hk))
    rw [hA0, hsumk]
    have hsplit2 : Φ y (a i) = Φ y (a (q S i))
        + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i)) := by
      conv_lhs => rw [hqdecomp i]
      rw [hΦadd, hΦsum]
    calc ‖Φ y (a i)‖
        = ‖Φ y (a (q S i)) + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := by
          rw [hsplit2]
      _ ≤ ‖Φ y (a (q S i))‖
            + ‖∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := norm_add_le _ _
      _ ≤ (⨆ b ∈ Ctop, ‖Φ y b‖) + ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) := by
          apply add_le_add
          · exact le_iSup_finset Ctop (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)
              (Finset.mem_image.mpr ⟨q S i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩)
          · refine (norm_sum_le _ _).trans ?_
            apply Finset.sum_le_sum; intro k hk
            exact le_iSup_finset (B k) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)
              (hqmem k (Finset.mem_range.mp hk) i)
  have hdom : ∀ y, (⨆ i : Fin N, ‖Φ y (a i)‖) ≤ ∑ j ∈ Finset.range (S+1), Acls j y := by
    intro y
    rw [Finset.sum_range_succ]
    exact ciSup_le (fun i => (hper y i).trans (le_of_eq (add_comm _ _)))
  have hsup0 : ∀ y, (0:ℝ) ≤ ⨆ i : Fin N, ‖Φ y (a i)‖ := fun y =>
    le_trans (norm_nonneg _) (le_ciSup
      (⟨Acls S y + ∑ k ∈ Finset.range S, Acls k y, by
        rintro z ⟨i, rfl⟩
        exact hper y i⟩ : BddAbove (Set.range (fun i : Fin N => ‖Φ y (a i)‖)))
      ⟨0, hNpos⟩)
  -- per-class integral bounds
  have hA_top' : ∀ j, ¬ j < S → ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls j y) ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt c₀ * D * Real.sqrt (N + 1)) ^ 2) := by
    intro j hjS
    have hclsj : cls j = Ctop := by
      show (if j < S then B j else Ctop) = Ctop
      rw [if_neg hjS]
    have hAeq : Acls j = fun y => (⨆ b ∈ Ctop, ‖Φ y b‖) := by
      funext y
      simp only [Acls, hclsj]
      exact (iSup_finset_eq_sup' Ctop hCtop_ne (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)).symm
    rw [hAeq]
    have hmem : ∀ b ∈ Ctop, ∑ k : Fin K, ‖b k‖ ^ 2 ≤ D ^ 2 := by
      intro b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      exact hDa i
    have h1 := hc₀ Ctop D hD hmem
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcard : (Ctop.card : ℝ) ≤ N := by
      have h2 : ((Finset.univ.image (q S)).card : ℝ) ≤ N := by
        have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Fin N))) (f := q S)
        simp only [Finset.card_univ, Fintype.card_fin] at h3
        exact_mod_cast h3
      have h3 : ((Ctop).card : ℝ) ≤ ((Finset.univ.image (q S)).card : ℝ) := by
        exact_mod_cast Finset.card_image_le (s := Finset.univ.image (q S)) (f := fun i => a i)
      linarith
    have hN1 : (0:ℝ) < N + 1 := by positivity
    have hsq : (Real.sqrt c₀ * D * Real.sqrt (N + 1)) ^ 2 = c₀ * D^2 * (N+1) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc₀pos.le, Real.sq_sqrt hN1.le]
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc₀pos.le (sq_nonneg D))
  have hA_cls : ∀ k, k < S → ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - k - 1))
          * Real.sqrt (((B k).card : ℝ) + 1)) ^ 2) := by
    intro k hk
    have hAeq : Acls k = fun y => (⨆ b ∈ B k, ‖Φ y b‖) := by
      funext y
      simp only [Acls, hclsj k hk]
      exact (iSup_finset_eq_sup' (B k) (hB_ne k) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)).symm
    rw [hAeq]
    have hmem : ∀ b ∈ B k, ∑ k' : Fin K, ‖b k'‖ ^ 2 ≤ (2 * (1/2:ℝ)^(S-k-1)) ^ 2 := by
      intro b hb
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hqBeq k ▸ hb)
      exact hnet2 (S-k-1) (by omega) j
    have h1 := hc₀ (B k) (2 * (1/2:ℝ)^(S-k-1)) (by positivity) hmem
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : (Real.sqrt c₀ * (2 * (1/2:ℝ)^(S-k-1)) * Real.sqrt (((B k).card : ℝ) + 1)) ^ 2
        = c₀ * (2 * (1/2:ℝ)^(S-k-1))^2 * (((B k).card : ℝ) + 1) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc₀pos.le,
          Real.sq_sqrt (by exact add_nonneg (Nat.cast_nonneg _) zero_le_one)]
    rw [hsq]
    have hle : ((B k).card : ℝ) ≤ ((B k).card : ℝ) + 1 := by linarith
    have hnn : (0:ℝ) ≤ c₀ * (2 * (1/2:ℝ)^(S-k-1))^2 :=
      mul_nonneg hc₀pos.le (sq_nonneg (2 * (1/2:ℝ)^(S-k-1)))
    exact mul_le_mul_of_nonneg_left hle hnn
  -- the weight sequence
  let uu : ℕ → ℝ := fun j => (if j < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
        * Real.sqrt (((B j).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
      + (1/2:ℝ)^(j+1)
  have huu_pos : ∀ j ∈ Finset.range (S+1), 0 < uu j := by
    intro j hj
    have hε : 0 < (1/2:ℝ)^(j+1) := by positivity
    by_cases hjS : j < S
    · have h1 : uu j = Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) + (1/2:ℝ)^(j+1) := by
        show (if j < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
          + (1/2:ℝ)^(j+1) = _
        rw [if_pos hjS]
      rw [h1]
      have h2 : 0 ≤ Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_nonneg _)
      linarith
    · have h1 : uu j = Real.sqrt c₀ * D * Real.sqrt (N+1) + (1/2:ℝ)^(j+1) := by
        show (if j < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
          + (1/2:ℝ)^(j+1) = _
        rw [if_neg hjS]
      rw [h1]
      have h2 : 0 ≤ Real.sqrt c₀ * D * Real.sqrt (N+1) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hD) (Real.sqrt_nonneg _)
      linarith
  have huu_meas : ∀ j ∈ Finset.range (S+1),
      AEMeasurable (fun y => ENNReal.ofReal (Acls j y) ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    fun j _ => ((hAcls_cont j).measurable.ennreal_ofReal.pow_const 2).aemeasurable
  have huu_bound : ∀ j ∈ Finset.range (S+1),
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls j y) ^ 2 ≤ ENNReal.ofReal ((uu j) ^ 2) := by
    intro j hj
    have hjle : j ≤ S := by rw [Finset.mem_range] at hj; omega
    by_cases hjS : j < S
    · have h1 : uu j = Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) + (1/2:ℝ)^(j+1) := by
        show (if j < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
          + (1/2:ℝ)^(j+1) = _
        rw [if_pos hjS]
      rw [h1]
      refine (hA_cls j hjS).trans (ENNReal.ofReal_le_ofReal ?_)
      have hb : 0 ≤ Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_nonneg _)
      exact pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 2
    · have h1 : uu j = Real.sqrt c₀ * D * Real.sqrt (N+1) + (1/2:ℝ)^(j+1) := by
        show (if j < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
          * Real.sqrt (((B j).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
          + (1/2:ℝ)^(j+1) = _
        rw [if_neg hjS]
      rw [h1]
      refine (hA_top' j hjS).trans (ENNReal.ofReal_le_ofReal ?_)
      have hb : 0 ≤ Real.sqrt c₀ * D * Real.sqrt (N+1) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hD) (Real.sqrt_nonneg _)
      exact pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 2
  have hmain := BourgainSmoothWindow.lintegral_sq_sum_le_of_class_bounds (Finset.range (S+1)) Acls uu huu_pos
    (fun j _ y => hAcls_nn j y) huu_meas huu_bound
  refine le_trans ?_ (le_trans hmain (ENNReal.ofReal_le_ofReal ?_))
  · apply lintegral_mono
    intro y
    simp only
    have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (S+1), Acls j y :=
      Finset.sum_nonneg (fun j _ => hAcls_nn j y)
    rw [← ENNReal.ofReal_pow hsum0 2, ← ENNReal.ofReal_pow (hsup0 y) 2]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hsup0 y) (hdom y) 2)
  · -- final numeric bound on `(∑ uu)²`
    have htnn : ∀ t : ℕ, (0:ℝ) ≤ (1/2:ℝ)^t * Real.sqrt
        (((Finset.univ.image (σ t)).card : ℝ) + N + 1) :=
      fun t => mul_nonneg (pow_nonneg (by norm_num) t) (Real.sqrt_nonneg _)
    set T : ℝ := D * Real.sqrt (N + 1) +
      ∑ t ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ t * Real.sqrt
        (((Finset.univ.image (σ t)).card : ℝ) + N + 1) with hT
    have hTnn : 0 ≤ T := by
      rw [hT]
      exact add_nonneg (mul_nonneg hD (Real.sqrt_nonneg _))
        (Finset.sum_nonneg (fun t _ => htnn t))
    have hT1 : 1 ≤ T := by
      rw [hT]
      have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
      have h0 : (1:ℝ) ≤ (1/2:ℝ)^0 * Real.sqrt
          (((Finset.univ.image (σ 0)).card : ℝ) + N + 1) := by
        rw [pow_zero, one_mul]
        calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt (((Finset.univ.image (σ 0)).card : ℝ) + (N : ℝ) + 1) := by
              apply Real.sqrt_le_sqrt
              have hc : (0:ℝ) ≤ ((Finset.univ.image (σ 0)).card : ℝ) := Nat.cast_nonneg _
              have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
              linarith
      have hsum : (1:ℝ) ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt
          (((Finset.univ.image (σ t)).card : ℝ) + N + 1) :=
        le_trans h0 (Finset.single_le_sum (fun t _ => htnn t) hmem)
      have hDterm : (0:ℝ) ≤ D * Real.sqrt (N+1) := mul_nonneg hD (Real.sqrt_nonneg _)
      linarith
    have hBcard : ∀ k, (B k).card ≤ N := by
      intro k
      have h1 : (B k).card ≤ (Finset.univ.image (q k)).card := by
        rw [hqBeq k]; exact Finset.card_image_le
      have h2 : (Finset.univ.image (q k)).card ≤ N := by
        have := Finset.card_image_le (s := (Finset.univ : Finset (Fin N))) (f := q k)
        simpa only [Finset.card_univ, Fintype.card_fin] using this
      exact le_trans h1 h2
    have hgs' : ∀ n : ℕ, ∑ j ∈ Finset.range n, (1/2:ℝ)^j ≤ 2 := by
      intro n
      have h1 : ∑ j ∈ Finset.range n, (1/2:ℝ)^j = 2 * (1 - (1/2:ℝ)^n) := by
        have h2 : ∑ j ∈ Finset.range n, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1)) = 1 - (1/2:ℝ)^n := by
          have h3 := Finset.sum_range_sub (fun j => (1/2:ℝ)^j) n
          rw [pow_zero] at h3
          have h4 : ∑ j ∈ Finset.range n, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
              = -∑ j ∈ Finset.range n, ((1/2:ℝ)^(j+1) - (1/2:ℝ)^j) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun j _ => by ring)
          rw [h4, h3]; ring
        rw [← h2, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_succ]; ring
      rw [h1]
      have : (0:ℝ) ≤ 2 * (1/2:ℝ)^n := by positivity
      linarith
    have hgeom2 : ∑ k ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - k - 1) ≤ 4 := by
      have hrefl : (∑ k ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - k - 1))
          = ∑ j ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^j := by
        rw [show (∑ k ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - k - 1))
            = ∑ k ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - 1 - k) from
          Finset.sum_congr rfl (fun k _ => by
            rw [show S - k - 1 = S - 1 - k from by omega])]
        exact Finset.sum_range_reflect (fun j => (2:ℝ) * (1/2:ℝ)^j) S
      rw [hrefl, ← Finset.mul_sum]
      have := hgs' S
      linarith
    have hWle : D * Real.sqrt (N + 1) + ∑ k ∈ Finset.range S,
        (2:ℝ) * (1/2:ℝ)^(S - k - 1) * Real.sqrt (((B k).card : ℝ) + 1) ≤ 5 * T := by
      have hDterm : D * Real.sqrt (N+1) ≤ T := by
        rw [hT]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun t _ => htnn t))
      have hsum : ∑ k ∈ Finset.range S,
          (2:ℝ) * (1/2:ℝ)^(S - k - 1) * Real.sqrt (((B k).card : ℝ) + 1)
          ≤ 4 * Real.sqrt (N+1) := by
        have hterm : ∀ k ∈ Finset.range S,
            (2:ℝ) * (1/2:ℝ)^(S - k - 1) * Real.sqrt (((B k).card : ℝ) + 1)
            ≤ (2:ℝ) * (1/2:ℝ)^(S - k - 1) * Real.sqrt (N+1) := by
          intro k hk
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.sqrt_le_sqrt
          have hk' : ((B k).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hBcard k
          have hc : (0:ℝ) ≤ ((B k).card : ℝ) := Nat.cast_nonneg _
          linarith
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.sum_mul]
        nlinarith [hgeom2, Real.sqrt_nonneg (N+1)]
      have hTsqrt : Real.sqrt (N+1) ≤ T := by
        rw [hT]
        have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
        have h0 : Real.sqrt (N+1) ≤ (1/2:ℝ)^0 * Real.sqrt
            (((Finset.univ.image (σ 0)).card : ℝ) + N + 1) := by
          rw [pow_zero, one_mul]
          apply Real.sqrt_le_sqrt
          have hc : (0:ℝ) ≤ ((Finset.univ.image (σ 0)).card : ℝ) := Nat.cast_nonneg _
          have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
          linarith
        have hsum' : Real.sqrt (N+1) ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt
            (((Finset.univ.image (σ t)).card : ℝ) + N + 1) :=
          le_trans h0 (Finset.single_le_sum (fun t _ => htnn t) hmem)
        have := mul_nonneg hD (Real.sqrt_nonneg (N+1))
        linarith
      linarith
    have hsumuu : ∑ j ∈ Finset.range (S+1), uu j ≤ Real.sqrt c₀ * (5 * T) + 2 := by
      rw [Finset.sum_range_succ]
      -- split off the last term
      have hlast : (if S < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - S - 1))
            * Real.sqrt (((B S).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
            + (1/2:ℝ)^(S+1) ≤ Real.sqrt c₀ * D * Real.sqrt (N+1) + 1 := by
        rw [if_neg (lt_irrefl S)]
        have : (1/2:ℝ)^(S+1) ≤ 1 := by
          exact pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      have hfirst : ∑ j ∈ Finset.range S, uu j
          ≤ Real.sqrt c₀ * (∑ k ∈ Finset.range S,
              (2:ℝ) * (1/2:ℝ)^(S - k - 1) * Real.sqrt (((B k).card : ℝ) + 1))
            + ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) := by
        have hterm : ∀ j ∈ Finset.range S, uu j ≤ Real.sqrt c₀ *
            ((2:ℝ) * (1/2:ℝ)^(S - j - 1) * Real.sqrt (((B j).card : ℝ) + 1))
            + (1/2:ℝ)^(j+1) := by
          intro j hj
          have hjS : j < S := Finset.mem_range.mp hj
          show (if j < S then Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1))
            * Real.sqrt (((B j).card : ℝ) + 1) else Real.sqrt c₀ * D * Real.sqrt (N+1))
            + (1/2:ℝ)^(j+1) ≤ _
          rw [if_pos hjS]
          have : Real.sqrt c₀ * (2 * (1/2:ℝ)^(S - j - 1)) * Real.sqrt (((B j).card:ℝ)+1)
              = Real.sqrt c₀ * ((2:ℝ) * (1/2:ℝ)^(S - j - 1) * Real.sqrt (((B j).card:ℝ)+1)) := by
            ring
          rw [this]
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      have hgeomsmall : ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) ≤ 1 := by
        rw [show (∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1))
            = (1/2:ℝ) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j from by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
              rw [pow_succ]; ring]
        have hgs : ∑ j ∈ Finset.range S, (1/2:ℝ)^j ≤ 2 := hgs' S
        linarith
      have h2 := mul_le_mul_of_nonneg_left hWle (Real.sqrt_nonneg c₀)
      nlinarith [hfirst, hlast, h2, hgeomsmall, Real.sqrt_nonneg c₀]
    have hsq : (∑ j ∈ Finset.range (S+1), uu j) ^ 2 ≤ 100 * (c₀ + 1) * T^2 := by
      have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (S+1), uu j :=
        Finset.sum_nonneg (fun j hj => (huu_pos j hj).le)
      have h1 : (∑ j ∈ Finset.range (S+1), uu j) ^ 2 ≤ (Real.sqrt c₀ * (5*T) + 2)^2 :=
        pow_le_pow_left₀ hnn hsumuu 2
      have hsq0 : Real.sqrt c₀ ≤ c₀ + 1 := by
        nlinarith [sq_nonneg (Real.sqrt c₀ - 1), Real.sqrt_nonneg c₀, Real.sq_sqrt hc₀pos.le]
      nlinarith [h1, hsq0, hT1, Real.sq_sqrt hc₀pos.le, Real.sqrt_nonneg c₀, sq_nonneg T,
        sq_nonneg (Real.sqrt c₀ * (5*T) + 2)]
    exact hsq

/-! ## The Fatou step: `MemLp f 1` is not needed

Bourgain's Lemma 4.13 only assumes `f ∈ L²`, while the band-sum identity `bandSum_windowed`
needs `f ∈ L¹`.  The gap is closed by dominated convergence: truncating `f` to
`f_n = f · 1_{‖f‖ ≤ n, |·| ≤ n} ∈ L¹ ∩ L²` and applying Fatou's lemma to the pointwise inequality
`sup_j |T_j f(x)| ≤ liminf_n sup_j |T_j f_n(x)|`.  Everything below is stated with the liminf in
`ℝ≥0∞`, where the boundedness side conditions of `Filter.liminf_le_liminf` are automatic. -/

namespace BourgainFatou

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

noncomputable section

/-- The `L¹`-`L²` truncation of `f` at level `n`. -/
def trunc (f : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fun y => if ‖f y‖ ≤ n ∧ |y| ≤ n then f y else 0

lemma trunc_measurable {f : ℝ → ℂ} (hf : Measurable f) (n : ℕ) : Measurable (trunc f n) := by
  have hs : MeasurableSet {y : ℝ | ‖f y‖ ≤ (n:ℝ) ∧ |y| ≤ (n:ℝ)} :=
    (measurableSet_le hf.norm measurable_const).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  exact Measurable.ite hs hf measurable_const

lemma norm_trunc_le (f : ℝ → ℂ) (n : ℕ) (y : ℝ) : ‖trunc f n y‖ ≤ ‖f y‖ := by
  rw [trunc]
  split_ifs with h
  · exact le_rfl
  · rw [norm_zero]; positivity

lemma trunc_tendsto (f : ℝ → ℂ) (y : ℝ) :
    Tendsto (fun n : ℕ => trunc f n y) atTop (𝓝 (f y)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖f y‖⌉₊, eventually_ge_atTop ⌈|y|⌉₊] with n h1 h2
  rw [trunc, if_pos]
  refine ⟨?_, ?_⟩
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast h2)

/-- **Band-integral measurability in `x`.**  For a jointly measurable kernel `K` and a measurable
`g` whose band integrals exist for every `x`, the map `x ↦ ∫ y, g y * K (x, y)` is measurable. -/
theorem measurable_parametric_integral {K : ℝ × ℝ → ℂ} (hK : Measurable K) {g : ℝ → ℂ}
    (hg : Measurable g)
    (hint : ∀ x : ℝ, Integrable (fun y : ℝ => g y * K (x, y)) volume) :
    Measurable (fun x : ℝ => ∫ y : ℝ, g y * K (x, y)) := by
  have hmeas : ∀ n : ℕ, Measurable (fun x : ℝ => ∫ y : ℝ, trunc g n y * K (x, y)) := by
    intro n
    have h1 : Measurable (Function.uncurry (fun x y : ℝ => trunc g n y * K (x, y))) := by
      show Measurable (fun p : ℝ × ℝ => trunc g n p.2 * K p)
      exact ((trunc_measurable hg n).comp measurable_snd).mul hK
    exact (StronglyMeasurable.integral_prod_right h1.stronglyMeasurable).measurable
  have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ => ∫ y : ℝ, trunc g n y * K (x, y)) atTop
      (𝓝 (∫ y : ℝ, g y * K (x, y))) := by
    intro x
    refine tendsto_integral_of_dominated_convergence (fun y : ℝ => ‖g y‖ * ‖K (x, y)‖)
      (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact ((trunc_measurable hg n).mul
        (hK.comp (by fun_prop : Measurable (fun y : ℝ => (x, y))))).aestronglyMeasurable
    · have h1 : Integrable (fun y : ℝ => ‖g y * K (x, y)‖) volume := (hint x).norm
      refine h1.congr ?_
      filter_upwards with y
      rw [norm_mul]
    · filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_trunc_le g n y) (norm_nonneg _)
    · filter_upwards with y
      exact (trunc_tendsto g y).mul_const (K (x, y))
  exact measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr hlim)

lemma BoundaryLayer.enorm_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by simp [enorm_eq_nnnorm]

/-- **The `AEMeasurable` input for `lintegral_liminf_le'`.** -/
theorem measurable_trunc_sup_rpow {f : ℝ → ℂ} (hf : Measurable f) (b : ℕ → ℝ → ℂ)
    (hb : ∀ j, Measurable (b j))
    (hint : ∀ (j : ℕ) (x : ℝ), Integrable (fun y : ℝ => f y * b j (x - y)) volume) (n : ℕ) :
    Measurable (fun x : ℝ => (⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ) ^ (2:ℝ)) := by
  have hslice : ∀ j : ℕ, Measurable (fun x : ℝ => ∫ y : ℝ, trunc f n y * b j (x - y)) := by
    intro j
    refine measurable_parametric_integral
      ((hb j).comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 - p.2)))
      (trunc_measurable hf n) (fun x => ?_)
    have hs : MeasurableSet {y : ℝ | ‖f y‖ ≤ (n:ℝ) ∧ |y| ≤ (n:ℝ)} :=
      (measurableSet_le hf.norm measurable_const).inter
        (measurableSet_le continuous_abs.measurable measurable_const)
    refine Integrable.congr ((hint j x).indicator hs) ?_
    filter_upwards with y
    simp only [trunc, Set.indicator_apply, Function.comp_apply, Set.mem_setOf_eq]
    split_ifs with h <;> ring_nf
  have hsup : Measurable (fun x : ℝ => ⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ) :=
    Measurable.iSup fun j => by
      simpa only [BoundaryLayer.enorm_eq_ofReal_norm'] using (hslice j).norm.ennreal_ofReal
  have h2 : Measurable (fun x : ℝ =>
      (⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ)
        * (⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ)) := hsup.mul hsup
  simpa only [ENNReal.rpow_two, pow_two] using h2

/-- `(liminf u)^2 ≤ liminf (u^2)` in `ℝ≥0∞`. -/
theorem liminf_sq_le_liminf_sq {α : Type*} {l : Filter α} {u : α → ENNReal} :
    (Filter.liminf u l) ^ 2 ≤ Filter.liminf (fun a => (u a) ^ 2) l := by
  simp only [pow_two]
  simp_rw [Filter.liminf_eq_iSup_iInf]
  simp_rw [iSup_subtype']
  simp_rw [ENNReal.mul_iSup, ENNReal.iSup_mul]
  refine iSup_le fun s => ?_
  refine iSup_le fun t => ?_
  refine le_trans (le_iInf₂ fun a ha => mul_le_mul' (iInf₂_le a ha.2) (iInf₂_le a ha.1))
    (le_iSup (fun w : {w : Set α // w ∈ l} => ⨅ a ∈ w.1, u a * u a)
      ⟨s.1 ∩ t.1, l.inter_mem s.2 t.2⟩)

/-- Per-kernel comparison: `|T f(x)|` is dominated by the `liminf` over truncations. -/
theorem enorm_integral_le_liminf_trunc {f : ℝ → ℂ} (hf : Measurable f) {b : ℝ → ℂ}
    (hb : Measurable b) (x : ℝ) :
    ‖∫ y : ℝ, f y * b (x - y)‖ₑ
      ≤ Filter.liminf (fun n : ℕ => ‖∫ y : ℝ, trunc f n y * b (x - y)‖ₑ) Filter.atTop := by
  by_cases hInt : Integrable (fun y : ℝ => f y * b (x - y)) volume
  · have hFm : ∀ n : ℕ, AEStronglyMeasurable (fun y : ℝ => trunc f n y * b (x - y)) volume :=
      fun n => ((trunc_measurable hf n).mul
        (hb.comp (by fun_prop : Measurable (fun y : ℝ => x - y)))).aestronglyMeasurable
    have hbound : Integrable (fun y : ℝ => ‖f y‖ * ‖b (x - y)‖) volume := by
      have h1 : Integrable (fun y : ℝ => ‖f y * b (x - y)‖) volume := hInt.norm
      refine h1.congr ?_
      filter_upwards with y
      rw [norm_mul]
    have hbnd : ∀ n : ℕ, ∀ᵐ y : ℝ ∂volume,
        ‖trunc f n y * b (x - y)‖ ≤ ‖f y‖ * ‖b (x - y)‖ := by
      intro n
      filter_upwards with y
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_trunc_le f n y) (norm_nonneg _)
    have hlim : ∀ᵐ y : ℝ ∂volume,
        Tendsto (fun n : ℕ => trunc f n y * b (x - y)) atTop (𝓝 (f y * b (x - y))) := by
      filter_upwards with y
      exact (trunc_tendsto f y).mul_const (b (x - y))
    have htend := tendsto_integral_of_dominated_convergence
      (fun y : ℝ => ‖f y‖ * ‖b (x - y)‖) hFm hbound hbnd hlim
    have hnorm : Tendsto (fun n : ℕ => ‖∫ y : ℝ, trunc f n y * b (x - y)‖) atTop
        (𝓝 ‖∫ y : ℝ, f y * b (x - y)‖) := htend.norm
    have h2 : Tendsto (fun n : ℕ => ‖∫ y : ℝ, trunc f n y * b (x - y)‖ₑ) atTop
        (𝓝 ‖∫ y : ℝ, f y * b (x - y)‖ₑ) := by
      have h1 := (ENNReal.continuous_ofReal.tendsto ‖∫ y : ℝ, f y * b (x - y)‖).comp hnorm
      simpa only [BoundaryLayer.enorm_eq_ofReal_norm', Function.comp_def] using h1
    rw [h2.liminf_eq]
  · rw [integral_undef hInt, enorm_zero]
    exact bot_le

/-- The `sup_j` upgrade of the per-kernel comparison. -/
theorem sup_enorm_integral_le_liminf {f : ℝ → ℂ} (hf : Measurable f) (b : ℕ → ℝ → ℂ)
    (hb : ∀ j, Measurable (b j)) (x : ℝ) :
    (⨆ j : ℕ, ‖∫ y : ℝ, f y * b j (x - y)‖ₑ)
      ≤ Filter.liminf (fun n : ℕ => ⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ)
          Filter.atTop := by
  refine iSup_le fun j => ?_
  refine le_trans (enorm_integral_le_liminf_trunc hf (hb j) x) ?_
  refine Filter.liminf_le_liminf (Eventually.of_forall (fun n => ?_))
  exact le_iSup (fun j : ℕ => ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ) j

/-- **The Fatou integration step**: pointwise squaring + `lintegral_liminf_le'`. -/
theorem lintegral_sup_enorm_le_liminf {f : ℝ → ℂ} (hf : Measurable f) (b : ℕ → ℝ → ℂ)
    (hb : ∀ j, Measurable (b j))
    (hint : ∀ (j : ℕ) (x : ℝ), Integrable (fun y : ℝ => f y * b j (x - y)) volume) :
    ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * b j (x - y)‖ₑ) ^ (2:ℝ)
      ≤ Filter.liminf (fun n : ℕ =>
          ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ) ^ (2:ℝ)) Filter.atTop := by
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖∫ y : ℝ, f y * b j (x - y)‖ₑ) ^ (2:ℝ)
      ≤ Filter.liminf (fun n : ℕ =>
          (⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ) ^ (2:ℝ)) Filter.atTop := by
    intro x
    refine le_trans (ENNReal.rpow_le_rpow (sup_enorm_integral_le_liminf hf b hb x)
      (by norm_num : (0:ℝ) ≤ 2)) ?_
    simpa only [ENNReal.rpow_two] using
      (liminf_sq_le_liminf_sq (l := Filter.atTop)
        (u := fun n : ℕ => ⨆ j : ℕ, ‖∫ y : ℝ, trunc f n y * b j (x - y)‖ₑ))
  refine le_trans (lintegral_mono hpt) ?_
  exact lintegral_liminf_le'
    (fun n => (measurable_trunc_sup_rpow hf b hb hint n).aemeasurable)

end

end BourgainFatou


/-! ## The top-cardinality obligation of the chain construction

The chain decomposition of a net `σ (S-1)` needs the *difference* family `j ↦ a j - a (σ (S-1) j)` to be no larger than the net itself.  If the family is
`τ`-separated in `ℓ²` and `σ (S-1)` resolves it at radius `2D·2^{-(S-1)}`, this holds because the
difference map is constant on the fibres of `σ (S-1)`. -/

namespace BourgainCard

open Finset

/-- **Top-cardinality obligation.** -/
theorem card_diff_image_le_of_separated {K J : ℕ} (a : Fin (J+1) → Fin K → ℂ)
    (σ : ℕ → Fin (J+1) → Fin (J+1)) {D τ : ℝ} (hD : 0 < D) (hτ : 0 < τ) (S : ℕ)
    (hnet : ∀ i, ∑ k : Fin K, ‖a i k - a (σ (S-1) i) k‖^2 ≤ (2*D*(1/2:ℝ)^(S-1))^2)
    (hsep : ∀ i j : Fin (J+1), a i ≠ a j → τ ≤ Real.sqrt (∑ k : Fin K, ‖a i k - a j k‖^2))
    (hS : 8*D*(1/2:ℝ)^(S-1) < τ) :
    (Finset.univ.image (fun j : Fin (J+1) => a j - a (σ (S-1) j))).card
      ≤ (Finset.univ.image (σ (S-1))).card := by
  classical
  set c : ℝ := (1/2:ℝ)^(S-1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set d : Fin (J+1) → (Fin K → ℂ) := fun i => a i - a (σ (S-1) i) with hd
  have hd_apply : ∀ i k, d i k = a i k - a (σ (S-1) i) k := fun i k => rfl
  have hfib : ∀ i j : Fin (J+1), σ (S-1) i = σ (S-1) j → d i = d j := by
    intro i j hij
    have hsum : (∑ k : Fin K, ‖a i k - a j k‖^2) = ∑ k : Fin K, ‖d i k - d j k‖^2 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h1 : a (σ (S-1) j) k = a (σ (S-1) i) k := by rw [hij]
      rw [hd_apply, hd_apply, h1]
      congr 1
      ring_nf
    have hterm : ∀ k : Fin K, ‖d i k - d j k‖^2 ≤ 2*‖d i k‖^2 + 2*‖d j k‖^2 := by
      intro k
      nlinarith [norm_nonneg (d i k), norm_nonneg (d j k), norm_nonneg (d i k - d j k),
        norm_sub_le (d i k) (d j k), sq_nonneg (‖d i k‖ - ‖d j k‖)]
    have hstep : ∑ k : Fin K, ‖d i k - d j k‖^2 ≤ 2 * ∑ k : Fin K, ‖d i k‖^2
        + 2 * ∑ k : Fin K, ‖d j k‖^2 := by
      calc ∑ k : Fin K, ‖d i k - d j k‖^2
          ≤ ∑ k : Fin K, (2*‖d i k‖^2 + 2*‖d j k‖^2) := Finset.sum_le_sum (fun k _ => hterm k)
        _ = 2 * ∑ k : Fin K, ‖d i k‖^2 + 2 * ∑ k : Fin K, ‖d j k‖^2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hb : ∑ k : Fin K, ‖d i k‖^2 ≤ (2*D*c)^2 := by
      simpa only [hd, Pi.sub_apply] using hnet i
    have hb' : ∑ k : Fin K, ‖d j k‖^2 ≤ (2*D*c)^2 := by
      simpa only [hd, Pi.sub_apply] using hnet j
    have hmain : ∑ k : Fin K, ‖a i k - a j k‖^2 < τ^2 := by
      rw [hsum]
      have hp : (2*D*c)^2 = 4*D^2*c^2 := by ring
      rw [hp] at hb hb'
      have hbound : ∑ k : Fin K, ‖d i k - d j k‖^2 ≤ 16*D^2*c^2 := by linarith
      have hsq : (8*D*c)^2 < τ^2 := by
        have hpos : 0 < 8*D*c := by positivity
        nlinarith [hS, hpos]
      have h4 : 16*D^2*c^2 < (8*D*c)^2 := by
        have hpos : 0 < D^2*c^2 := by positivity
        nlinarith
      linarith
    by_contra hne
    have haij : a i ≠ a j := fun h => hne (by
      simp only [hd, h, hij])
    have hle := hsep i j haij
    have hlt : Real.sqrt (∑ k : Fin K, ‖a i k - a j k‖^2) < τ := by
      rwa [Real.sqrt_lt' hτ]
    linarith
  set g : Fin (J+1) → (Fin K → ℂ) :=
    fun r => if h : ∃ i, σ (S-1) i = r then d h.choose else 0 with hg
  have hdg : ∀ j, g (σ (S-1) j) = d j := by
    intro j
    have hex : ∃ i, σ (S-1) i = σ (S-1) j := ⟨j, rfl⟩
    simp only [hg]
    rw [dif_pos hex]
    exact hfib _ _ (Exists.choose_spec hex)
  calc (Finset.univ.image (fun j : Fin (J+1) => d j)).card
      = (Finset.univ.image (fun j : Fin (J+1) => g (σ (S-1) j))).card := by
        congr 1
        exact Finset.image_congr (fun j _ => (hdg j).symm)
    _ = ((Finset.univ.image (σ (S-1))).image g).card := by
        congr 1
        rw [Finset.image_image]
        rfl
    _ ≤ (Finset.univ.image (σ (S-1))).card := Finset.card_image_le


end BourgainCard

/-! ## The remaining deep input, stated precisely

The whole of the target reduces (see `BOURGAIN_SMOOTH_WINDOW_ROADMAP.md`, session-3 update) to the
following estimate of Bourgain (Lemma 3.33 of *Pointwise ergodic theorems for arithmetic sets*,
first part of Lemma 2.3/2.2 in Krause, arXiv:1402.1804).  It is the *only* statement in the
project for which no proof route without martingale variation theory (Lépingle / Doob
oscillation / Brownian transfer) is known, and it is sharp.

Note the convention: the `r`-entropy of the curve is declared to be `0` as soon as the curve is
contained in a single `ℓ²`-ball of radius `r` (Bourgain: "we set `M_λ = 0` if `diam A < λ`").
Without this convention the integral `∫_0^∞ min(√K, M_r^{1/2}) dr` diverges (it would be `1` on
`(diam, ∞)`), and the statement below would be false. -/

/-- The pointwise curve of windowed values attached to a `K`-tuple of functions: the set of
`((f_1 * Ψ_t)(x), …, (f_K * Ψ_t)(x))`, `t > 0`, where `Ψ_t(z) = t⁻¹ Ψ(z/t)` is the `L¹`-normalised
dilation of the window `Ψ` (so the smoothing of the `k`-th function is
`∫ y, f_k y · (t⁻¹ • Ψ((x-y)/t))`).  In the assembly `Ψ` is `\hatφ = ∫ u, φ u · e^{-I · u}`, which
is *complex*-valued, hence the complex codomain. -/
noncomputable def winCurve (K : ℕ) (Ψ : ℝ → ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    Set (Fin K → ℂ) :=
  Set.range (fun t : {t : ℝ // 0 < t} =>
    fun k => ∫ y : ℝ, f k y * ((t:ℝ)⁻¹ • Ψ ((x - y) / (t:ℝ))))

/-- A finite set `S` of centres covers the pointwise curve at radius `r` in the `ℓ²` sense. -/
def winCovers (K : ℕ) (Ψ : ℝ → ℂ) (f : Fin K → ℝ → ℂ) (x r : ℝ)
    (S : Finset (Fin K → ℂ)) : Prop :=
  ∀ a ∈ winCurve K Ψ f x, ∃ s ∈ S, ∑ k : Fin K, ‖a k - s k‖ ^ 2 ≤ r ^ 2

/-- A single `ℓ²`-ball of radius `r` covers the pointwise curve. -/
def winCovered (K : ℕ) (Ψ : ℝ → ℂ) (f : Fin K → ℝ → ℂ) (x r : ℝ) : Prop :=
  ∃ s : Fin K → ℂ, ∀ a ∈ winCurve K Ψ f x, ∑ k : Fin K, ‖a k - s k‖ ^ 2 ≤ r ^ 2

/-- Covering the curve at radius `r` implies covering it at any larger positive radius. -/
theorem winCovers_mono {K : ℕ} {Ψ : ℝ → ℂ} {f : Fin K → ℝ → ℂ} {x r r' : ℝ}
    (S : Finset (Fin K → ℂ)) (hr : 0 ≤ r) (h : r ≤ r')
    (hS : winCovers K Ψ f x r S) : winCovers K Ψ f x r' S := by
  intro a ha
  obtain ⟨s, hsS, hs⟩ := hS a ha
  exact ⟨s, hsS, le_trans hs (pow_le_pow_left₀ hr h 2)⟩

theorem winCovered_mono {K : ℕ} {Ψ : ℝ → ℂ} {f : Fin K → ℝ → ℂ} {x r r' : ℝ}
    (hr : 0 ≤ r) (h : r ≤ r') (hc : winCovered K Ψ f x r) : winCovered K Ψ f x r' := by
  obtain ⟨s, hs⟩ := hc
  exact ⟨s, fun a ha => le_trans (hs a ha) (pow_le_pow_left₀ hr h 2)⟩

/-- `ℓ²`-covering number of the pointwise curve at radius `r`, with Bourgain's convention that it
is `0` once a single `ℓ²`-ball of radius `r` covers the curve (without this convention the
integral below would be `+∞`). -/
noncomputable def winEntropy (K : ℕ) (Ψ : ℝ → ℂ) (f : Fin K → ℝ → ℂ) (x r : ℝ) : ℝ≥0∞ := by
  classical
  exact if winCovered K Ψ f x r then 0
    else ⨅ (S : {S : Finset (Fin K → ℂ) // winCovers K Ψ f x r S}),
      ((S : Finset (Fin K → ℂ)).card : ℝ≥0∞)

/-- The entropy numbers are non-increasing in the radius (for positive radii). -/
theorem winEntropy_antitone (K : ℕ) (Ψ : ℝ → ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {r r' : ℝ}
    (hr : 0 < r) (h : r ≤ r') : winEntropy K Ψ f x r' ≤ winEntropy K Ψ f x r := by
  unfold winEntropy
  by_cases h1 : winCovered K Ψ f x r
  · rw [if_pos h1, if_pos (winCovered_mono hr.le h h1)]
  · rw [if_neg h1]
    by_cases h2 : winCovered K Ψ f x r'
    · rw [if_pos h2]; exact bot_le
    · rw [if_neg h2]
      refine le_iInf fun S => ?_
      exact iInf_le_of_le ⟨S.1, winCovers_mono S.1 hr.le h S.2⟩ le_rfl

/-- **A covering set of centres whose cardinality realises the entropy number.**  If the entropy
number is finite, there is a covering set of centres of cardinality at most `winEntropy + 1`: in
the non-degenerate case the infimum defining `winEntropy` is over a nonempty set of natural
numbers, hence attained by the well-ordering of `ℕ`. -/
theorem exists_cover_of_winEntropy {K : ℕ} {Ψ : ℝ → ℂ} {f : Fin K → ℝ → ℂ} {x r : ℝ}
    (h : winEntropy K Ψ f x r ≠ ⊤) :
    ∃ S : Finset (Fin K → ℂ), winCovers K Ψ f x r S ∧
      (S.card : ℝ≥0∞) ≤ winEntropy K Ψ f x r + 1 := by
  unfold winEntropy at h ⊢
  by_cases hc : winCovered K Ψ f x r
  · rw [if_pos hc]
    obtain ⟨s, hs⟩ := hc
    exact ⟨{s}, fun a ha => ⟨s, Finset.mem_singleton_self s, hs a ha⟩, by simp⟩
  · rw [if_neg hc] at h
    rw [if_neg hc]
    haveI hne : Nonempty {S : Finset (Fin K → ℂ) // winCovers K Ψ f x r S} := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      exact h (iInf_of_empty _)
    have hne' : ({n : ℕ | ∃ S : Finset (Fin K → ℂ), winCovers K Ψ f x r S ∧ S.card = n}).Nonempty :=
      hne.elim fun S => ⟨S.1.card, S.1, S.2, rfl⟩
    obtain ⟨S₀, hS₀c, hS₀card⟩ := Nat.sInf_mem hne'
    refine ⟨S₀, hS₀c, ?_⟩
    have hle : ((S₀.card : ℕ) : ℝ≥0∞)
        ≤ ⨅ (S : {S : Finset (Fin K → ℂ) // winCovers K Ψ f x r S}),
            ((S : Finset (Fin K → ℂ)).card : ℝ≥0∞) := by
      refine le_iInf fun S => ?_
      have := Nat.sInf_le (show S.1.card ∈ {n : ℕ | ∃ T : Finset (Fin K → ℂ),
          winCovers K Ψ f x r T ∧ T.card = n} from ⟨S.1, S.2, rfl⟩)
      rw [hS₀card]
      exact_mod_cast this
    calc ((S₀.card : ℕ) : ℝ≥0∞)
        ≤ ⨅ (S : {S : Finset (Fin K → ℂ) // winCovers K Ψ f x r S}),
            ((S : Finset (Fin K → ℂ)).card : ℝ≥0∞) := hle
      _ ≤ _ + 1 := le_add_of_nonneg_right bot_le

/-- Change-of-variables identity relating the oscillatory integral defining a window kernel to an
integral against `M` at the rescaled argument (`θ = -2π ξ`). -/
theorem fourierInv_change_of_variables (M : ℝ → ℂ) (t : ℝ) :
    (∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * (t : ℂ) * (θ : ℂ))))
      = 2 * Real.pi *
        ∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * ξ * t) : ℂ) * Complex.I) *
          M (-(2 * Real.pi) * ξ) := by
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h := Measure.integral_comp_mul_left
    (fun ξ : ℝ => Complex.exp ((↑(2 * Real.pi * ξ * t) : ℂ) * Complex.I) *
      M (-(2 * Real.pi) * ξ))
    (-(1/(2 * Real.pi)))
  rw [show (-(1/(2*Real.pi)) : ℝ)⁻¹ = -(2*Real.pi) by field_simp] at h
  rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), Complex.real_smul] at h
  rw [show (↑(2*Real.pi) : ℂ) = 2 * (↑Real.pi : ℂ) by push_cast; ring] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with θ
  have h1 : (2 * Real.pi * ((-(1/(2*Real.pi))) * θ) * t : ℝ) = -(θ * t) := by field_simp
  have h2 : (-(2 * Real.pi) * ((-(1/(2*Real.pi))) * θ) : ℝ) = θ := by field_simp
  rw [h1, h2, mul_comm (Complex.exp _) (M θ)]
  congr 1
  congr 1
  push_cast
  ring

/-! ## Step 1 of the assembly: the band sum is a sum of Fourier multipliers

These lemmas identify the `y`-integral of the target with a sum of Fourier multiplier operators,
for `f ∈ L¹ ∩ L²` (the extension to `f ∈ L²` is done later by a Fatou argument).  They use
`Commons.Analysis.Fourier.convolution_kernel_fubini`. -/

namespace BandDecomp

open scoped ContDiff

/-- The target's smoothness hypothesis (`C^n` for every `n`) is `C^∞`.  Note that `ContDiff ℝ ⊤`
in this Mathlib is *analytic* (and hence, under compact support, forces `φ ≡ 0`), so this
conversion is what makes the `BandDecomp`/`BourgainAssembly` lemmas applicable to the target. -/
lemma contDiff_infty_of_forall_nat {φ : ℝ → ℝ} (h : ∀ n : ℕ, ContDiff ℝ n φ) : ContDiff ℝ ∞ φ := by
  rw [contDiff_iff_forall_nat_le]
  intro m _
  exact h m


/-- A bounded function supported in a bounded interval is in every `Lᵖ`. -/
theorem memLp_of_support_subset_Icc (g : ℝ → ℂ) (hg : Measurable g) {C a b : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ x, ‖g x‖ ≤ C) (hsupp : ∀ x, x ∉ Set.Icc a b → g x = 0) (p : ℝ≥0∞) :
    MemLp g p (volume : Measure ℝ) := by
  have hfin : volume (Set.Icc a b) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) := ⟨by
    rwa [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]⟩
  have hmem : MemLp g p (volume.restrict (Set.Icc a b)) :=
    MemLp.of_bound hg.aestronglyMeasurable C (ae_of_all _ hbd)
  have hind : MemLp ((Set.Icc a b).indicator g) p (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict (μ := (volume : Measure ℝ)) measurableSet_Icc).mpr hmem
  rwa [show (Set.Icc a b).indicator g = g from funext (fun x => by
    by_cases hx : x ∈ Set.Icc a b
    · simp [Set.indicator_of_mem hx]
    · simp only [Set.indicator_apply, hx, if_false]; exact (hsupp x hx).symm)] at hind

/-- The window symbol of a band: `θ ↦ 1_{(λ-h,λ+h]}(θ) φ((θ-λ)/h)`. -/
noncomputable def bandSymbol (φ : ℝ → ℝ) (lam h : ℝ) : ℝ → ℂ :=
  (Set.Ioc (lam - h) (lam + h)).indicator (fun th => (φ ((th - lam) / h) : ℂ))

/-- The (complex) window integral over one band, as a function of the point `x` and the
integration variable `y`. -/
noncomputable def bandTerm (φ : ℝ → ℝ) (lam h x y : ℝ) : ℂ :=
  ∫ th in (lam - h)..(lam + h),
    (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))

theorem bandSymbol_bdd (φ : ℝ → ℝ) (hφ : ∀ x, ‖φ x‖ ≤ 1) (lam h th : ℝ) :
    ‖bandSymbol φ lam h th‖ ≤ 1 := by
  rw [bandSymbol]
  by_cases hmem : th ∈ Set.Ioc (lam - h) (lam + h)
  · rw [Set.indicator_apply, if_pos hmem]; simpa using hφ ((th - lam)/h)
  · rw [Set.indicator_apply, if_neg hmem]; simp

theorem bandSymbol_supp (φ : ℝ → ℝ) (hsupp : ∀ x, 1 ≤ |x| → φ x = 0) {lam h : ℝ} (hh : 0 < h)
    {th : ℝ} (hout : th ∉ Set.Icc (lam - h) (lam + h)) : bandSymbol φ lam h th = 0 := by
  rw [bandSymbol, Set.indicator_apply, if_neg]
  intro hmem
  rw [Set.mem_Ioc] at hmem
  exact hout ⟨le_of_lt hmem.1, hmem.2⟩

theorem bandSymbol_measurable (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (lam h : ℝ) :
    Measurable (bandSymbol φ lam h) := by
  rw [bandSymbol]
  have hcont : Continuous (fun th : ℝ => ((φ ((th - lam) / h) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous.comp (by continuity))
  exact Measurable.indicator hcont.measurable measurableSet_Ioc

theorem bandSymbol_memLp (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hbd : ∀ x, ‖φ x‖ ≤ 1)
    (hsupp : ∀ x, 1 ≤ |x| → φ x = 0) {lam h : ℝ} (hh : 0 < h) (p : ℝ≥0∞) :
    MemLp (bandSymbol φ lam h) p (volume : Measure ℝ) :=
  memLp_of_support_subset_Icc _ (bandSymbol_measurable φ hφ lam h) (by norm_num : (0:ℝ) ≤ 1)
    (bandSymbol_bdd φ hbd lam h) (fun x hx => bandSymbol_supp φ hsupp hh hx) p

/-- The interval integral of the target equals the full-line integral against the band symbol. -/
theorem integral_bandSymbol (φ : ℝ → ℝ) (lam h tau : ℝ) (hh : 0 ≤ h) :
    (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (tau : ℂ) * (th : ℂ))))
      = ∫ th, bandSymbol φ lam h th * Complex.exp (-(Complex.I * (tau : ℂ) * (th : ℂ))) := by
  rw [intervalIntegral.integral_of_le (by linarith : lam - h ≤ lam + h)]
  rw [← MeasureTheory.integral_indicator (μ := volume) measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with th
  simp only [bandSymbol, Set.indicator_apply]
  split_ifs <;> simp

/-- **The `k`-th band term is a Fourier multiplier operator.**  For `f ∈ L¹ ∩ L²` and a window
`φ` vanishing off `[-1,1]`, the `y`-integral over a single band equals `2π` times the inverse
Fourier transform of the band symbol times the Fourier transform of `f`. -/
theorem band_term_eq_multiplier (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hbd : ∀ x, ‖φ x‖ ≤ 1)
    (hsupp : ∀ x, 1 ≤ |x| → φ x = 0) {lam h : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    (∫ y, f y * bandTerm φ lam h x y)
      = 2 * Real.pi * FourierTransformInv.fourierInv
          (fun ξ => bandSymbol φ lam h (-(2 * Real.pi) * ξ) * FourierTransform.fourier f ξ) x := by
  have key : bandTerm φ lam h x = fun y : ℝ => (∫ th,
      bandSymbol φ lam h th * Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))) := by
    funext y
    exact integral_bandSymbol φ lam h _ hh.le
  rw [key]
  exact convolution_kernel_fubini (bandSymbol φ lam h) f
    (bandSymbol_measurable φ hφ lam h) (bandSymbol_memLp φ hφ hbd hsupp hh 1)
    (bandSymbol_memLp φ hφ hbd hsupp hh 2) (bandSymbol_memLp φ hφ hbd hsupp hh ⊤) hf1 hf2 x


/-- **The band sum of the target is a sum of multiplier operators** (for `f ∈ L¹ ∩ L²`). -/
theorem band_sum_eq_multiplier (K : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hbd : ∀ x, ‖φ x‖ ≤ 1)
    (hsupp : ∀ x, 1 ≤ |x| → φ x = 0) (lam : Fin K → ℝ) {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    (∫ y, f y * (∑ k : Fin K, bandTerm φ (lam k) h x y))
      = ∑ k : Fin K, 2 * Real.pi * FourierTransformInv.fourierInv
          (fun ξ => bandSymbol φ (lam k) h (-(2 * Real.pi) * ξ) * FourierTransform.fourier f ξ) x := by
  have hband : ∀ (k : Fin K) (y : ℝ), ‖bandTerm φ (lam k) h x y‖ ≤ 2 * h := by
    intro k y
    have h1 : ∀ th : ℝ, ‖(φ ((th - lam k) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))‖ ≤ 1 := by
      intro th
      rw [norm_mul, show Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))
          = Complex.exp (((-(x - y) * th : ℝ) : ℂ) * Complex.I) by
            congr 1; push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      simpa using hbd ((th - lam k) / h)
    have hc : Continuous fun th : ℝ => (φ ((th - lam k) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ))) := by fun_prop
    calc ‖bandTerm φ (lam k) h x y‖
        ≤ ∫ th in (lam k - h)..(lam k + h), ‖(φ ((th - lam k) / h) : ℂ) *
            Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ _th in (lam k - h)..(lam k + h), (1 : ℝ) := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (hc.norm.intervalIntegrable _ _) intervalIntegrable_const
          intro th _
          exact h1 th
      _ = 2 * h := by rw [intervalIntegral.integral_const]; simp; ring
  have hcont : ∀ k : Fin K, Continuous (fun y : ℝ => bandTerm φ (lam k) h x y) := by
    intro k
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := (volume : Measure ℝ))
      (f := fun y th : ℝ => (φ ((th - lam k) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))) (by fun_prop)
      (lam k - h) (lam k + h)
    simpa [bandTerm] using h
  have hint : ∀ k : Fin K, Integrable (fun y : ℝ => f y * bandTerm φ (lam k) h x y)
      (volume : Measure ℝ) := by
    intro k
    refine Integrable.mono' (((memLp_one_iff_integrable.mp hf1).norm).const_mul (2 * h))
      (hf1.aestronglyMeasurable.mul (hcont k).aestronglyMeasurable) ?_
    filter_upwards with y
    rw [norm_mul]
    calc ‖f y‖ * ‖bandTerm φ (lam k) h x y‖ ≤ ‖f y‖ * (2 * h) :=
          mul_le_mul_of_nonneg_left (hband k y) (norm_nonneg _)
      _ = 2 * h * ‖f y‖ := by ring
  have hpt : (fun y : ℝ => f y * (∑ k : Fin K, bandTerm φ (lam k) h x y))
      = fun y : ℝ => ∑ k : Fin K, f y * bandTerm φ (lam k) h x y := by
    funext y
    rw [Finset.mul_sum]
  rw [hpt, integral_finsetSum _ (fun k _ => hint k)]
  exact Finset.sum_congr rfl (fun k _ => band_term_eq_multiplier φ hφ hbd hsupp hh hf1 hf2 x)

/-- The target's window integral over one band, in closed form: substituting `θ = λ + h u` and
using that `φ` vanishes off `[-1,1]`,
`∫_{λ-h}^{λ+h} φ((θ-λ)/h) e^{-I z θ} dθ = h · \hatφ(h z) · e^{-I λ z}` where
`\hatφ(s) := ∫ u, φ u · e^{-I s u}`. -/
theorem bandTerm_apply (φ : ℝ → ℝ) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {lam h z : ℝ} (hh : 0 < h) :
    (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ))))
      = h * (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) := by
  -- the substitution `θ = λ + h u`
  have hsub : h * (∫ u in (-1 : ℝ)..1, (φ ((lam + h * u - lam) / h) : ℂ) *
        Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ))))
      = (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ)))) := by
    rw [show (lam - h) = lam + h * (-1) by ring, show (lam + h) = lam + h * 1 by ring]
    rw [intervalIntegral.integral_comp_add_mul (f := fun th : ℝ => (φ ((th - lam) / h) : ℂ) *
      Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ))))
      (a := (-1 : ℝ)) (b := 1) (c := h) (d := lam) (ne_of_gt hh)]
    rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
      mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hh), one_mul]
  -- the pointwise identification of the integrand
  have hsimp : (∫ u in (-1 : ℝ)..1, (φ ((lam + h * u - lam) / h) : ℂ) *
        Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ))))
      = ∫ u in (-1 : ℝ)..1, Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
        ((φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) := by
    apply intervalIntegral.integral_congr
    intro u _
    show (φ ((lam + h * u - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
        ((φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
    have h1 : (lam + h * u - lam) / h = u := by field_simp; ring
    rw [show -(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ))
        = -(Complex.I * (lam : ℂ) * (z : ℂ)) + -(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)) by
      push_cast; ring, Complex.exp_add, h1]
    ring
  -- `φ` vanishes off `[-1,1]`, so the interval integral is a full-line integral
  have hzero : ∀ u : ℝ, u ∉ Set.Icc (-1 : ℝ) 1 →
      (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))) = 0 := by
    intro u hu
    have h1 : 1 ≤ |u| := by
      rcases (not_and_or.mp hu) with h | h
      · rw [abs_of_neg (by linarith [not_le.mp h])]; linarith [not_le.mp h]
      · rw [abs_of_pos (by linarith [not_le.mp h])]; linarith [not_le.mp h]
    rw [hsupp u h1]; simp
  have hzero' : ∀ u : ℝ, u ∉ Set.Ioc (-1 : ℝ) 1 →
      (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))) = 0 := by
    intro u hu
    by_cases h : u ∈ Set.Icc (-1 : ℝ) 1
    · have : u = -1 := by
        rw [Set.mem_Icc] at h; rw [Set.mem_Ioc] at hu
        have hle : u ≤ -1 := by
          by_contra hc
          exact hu ⟨not_le.mp hc, h.2⟩
        linarith [h.1]
      rw [this, hsupp (-1) (by norm_num)]; simp
    · exact hzero u h
  have hfull : (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
      = ∫ u in (-1 : ℝ)..1, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Ioc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_apply, if_neg hu]
      exact hzero' u hu
  calc (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ))))
      = h * (∫ u in (-1 : ℝ)..1, (φ ((lam + h * u - lam) / h) : ℂ) *
          Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ)))) := hsub.symm
    _ = h * (∫ u in (-1 : ℝ)..1, Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
          ((φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))) := by
          rw [hsimp]
    _ = h * (Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
          ∫ u in (-1 : ℝ)..1, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) := by
          rw [intervalIntegral.integral_const_mul]
    _ = h * (Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
          ∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) := by
          rw [hfull]
    _ = h * (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) *
          Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) := by ring

/-- **Unwinding the band symbol.**  The inverse Fourier transform of the (rescaled) band symbol of
the target is `(2π)⁻¹ · h · \hatφ(h z) · e^{-I λ z}`; equivalently the kernel of the `k`-th band
operator is the `L¹`-normalised dilation of `\hatφ` times a modulation. -/
theorem bandSymbol_fourierInv (φ : ℝ → ℝ) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {lam h : ℝ} (hh : 0 < h) (z : ℝ) :
    FourierTransformInv.fourierInv (fun ξ => bandSymbol φ lam h (-(2 * Real.pi) * ξ)) z
      = (2 * Real.pi)⁻¹ * (h * (∫ u : ℝ, (φ u : ℂ) *
            Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ)))) := by
  have hkey := fourierInv_change_of_variables (bandSymbol φ lam h) z
  have hleft : (∫ θ : ℝ, bandSymbol φ lam h θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = h * (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) := by
    rw [← integral_bandSymbol φ lam h z hh.le]
    exact bandTerm_apply φ hsupp hh
  have hright : (∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * ξ * z) : ℂ) * Complex.I) *
        bandSymbol φ lam h (-(2 * Real.pi) * ξ))
      = FourierTransformInv.fourierInv
          (fun ξ => bandSymbol φ lam h (-(2 * Real.pi) * ξ)) z := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with v
    simp only [Real.inner_apply, smul_eq_mul]
    congr 1
    ring
  have hA : h * (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
        * Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ)))
      = 2 * Real.pi * FourierTransformInv.fourierInv
          (fun ξ => bandSymbol φ lam h (-(2 * Real.pi) * ξ)) z := by
    rw [← hleft, hkey, hright]
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hA]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]


/-- The (unnormalised) Fourier transform of the window `φ`: `\hatφ(s) = ∫ u, φ u · e^{-I s u}`. -/
noncomputable def hat (φ : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * (s : ℂ) * (u : ℂ)))

/-! ### The window `hat φ` as a Schwartz function

The target's band kernel is `h · hat φ (h ·)`, where `hat φ w = ∫ u, φ u · e^{-I u w}`.  To feed it
to the `BourgainMax` machinery (which asks for a `SchwartzMap`) we build the Schwartz function
`𝓕 Φ'` of the rescaled window `Φ'(u) = 2π φ(2π u)`, whose Fourier transform is exactly `hat φ`
(the `2π`'s are the Jacobian of `u = 2π v` in Mathlib's `e^{-2πi x ξ}` convention). -/

/-- The rescaledwindow `Φ'(u) = 2π · φ(2π u)`. -/
noncomputable def phiShift (φ : ℝ → ℝ) : ℝ → ℂ :=
  fun u => (φ (2 * Real.pi * u) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)

lemma phiShift_contDiff (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (phiShift φ) := by
  unfold phiShift
  exact (Complex.ofRealCLM.contDiff.comp (hφ.comp (by fun_prop))).mul contDiff_const

lemma phiShift_hasCompactSupport (φ : ℝ → ℝ) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) :
    HasCompactSupport (phiShift φ) := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  refine HasCompactSupport.intro (K := Set.Icc (-(1/(2*Real.pi))) (1/(2*Real.pi))) isCompact_Icc ?_
  intro u hu
  have ha : 0 < 1/(2*Real.pi) := by positivity
  have huabs : 1/(2*Real.pi) < |u| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp only [phiShift]
  have harg : 1 ≤ |2 * Real.pi * u| := by
    rw [abs_mul, abs_of_pos h2pi]
    have := mul_lt_mul_of_pos_left huabs h2pi
    rw [mul_one_div_cancel (ne_of_gt h2pi)] at this
    linarith
  rw [hsupp _ harg, Complex.ofReal_zero, zero_mul]

/-- The window `hat φ` as a Schwartz function. -/
noncomputable def winPsi (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) : SchwartzMap ℝ ℂ :=
  𝓕 ((phiShift_hasCompactSupport φ hsupp).toSchwartzMap (phiShift_contDiff φ hφ))

lemma winPsi_coe (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (w : ℝ) :
    winPsi φ hφ hsupp w = hat φ w := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2pine : (2 * Real.pi) ≠ 0 := ne_of_gt h2pi
  unfold winPsi hat
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  have hcoe : ∀ v : ℝ,
      ((phiShift_hasCompactSupport φ hsupp).toSchwartzMap (phiShift_contDiff φ hφ) : ℝ → ℂ) v
        = phiShift φ v := fun v => HasCompactSupport.toSchwartzMap_toFun _ _ v
  simp_rw [hcoe]
  set G : ℝ → ℂ := fun x => phiShift φ x
    * Complex.exp (-(Complex.I * (w : ℂ) * ((2 * Real.pi * x : ℝ) : ℂ))) with hG
  have hpt : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) • phiShift φ v
      = G v := by
    intro v
    rw [hG, smul_eq_mul]
    rw [show (↑(-2 * Real.pi * inner ℝ v w) : ℂ) * Complex.I
        = -(Complex.I * (w : ℂ) * ((2 * Real.pi * v : ℝ) : ℂ)) by
      rw [Real.inner_apply]; push_cast; ring]
    ring
  simp_rw [hpt]
  have hmain := MeasureTheory.Measure.integral_comp_mul_left G ((2 * Real.pi)⁻¹)
  rw [show |(((2 * Real.pi)⁻¹)⁻¹)| = 2 * Real.pi by rw [inv_inv]; exact abs_of_pos h2pi] at hmain
  have hsplit : ∫ x, G x = (2 * Real.pi)⁻¹ • ∫ x, G ((2 * Real.pi)⁻¹ * x) := by
    rw [hmain, smul_smul, inv_mul_cancel₀ h2pine, one_smul]
  rw [hsplit]
  have hpt2 : ∀ x : ℝ, G ((2 * Real.pi)⁻¹ * x)
      = ((2 * Real.pi : ℝ) : ℂ) * ((φ x : ℂ) * Complex.exp (-(Complex.I * (w : ℂ) * (x : ℂ)))) := by
    intro x
    rw [hG]
    have hx : 2 * Real.pi * ((2 * Real.pi)⁻¹ * x) = x := by field_simp
    show (φ (2 * Real.pi * ((2 * Real.pi)⁻¹ * x)) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (w : ℂ) * ((2 * Real.pi * ((2 * Real.pi)⁻¹ * x) : ℝ) : ℂ)))
      = ((2 * Real.pi : ℝ) : ℂ) * ((φ x : ℂ) * Complex.exp (-(Complex.I * (w : ℂ) * (x : ℂ))))
    rw [hx]
    ring
  simp_rw [hpt2]
  rw [MeasureTheory.integral_const_mul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ h2pine, Complex.ofReal_one, one_mul]

/-- The window `hat φ` is bounded by the mass of `φ` (for `φ ≥ 0`): this supplies the bound `M`
of the deep input when the window is `hat φ`. -/
lemma norm_hat_le (φ : ℝ → ℝ) (hbd : ∀ x : ℝ, 0 ≤ φ x) (s : ℝ) :
    ‖hat φ s‖ ≤ ∫ u : ℝ, φ u := by
  have hexp : ∀ u : ℝ, ‖Complex.exp (-(Complex.I * (s : ℂ) * (u : ℂ)))‖ = 1 := by
    intro u
    rw [show Complex.exp (-(Complex.I * (s : ℂ) * (u : ℂ)))
        = Complex.exp (((-(s * u) : ℝ) : ℂ) * Complex.I) by
      congr 1; push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hpt : ∀ u : ℝ, ‖(φ u : ℂ) * Complex.exp (-(Complex.I * (s : ℂ) * (u : ℂ)))‖ = φ u := by
    intro u
    rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal,
      show φ u * φ u = (φ u) ^ 2 from by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (hbd u), hexp u, mul_one]
  calc ‖hat φ s‖
      = ‖∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * (s : ℂ) * (u : ℂ)))‖ := rfl
    _ ≤ ∫ u : ℝ, ‖(φ u : ℂ) * Complex.exp (-(Complex.I * (s : ℂ) * (u : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, φ u := by
        refine integral_congr_ae ?_
        filter_upwards with u
        exact hpt u

lemma norm_winPsi_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbd : ∀ x : ℝ, 0 ≤ φ x) (w : ℝ) :
    ‖winPsi φ hφ hsupp w‖ ≤ ∫ u : ℝ, φ u := by
  rw [winPsi_coe φ hφ hsupp w]
  exact norm_hat_le φ hbd w



/-- **The `k`-th band term is the windowed smoothing of the modulated function.**  For
`f ∈ L¹ ∩ L²`, the `y`-integral of `f` against one band of the target equals `e^{-I λ x}` times the
smoothing of `f · e^{I λ ·}` with the `L¹`-normalised dilation of `\hatφ` at scale `1/h`; this is
exactly the smoothing appearing in `winCurve`. -/
theorem bandTerm_windowed (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hbd : ∀ x, ‖φ x‖ ≤ 1)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) {lam h : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    (∫ y, f y * bandTerm φ lam h x y)
      = (∫ y, f y * Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ)) * (h * hat φ (h * (x - y))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * (x : ℂ))) := by
  have hne : (-(2 * Real.pi) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hm : Integrable (fun ξ : ℝ => bandSymbol φ lam h (-(2 * Real.pi) * ξ)) :=
    (integrable_comp_mul_left_iff (bandSymbol φ lam h) hne).2
      (memLp_one_iff_integrable.mp (bandSymbol_memLp φ hφ hbd hsupp hh 1))
  rw [band_term_eq_multiplier φ hφ hbd hsupp hh hf1 hf2 x]
  rw [fourierInv_mul_fourier_eq_convolution hm (memLp_one_iff_integrable.mp hf1) x]
  have hfourier : ∀ z : ℝ, FourierTransformInv.fourierInv
      (fun ξ => bandSymbol φ lam h (-(2 * Real.pi) * ξ)) z
      = (2 * Real.pi)⁻¹ * (h * hat φ (h * z) * Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ)))) := by
    intro z
    rw [bandSymbol_fourierInv φ hsupp hh z]
    simp only [hat]
  simp only [hfourier]
  have hL : (2 * (Real.pi : ℂ)) * (∫ y, f y * ((2 * Real.pi)⁻¹ *
        (h * hat φ (h * (x - y)) * Complex.exp (-(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ))))))
      = ∫ y, f y * (h * hat φ (h * (x - y)))
          * Complex.exp (-(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    rw [Complex.ofReal_inv,
      show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [hL]
  have hR : (∫ y, f y * Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))
        * (h * hat φ (h * (x - y)))) * Complex.exp (-(Complex.I * (lam : ℂ) * (x : ℂ)))
      = ∫ y, f y * (h * hat φ (h * (x - y)))
          * Complex.exp (-(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ))) := by
    rw [← MeasureTheory.integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    rw [show -(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ))
        = Complex.I * (lam : ℂ) * (y : ℂ) + -(Complex.I * (lam : ℂ) * (x : ℂ)) by
      push_cast; ring, Complex.exp_add]
    ring
  rw [hR]

/-- **The band sum of the target is a sum of windowed smoothings of the modulated slices.** -/
theorem bandSum_windowed (K : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hbd : ∀ x, ‖φ x‖ ≤ 1)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (lam : Fin K → ℝ) {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    (∫ y, f y * (∑ k : Fin K, bandTerm φ (lam k) h x y))
      = ∑ k : Fin K,
          (∫ y, f y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * (h * hat φ (h * (x - y))))
            * Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) := by
  have hbdd : ∀ (k : Fin K) (y : ℝ), ‖bandTerm φ (lam k) h x y‖ ≤ 2 * h := by
    intro k y
    have h1 : ∀ th : ℝ, ‖(φ ((th - lam k) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))‖ ≤ 1 := by
      intro th
      rw [norm_mul, show Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))
          = Complex.exp (((-(x - y) * th : ℝ) : ℂ) * Complex.I) by
            congr 1; push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      simpa using hbd ((th - lam k) / h)
    have hc : Continuous fun th : ℝ => (φ ((th - lam k) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ))) := by fun_prop
    calc ‖bandTerm φ (lam k) h x y‖
        ≤ ∫ th in (lam k - h)..(lam k + h), ‖(φ ((th - lam k) / h) : ℂ) *
            Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ _th in (lam k - h)..(lam k + h), (1 : ℝ) := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (hc.norm.intervalIntegrable _ _) intervalIntegrable_const
          intro th _
          exact h1 th
      _ = 2 * h := by rw [intervalIntegral.integral_const]; simp; ring
  have hcont : ∀ k : Fin K, Continuous (fun y : ℝ => bandTerm φ (lam k) h x y) := by
    intro k
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := (volume : Measure ℝ))
      (f := fun y th : ℝ => (φ ((th - lam k) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))) (by fun_prop)
      (lam k - h) (lam k + h)
    simpa [bandTerm] using h
  have hint : ∀ k : Fin K, Integrable (fun y : ℝ => f y * bandTerm φ (lam k) h x y) := by
    intro k
    refine Integrable.mono' (((memLp_one_iff_integrable.mp hf1).norm).const_mul (2 * h))
      (hf1.aestronglyMeasurable.mul ((hcont k).aestronglyMeasurable)) ?_
    filter_upwards with y
    rw [norm_mul]
    calc ‖f y‖ * ‖bandTerm φ (lam k) h x y‖ ≤ ‖f y‖ * (2 * h) :=
          mul_le_mul_of_nonneg_left (hbdd k y) (norm_nonneg _)
      _ = 2 * h * ‖f y‖ := by ring
  have hpt : (fun y : ℝ => f y * (∑ k : Fin K, bandTerm φ (lam k) h x y))
      = fun y : ℝ => ∑ k : Fin K, f y * bandTerm φ (lam k) h x y := by
    funext y; rw [Finset.mul_sum]
  rw [hpt, integral_finsetSum _ (fun k _ => hint k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bandTerm_windowed φ hφ hbd hsupp hh hf1 hf2 x]

end BandDecomp


/-! ## The assembly of the target: slices, the identification, and the energy bound

This section develops the frequency-slice machinery that identifies the target's band operator
with the `winCurve` smoothings: the `C^∞` slice profiles `sliceFun`, the overlap bound
`sliceFun_sum_sq_le`, the slice kernel `sliceKernel` (a Schwartz function with `𝓕 ψ_k = η_k`),
the frequency slice `sliceOf f lam`, the slice replacement `bandTerm_slice`, the summed
identification `bandSum_slice_windowed`, Plancherel for `L¹ ∩ L²` (`lintegral_fourier_sq_eq`)
and the energy bound `slice_energy_le`.
-/

namespace BourgainAssembly

open _root_.MeasureTheory Finset
open scoped BigOperators ENNReal Interval FourierTransform Convolution

open scoped ContDiff

/-- The base bump: a `C^∞` function on `ℝ` equal to `1` on `[-1,1]` and vanishing off
`(-3/2,3/2)`. -/
noncomputable def baseBump : ContDiffBump (0 : ℝ) := ⟨1, 3/2, by norm_num, by norm_num⟩

lemma baseBump_one {s : ℝ} (hs : |s| ≤ 1) : baseBump s = 1 :=
  ContDiffBump.one_of_mem_closedBall baseBump (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hs)

lemma baseBump_zero {s : ℝ} (hs : 3/2 ≤ |s|) : baseBump s = 0 :=
  ContDiffBump.zero_of_le_dist baseBump (by rwa [Real.dist_eq, sub_zero])

lemma baseBump_nonneg (s : ℝ) : 0 ≤ baseBump s := ContDiffBump.nonneg baseBump

lemma baseBump_le_one (s : ℝ) : baseBump s ≤ 1 := ContDiffBump.le_one baseBump

lemma baseBump_contDiff : ContDiff ℝ ∞ (⇑baseBump) := ContDiffBump.contDiff baseBump

/-- The slice multiplier profile centred at `-lam/(2π)`: `ξ ↦ β(4π ξ + 2 lam)`.  It equals `1` on
`[-lam/2π - 1/4π, -lam/2π + 1/4π]` and vanishes outside `(-lam/2π - 3/8π, -lam/2π + 3/8π)`. -/
noncomputable def sliceFun (lam ξ : ℝ) : ℝ := baseBump (4 * Real.pi * ξ + 2 * lam)

lemma four_pi_pos : (0:ℝ) < 4 * Real.pi := by positivity

lemma sliceFun_arg (lam ξ : ℝ) :
    4 * Real.pi * ξ + 2 * lam = 4 * Real.pi * (ξ + lam / (2 * Real.pi)) := by
  field_simp; ring

lemma sliceFun_one {lam ξ : ℝ} (h : |ξ + lam / (2 * Real.pi)| ≤ 1 / (4 * Real.pi)) :
    sliceFun lam ξ = 1 := by
  refine baseBump_one ?_
  rw [sliceFun_arg, abs_mul, abs_of_pos four_pi_pos]
  calc 4 * Real.pi * |ξ + lam / (2 * Real.pi)| ≤ 4 * Real.pi * (1 / (4 * Real.pi)) :=
        mul_le_mul_of_nonneg_left h four_pi_pos.le
    _ = 1 := by field_simp

lemma sliceFun_zero {lam ξ : ℝ} (h : 3 / (8 * Real.pi) ≤ |ξ + lam / (2 * Real.pi)|) :
    sliceFun lam ξ = 0 := by
  refine baseBump_zero ?_
  rw [sliceFun_arg, abs_mul, abs_of_pos four_pi_pos]
  calc (3:ℝ) / 2 = 4 * Real.pi * (3 / (8 * Real.pi)) := by field_simp; ring
    _ ≤ 4 * Real.pi * |ξ + lam / (2 * Real.pi)| := mul_le_mul_of_nonneg_left h four_pi_pos.le

lemma sliceFun_zero_of_abs {lam ξ : ℝ} (h : 3 / 2 ≤ |4 * Real.pi * ξ + 2 * lam|) :
    sliceFun lam ξ = 0 := baseBump_zero h

lemma sliceFun_nonneg (lam ξ : ℝ) : 0 ≤ sliceFun lam ξ := baseBump_nonneg _

lemma sliceFun_le_one (lam ξ : ℝ) : sliceFun lam ξ ≤ 1 := baseBump_le_one _

lemma sliceFun_contDiff (lam : ℝ) : ContDiff ℝ ∞ (fun ξ : ℝ => sliceFun lam ξ) :=
  baseBump_contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun ξ : ℝ => 4 * Real.pi * ξ + 2 * lam)

/-- The slice profiles have compact support. -/
lemma sliceFun_hasCompactSupport (lam : ℝ) : HasCompactSupport (fun ξ : ℝ => sliceFun lam ξ) := by
  refine HasCompactSupport.of_support_subset_isCompact (K :=
    Set.Icc ((-(3:ℝ)/2 - 2 * lam) / (4 * Real.pi)) (((3:ℝ)/2 - 2 * lam) / (4 * Real.pi)))
    isCompact_Icc ?_
  intro ξ hξ
  simp only [Function.mem_support] at hξ
  have he1 : 4 * Real.pi * ((-(3:ℝ)/2 - 2 * lam) / (4 * Real.pi)) = -(3:ℝ)/2 - 2 * lam := by
    field_simp
  have he2 : 4 * Real.pi * (((3:ℝ)/2 - 2 * lam) / (4 * Real.pi)) = (3:ℝ)/2 - 2 * lam := by
    field_simp
  rw [Set.mem_Icc]
  constructor
  · by_contra hcon
    push Not at hcon
    refine hξ (sliceFun_zero_of_abs ?_)
    have h1 : 4 * Real.pi * ξ < -(3:ℝ)/2 - 2 * lam := by
      have := mul_lt_mul_of_pos_left hcon four_pi_pos; linarith
    rw [abs_of_neg (by linarith)]; linarith
  · by_contra hcon
    push Not at hcon
    refine hξ (sliceFun_zero_of_abs ?_)
    have h1 : (3:ℝ)/2 - 2 * lam < 4 * Real.pi * ξ := by
      have := mul_lt_mul_of_pos_left hcon four_pi_pos; linarith
    rw [abs_of_pos (by linarith)]; linarith



/-- The overlap bound `∑_k η_k(ξ)² ≤ 2`: at most two of the `3/2`-radius intervals centred at the
`4πξ + 2λ_k` can meet. -/
lemma sliceFun_sum_sq_le (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) (ξ : ℝ) :
    ∑ k : Fin K, (sliceFun (lam k) ξ) ^ 2 ≤ 2 := by
  have h := Commons.Analysis.Fourier.sum_sq_le_two_of_separated K lam hsep (⇑baseBump)
    (fun s hs => baseBump_one hs) (fun s hs => baseBump_zero hs)
    (fun s => baseBump_nonneg s) (fun s => baseBump_le_one s) ξ
  simpa only [sliceFun] using h

/-- The complex-valued slice profile has compact support. -/
lemma sliceFun_hasCompactSupport_C (lam : ℝ) :
    HasCompactSupport (fun ξ : ℝ => (sliceFun lam ξ : ℂ)) :=
  (sliceFun_hasCompactSupport lam).mono (fun ξ hξ => by
    simp only [Function.mem_support] at hξ ⊢
    intro h
    exact hξ (by rw [h]; rfl))

lemma sliceFun_contDiff_C (lam : ℝ) : ContDiff ℝ ∞ (fun ξ : ℝ => (sliceFun lam ξ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (sliceFun_contDiff lam)

/-- The slice profile as a Schwartz function. -/
noncomputable def sliceSchwartz (lam : ℝ) : SchwartzMap ℝ ℂ :=
  (sliceFun_hasCompactSupport_C lam).toSchwartzMap (sliceFun_contDiff_C lam)

lemma sliceSchwartz_coe (lam : ℝ) :
    (sliceSchwartz lam : ℝ → ℂ) = fun ξ => (sliceFun lam ξ : ℂ) := by
  funext ξ
  exact HasCompactSupport.toSchwartzMap_toFun _ _ ξ

/-- The `L¹` kernel whose Fourier transform is the slice profile: `ψ_k := 𝓕⁻(η_k)`. -/
noncomputable def sliceKernel (lam : ℝ) : SchwartzMap ℝ ℂ :=
  FourierTransform.fourierInv (sliceSchwartz lam)

lemma sliceKernel_fourier (lam : ℝ) :
    FourierTransform.fourier (sliceKernel lam : ℝ → ℂ) = fun ξ => (sliceFun lam ξ : ℂ) := by
  rw [← SchwartzMap.fourier_coe, sliceKernel, FourierInvPair.fourier_fourierInv_eq, sliceSchwartz_coe]

lemma sliceKernel_one {lam ξ : ℝ} (h : |ξ + lam / (2 * Real.pi)| ≤ 1 / (4 * Real.pi)) :
    FourierTransform.fourier (sliceKernel lam : ℝ → ℂ) ξ = 1 := by
  simp only [sliceKernel_fourier, sliceFun_one h, Complex.ofReal_one]


/-- The frequency slice of `f` at `lam`: the convolution of `f` with the `L¹` kernel `ψ_k` whose
Fourier transform is the slice profile `η_k`. -/
noncomputable def sliceOf (f : ℝ → ℂ) (lam : ℝ) : ℝ → ℂ :=
  fun x => ∫ y, (sliceKernel lam : ℝ → ℂ) y * f (x - y)

lemma sliceOf_eq_convolution (f : ℝ → ℂ) (lam : ℝ) :
    sliceOf f lam = MeasureTheory.convolution (sliceKernel lam : ℝ → ℂ) f
      (ContinuousLinearMap.lsmul ℂ ℂ) volume := by
  funext x
  rw [MeasureTheory.convolution_def]
  simp only [sliceOf, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma sliceOf_fourier {f : ℝ → ℂ} (hf : Integrable f) (lam ξ : ℝ) :
    FourierTransform.fourier (sliceOf f lam) ξ = (sliceFun lam ξ : ℂ) * FourierTransform.fourier f ξ := by
  rw [sliceOf_eq_convolution, Real.fourier_smul_convolution_eq (sliceKernel lam).integrable hf ξ,
    sliceKernel_fourier lam, smul_eq_mul]

lemma sliceOf_integrable {f : ℝ → ℂ} (hf : Integrable f) (lam : ℝ) :
    Integrable (sliceOf f lam) := by
  rw [sliceOf_eq_convolution]
  exact Integrable.integrable_convolution (L := ContinuousLinearMap.lsmul ℂ ℂ)
    (sliceKernel lam).integrable hf

lemma sliceOf_memLp {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) (lam : ℝ) :
    MemLp (sliceOf f lam) 2 (volume : Measure ℝ) :=
  (Commons.Analysis.Fourier.memLp_convolution_one_two ((sliceKernel lam).memLp 1 volume) hf).1


/-- If `bandSymbol φ lam h th ≠ 0` then `th` lies in the band, hence `sliceFun lam ξ = 1` for
`th = -2πξ`. -/
lemma sliceFun_eq_one_of_bandSymbol_ne_zero {φ : ℝ → ℝ} (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {lam h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1/2) {ξ : ℝ}
    (hs : BandDecomp.bandSymbol φ lam h (-(2 * Real.pi) * ξ) ≠ 0) :
    sliceFun lam ξ = 1 := by
  have hmem : (-(2 * Real.pi) * ξ) ∈ Set.Ioc (lam - h) (lam + h) := by
    by_contra hc
    exact hs (by
      rw [BandDecomp.bandSymbol, Set.indicator_apply, if_neg hc])
  rw [Set.mem_Ioc] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have habs : |(-(2 * Real.pi) * ξ) - lam| ≤ h := by
    rw [abs_le]; constructor <;> linarith
  refine sliceFun_one ?_
  have h1 : (-(2 * Real.pi) * ξ) - lam = -(2 * Real.pi) * (ξ + lam / (2 * Real.pi)) := by
    field_simp; ring
  rw [h1, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at habs
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hk : (2:ℝ) * Real.pi * (1 / (4 * Real.pi)) = 1 / 2 := by field_simp; norm_num
  nlinarith [habs, hh2, hk, Real.pi_pos]

/-- **Slice replacement**: the `k`-th band term of `f` equals that of the frequency slice
`sliceOf f lam`. -/
theorem bandTerm_slice (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hbd : ∀ x, ‖φ x‖ ≤ 1)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) {lam h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1/2)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    (∫ y, f y * BandDecomp.bandTerm φ lam h x y)
      = (∫ y, sliceOf f lam y * BandDecomp.bandTerm φ lam h x y) := by
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  rw [BandDecomp.band_term_eq_multiplier φ hφ hbd hsupp hh hf1 hf2 x]
  rw [BandDecomp.band_term_eq_multiplier φ hφ hbd hsupp hh
        (memLp_one_iff_integrable.mpr (sliceOf_integrable hfi lam)) (sliceOf_memLp hf2 lam) x]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  rw [sliceOf_fourier hfi lam ξ]
  by_cases hs : BandDecomp.bandSymbol φ lam h (-(2 * Real.pi) * ξ) = 0
  · rw [hs, zero_mul, zero_mul]
  · rw [sliceFun_eq_one_of_bandSymbol_ne_zero hsupp hh hh2 hs]
    simp


/-- **The band sum of the target is a sum of windowed smoothings of the *slices*.**
For `f ∈ L¹ ∩ L²` and `h ≤ 1/2`,
`∫ y, f y (Σ_k bandTerm φ (λ_k) h x y) = Σ_k e^{-Iλ_k x} ∫ y, (sliceOf f λ_k) y e^{Iλ_k y} (h \hatφ(h(x-y)))`. -/
theorem bandSum_slice_windowed (K : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hbd : ∀ x, ‖φ x‖ ≤ 1) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (lam : Fin K → ℝ)
    {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1/2)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    (∫ y, f y * (∑ k : Fin K, BandDecomp.bandTerm φ (lam k) h x y))
      = ∑ k : Fin K,
          (∫ y, sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
              * (h * BandDecomp.hat φ (h * (x - y))))
            * Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) := by
  rw [BandDecomp.bandSum_windowed K φ hφ hbd hsupp lam hh hf1 hf2 x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  have h1 := BandDecomp.bandTerm_windowed φ hφ hbd hsupp hh hf1 hf2 x (lam := lam k)
  have h2 := BandDecomp.bandTerm_windowed φ hφ hbd hsupp hh
    (memLp_one_iff_integrable.mpr (sliceOf_integrable hfi (lam k))) (sliceOf_memLp hf2 (lam k))
    x (lam := lam k)
  have h3 := bandTerm_slice φ hφ hbd hsupp hh hh2 hf1 hf2 x (lam := lam k)
  rw [← h1, ← h2]
  exact h3


/-- Plancherel for the forward Fourier transform of an `L¹ ∩ L²` function (pointwise form). -/
lemma lintegral_fourier_sq_eq {g : ℝ → ℂ} (hg1 : MemLp g 1 (volume : Measure ℝ))
    (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖FourierTransform.fourier g x‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) := by
  have hae := Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp (V := ℝ) hg1 hg2
  have hcoe := MemLp.coeFn_toLp hg2
  have hA : ∫⁻ x, ‖FourierTransform.fourier g x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖((FourierTransform.fourier (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  have hB : ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖((hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [← hx]
  rw [hA, hB, ← BoundaryLayer.lp_enorm_sq_eq_lintegral (FourierTransform.fourier (hg2.toLp g)),
    BoundaryLayer.enorm_fourier (hg2.toLp g), BoundaryLayer.lp_enorm_sq_eq_lintegral (hg2.toLp g)]

/-- **Energy of the frequency slices.**  For `1`-separated `lam` and `f ∈ L¹ ∩ L²`, the sum of the
`L²`-energies of the modulated slices `sliceOf f (lam k) · e^{I lam k ·}` is at most `2‖f‖²`. -/
theorem slice_energy_le (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∑ k : Fin K, ∫⁻ y, ‖sliceOf f (lam k) y *
        Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ ^ (2:ℝ)
      ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  classical
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  have hFmeas : AEMeasurable (fun ξ : ℝ => FourierTransform.fourier f ξ) (volume : Measure ℝ) :=
    (MeasureTheory.Lp.aestronglyMeasurable
      (FourierTransform.fourier (hf2.toLp f))).aemeasurable.congr
      (Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp (V := ℝ) hf1 hf2)
  have hmodnorm : ∀ (k : Fin K) (y : ℝ), ‖sliceOf f (lam k) y *
      Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ = ‖sliceOf f (lam k) y‖ := by
    intro k y
    rw [norm_mul, show Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
        = Complex.exp (((lam k * y : ℝ)) * Complex.I) by congr 1; push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hmod : ∀ (k : Fin K) (y : ℝ), ‖sliceOf f (lam k) y *
      Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ = ‖sliceOf f (lam k) y‖ₑ := by
    intro k y
    rw [← ofReal_norm, hmodnorm k y, ofReal_norm]
  have hkey : ∀ k : Fin K, ∫⁻ y, ‖sliceOf f (lam k) y‖ₑ ^ (2:ℝ)
      = ∫⁻ ξ, ‖(sliceFun (lam k) ξ : ℂ) * FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ) := by
    intro k
    rw [← lintegral_fourier_sq_eq (memLp_one_iff_integrable.mpr (sliceOf_integrable hfi (lam k)))
      (sliceOf_memLp hf2 (lam k))]
    apply lintegral_congr_ae
    filter_upwards with ξ
    rw [sliceOf_fourier hfi (lam k) ξ]
  have hsum_term : ∀ (ξ : ℝ), ∑ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ) *
      FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ)
      ≤ (2:ℝ≥0∞) * ‖FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ) := by
    intro ξ
    have hterm : ∀ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ)‖ₑ ^ (2:ℝ)
        = ENNReal.ofReal (‖(sliceFun (lam k) ξ : ℂ)‖ ^ 2) := by
      intro k
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two]
    have hnorm : ∀ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ)‖ = sliceFun (lam k) ξ := by
      intro k; rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs, abs_of_nonneg (sliceFun_nonneg _ _)]
    have hb : ∑ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ)‖ₑ ^ (2:ℝ) ≤ 2 := by
      rw [Finset.sum_congr rfl (fun k _ => hterm k),
        Finset.sum_congr rfl (fun k _ => by rw [hnorm k]),
        ← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _), ← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal (sliceFun_sum_sq_le K lam hsep ξ)
    have hsum_eq : ∑ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ) * FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ)
        = (∑ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ)‖ₑ ^ (2:ℝ))
            * ‖FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)])
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_right hb bot_le
  calc ∑ k : Fin K, ∫⁻ y, ‖sliceOf f (lam k) y *
        Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ ^ (2:ℝ)
      = ∑ k : Fin K, ∫⁻ y, ‖sliceOf f (lam k) y‖ₑ ^ (2:ℝ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        apply lintegral_congr_ae
        filter_upwards with y
        rw [hmod k y]
    _ = ∫⁻ ξ, ∑ k : Fin K, ‖(sliceFun (lam k) ξ : ℂ) * FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ) := by
        rw [Finset.sum_congr rfl (fun k _ => hkey k), lintegral_finsetSum']
        intro k _
        have hm : Measurable (fun ξ : ℝ => (sliceFun (lam k) ξ : ℂ)) :=
          (Complex.continuous_ofReal.comp (sliceFun_contDiff (lam k)).continuous).measurable
        exact (hm.aemeasurable.mul hFmeas).enorm.pow_const 2
    _ ≤ ∫⁻ ξ, (2:ℝ≥0∞) * ‖FourierTransform.fourier f ξ‖ₑ ^ (2:ℝ) :=
        lintegral_mono hsum_term
    _ = 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
        rw [lintegral_const_mul' (2:ℝ≥0∞) _ (by norm_num)]
        rw [lintegral_fourier_sq_eq hf1 hf2]


end BourgainAssembly

namespace BourgainChain

open BourgainSmoothWindow

/-- **The entropy chain bound for a finite family.** -/
theorem chain_exp_sum_le_entropy (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ), 1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      ((Finset.univ.image (fun i : Fin (N+1) => a i - a (σ (S-1) i))).card : ℕ) ≤ M S →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
          (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    refine ⟨1, one_pos, ?_⟩
    intro N S a σ M hS hconst hNM hcard hnet2
    have hz : (fun y : ℝ => ENNReal.ofReal
        (⨆ i : Fin (N+1), ‖∑ k : Fin 0, a i k * expChar (lam k) y‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) := by
      funext y
      simp
    rw [hz, lintegral_zero]
    exact bot_le
  obtain ⟨c₀, hc₀pos, hc₀⟩ := max_finset_exponential_sum_l2 K lam hsep
  obtain ⟨c₁, hc₁pos, hc₁⟩ := separated_exponentials_near_orthogonal
  refine ⟨200 * (c₀ + c₁ + 1), by positivity, ?_⟩
  intro N S a σ M hS hconst hNM hcard hnet2
  have hnet : ∀ t, t ≤ S → ∀ i : Fin (N+1), ‖a i - a (σ t i)‖ ≤ 2 * (1/2:ℝ)^t := by
    intro t ht i
    have h2 := hnet2 t ht i
    have hsqrt : Real.sqrt (∑ k : Fin K, ‖a i k - a (σ t i) k‖^2) ≤ 2 * (1/2:ℝ)^t := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (1/2:ℝ)^t)]
      exact Real.sqrt_le_sqrt h2
    refine le_trans ?_ hsqrt
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro m
    calc ‖(a i - a (σ t i)) m‖ = ‖a i m - a (σ t i) m‖ := by rw [Pi.sub_apply]
      _ = Real.sqrt (‖a i m - a (σ t i) m‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ x : Fin K, ‖a i x - a (σ t i) x‖^2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum
            (fun x (_ : x ∈ Finset.univ) => sq_nonneg (‖a i x - a (σ t i) x‖))
            (Finset.mem_univ m))
  obtain ⟨q, B, hqmem, hqdiff, hqBeq, hqcard, hqcard0, hqcard0diff, hqnorm, hqdecomp⟩ :=
    BourgainSmoothWindow.exists_dyadic_chain_decomposition (N+1) S a σ hnet
  let p : Fin K → ℂ := a (σ 0 0)
  let D : ℝ := Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2)
  let Φ : ℝ → (Fin K → ℂ) → ℂ := fun y v => ∑ k : Fin K, v k * expChar (lam k) y
  have hΦadd : ∀ y (u v : Fin K → ℂ), Φ y (u + v) = Φ y u + Φ y v := by
    intro y u v
    simp only [Φ, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hΦsum : ∀ y (s : Finset ℕ) (u : ℕ → Fin K → ℂ),
      Φ y (∑ k ∈ s, u k) = ∑ k ∈ s, Φ y (u k) := by
    intro y s u
    simp only [Φ, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hΦcont : ∀ b : Fin K → ℂ, Continuous (fun y : ℝ => Φ y b) := by
    intro b
    simp only [Φ]
    refine continuous_finsetSum _ (fun k _ => continuous_const.mul ?_)
    unfold expChar; fun_prop
  have hqS : ∀ i : Fin (N+1), q S i = σ 0 0 := by
    intro i
    have hmem := hqmem S hS le_rfl i
    rw [Nat.sub_self] at hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    rw [← hj, hconst j]
  have hB_ne : ∀ k, k < S → (B k).Nonempty := fun k hk => ⟨_, hqdiff k hk 0⟩
  let cls : ℕ → Finset (Fin K → ℂ) := fun j => if j < S then B j else {p}
  have hcls_ne : ∀ j, (cls j).Nonempty := by
    intro j
    by_cases hj : j < S
    · have h1 : cls j = B j := by simp [cls, hj]
      rw [h1]
      exact hB_ne j hj
    · have h1 : cls j = {p} := by simp [cls, hj]
      rw [h1]
      exact ⟨p, Finset.mem_singleton_self p⟩
  have hclsS : cls S = {p} := by simp [cls]
  have hclsj : ∀ j, j < S → cls j = B j := fun j hj => by simp [cls, hj]
  let Acls : ℕ → ℝ → ℝ := fun j y => (cls j).sup' (hcls_ne j) (fun b => ‖Φ y b‖)
  have hAcls_cont : ∀ j, Continuous (Acls j) := fun j =>
    Continuous.finset_sup'_apply (hcls_ne j) (fun b _ => (hΦcont b).norm)
  have hAcls_nn : ∀ j y, 0 ≤ Acls j y := by
    intro j y
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖Φ y b‖) (hcls_ne j).choose_spec)
  have hAeqS : ∀ y, Acls S y = (⨆ b ∈ cls S, ‖Φ y b‖) := by
    intro y
    simp only [Acls]
    exact (iSup_finset_eq_sup' (cls S) (hcls_ne S) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqk : ∀ k, k < S → ∀ y, Acls k y = (⨆ b ∈ B k, ‖Φ y b‖) := by
    intro k hk y
    simp only [Acls, hclsj k hk]
    exact (iSup_finset_eq_sup' (B k) (hB_ne k hk) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqS' : ∀ y, Acls S y = ‖Φ y p‖ := by
    intro y
    simp only [Acls, hclsS]
    rw [Finset.sup'_singleton]
  have hper : ∀ y i, ‖Φ y (a i)‖ ≤ Acls S y + ∑ k ∈ Finset.range S, Acls k y := by
    intro y i
    have hsumk : ∑ k ∈ Finset.range S, Acls k y
        = ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) :=
      Finset.sum_congr rfl (fun k hk => hAeqk k (Finset.mem_range.mp hk) y)
    rw [hAeqS y, hsumk]
    have hsplit2 : Φ y (a i) = Φ y (a (q S i))
        + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i)) := by
      conv_lhs => rw [hqdecomp i]
      rw [hΦadd, hΦsum]
    calc ‖Φ y (a i)‖
        = ‖Φ y (a (q S i)) + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := by
          rw [hsplit2]
      _ ≤ ‖Φ y (a (q S i))‖
            + ‖∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := norm_add_le _ _
      _ ≤ (⨆ b ∈ cls S, ‖Φ y b‖) + ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) := by
          apply add_le_add
          · refine le_iSup_finset (cls S) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _) ?_
            rw [hqS i, hclsS]
            exact Finset.mem_singleton_self p
          · refine (norm_sum_le _ _).trans ?_
            apply Finset.sum_le_sum; intro k hk
            exact le_iSup_finset (B k) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)
              (hqdiff k (Finset.mem_range.mp hk) i)
  have hdom : ∀ y, (⨆ i : Fin (N+1), ‖Φ y (a i)‖) ≤ ∑ j ∈ Finset.range (S+1), Acls j y := by
    intro y
    rw [Finset.sum_range_succ]
    exact ciSup_le (fun i => (hper y i).trans (le_of_eq (add_comm _ _)))
  have hsup0 : ∀ y, (0:ℝ) ≤ ⨆ i : Fin (N+1), ‖Φ y (a i)‖ := by
    intro y
    have hbdd : BddAbove (Set.range (fun i : Fin (N+1) => ‖Φ y (a i)‖)) := by
      refine ⟨Acls S y + ∑ k ∈ Finset.range S, Acls k y, ?_⟩
      rintro z ⟨i, rfl⟩
      exact hper y i
    exact le_trans (norm_nonneg _) (le_ciSup hbdd 0)
  -- per-class bounds
  have hcls_bound : ∀ k, k < S →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal ((2 * (1/2:ℝ)^(S-k-1)) ^ 2
            * min (K:ℝ) (c₀ * ((B k).card : ℝ) + 1)) := by
    intro k hk
    set R : ℝ := 2 * (1/2:ℝ)^(S-k-1) with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hmemB : ∀ b ∈ B k, ∑ j : Fin K, ‖b j‖ ^ 2 ≤ R ^ 2 := by
      intro b hb
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hqBeq k ▸ hb)
      rw [hRdef]
      exact hnet2 (S-k-1) (by omega) j
    have hpt : ∀ y, Acls k y ≤ Real.sqrt (K:ℝ) * R := by
      intro y
      have hsup : Acls k y = (B k).sup' (hB_ne k hk) (fun b => ‖Φ y b‖) := by
        simp only [Acls, hclsj k hk]
      rw [hsup]
      refine Finset.sup'_le (hB_ne k hk) (fun b => ‖Φ y b‖) (fun b hb => ?_)
      have hb2 := hmemB b hb
      have hnorm : ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := by
        have h1 : ‖Φ y b‖ ≤ ∑ j : Fin K, ‖b j‖ := by
          calc ‖Φ y b‖ = ‖∑ j : Fin K, b j * expChar (lam j) y‖ := rfl
            _ ≤ ∑ j : Fin K, ‖b j * expChar (lam j) y‖ := norm_sum_le _ _
            _ = ∑ j : Fin K, ‖b j‖ := by
                apply Finset.sum_congr rfl; intro j _
                rw [norm_mul]
                have hc : ‖expChar (lam j) y‖ = 1 := by
                  unfold expChar
                  rw [Complex.norm_exp]
                  simp [Complex.ofReal_re]
                rw [hc, mul_one]
        exact h1.trans (sum_norm_le_sqrt_card_mul_sqrt_sum_sq b)
      calc ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := hnorm
        _ ≤ Real.sqrt (K:ℝ) * Real.sqrt (R^2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _)
        _ = Real.sqrt (K:ℝ) * R := by rw [Real.sqrt_sq hRpos.le]
    have hpt_int : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (K * R^2) := by
      have hstep : ∀ y : ℝ, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 := by
        intro y
        rw [← ENNReal.ofReal_pow (hAcls_nn k y) 2,
          ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hAcls_nn k y) (hpt y) 2)
      calc ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 :=
            lintegral_mono hstep
        _ = ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 * volume (Set.Ioc (0:ℝ) 1) := by
            rw [setLIntegral_const]
        _ = ENNReal.ofReal (K * R^2) := by
            rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
            rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
            congr 1
            rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (K:ℝ))]
    have hlev : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (c₀ * R^2 * ((B k).card : ℝ)) := by
      have hAeq : Acls k = fun y => (⨆ b ∈ B k, ‖Φ y b‖) := funext (fun y => hAeqk k hk y)
      rw [hAeq]
      exact hc₀ (B k) R hRpos.le hmemB
    refine le_trans (le_min hpt_int hlev) ?_
    rw [← ENNReal.ofReal_min]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (K:ℝ) (c₀ * ((B k).card : ℝ) + 1) with hle | hle
    · rw [min_eq_left hle]
      calc min (K * R^2) (c₀ * R^2 * ((B k).card : ℝ)) ≤ K * R^2 := min_le_left _ _
        _ = R^2 * K := by ring
    · rw [min_eq_right hle]
      have h2 : c₀ * R^2 * ((B k).card : ℝ) ≤ R^2 * (c₀ * ((B k).card : ℝ) + 1) := by
        nlinarith [hRpos, sq_nonneg R, (Nat.cast_nonneg ((B k).card) : (0:ℝ) ≤ ((B k).card : ℝ)),
          mul_pos hc₀pos hRpos]
      calc min (K * R^2) (c₀ * R^2 * ((B k).card : ℝ)) ≤ c₀ * R^2 * ((B k).card : ℝ) :=
            min_le_right _ _
        _ ≤ R^2 * (c₀ * ((B k).card : ℝ) + 1) := h2
  -- base (top) class bound
  have htop_bound : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls S y) ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt c₁ * D) ^ 2) := by
    have hAeq : Acls S = fun y => ‖Φ y p‖ := funext hAeqS'
    rw [hAeq]
    have hcont : Continuous (fun y : ℝ => (‖Φ y p‖) ^ 2) := (hΦcont p).norm.pow 2
    have hint : Integrable (fun y : ℝ => (‖Φ y p‖) ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hrepr : (fun y : ℝ => ENNReal.ofReal (‖Φ y p‖) ^ 2)
        = fun y : ℝ => ENNReal.ofReal ((‖Φ y p‖) ^ 2) := by
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [hrepr]
    have h2 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun y : ℝ => (‖Φ y p‖) ^ 2) hint (ae_of_all _ (fun y => sq_nonneg _))
    rw [← h2]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply ENNReal.ofReal_le_ofReal
    have hc1 := hc₁ K lam hsep p
    have hD2 : D ^ 2 = ∑ k : Fin K, ‖p k‖ ^ 2 := by
      rw [show D = Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2) from rfl,
        Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    have hcongr : (∫ y in (0:ℝ)..1, (‖Φ y p‖) ^ 2)
        = ∫ u in (0:ℝ)..1,
            ‖∑ k : Fin K, p k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro u _
      rfl
    rw [hcongr]
    calc ∫ u in (0:ℝ)..1,
          ‖∑ k : Fin K, p k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2
        ≤ c₁ * ∑ k : Fin K, ‖p k‖ ^ 2 := hc1
      _ = (Real.sqrt c₁ * D) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc₁pos.le, hD2]
  -- the weights
  let X : ℕ → ℝ := fun t => Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))
  let Tsum : ℝ := ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t
  let w : ℕ → ℝ := fun j => if j < S
      then (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
      else Real.sqrt c₁ * D
  let uu : ℕ → ℝ := fun j => w j + (1/2:ℝ)^(j+1)
  have hXnn : ∀ t, 0 ≤ X t := fun t => Real.sqrt_nonneg _
  have hwnn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j < S
    · have h1 : w j = (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
        simp only [w]; rw [if_pos hj]
      rw [h1]
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · have h1 : w j = Real.sqrt c₁ * D := by simp only [w]; rw [if_neg hj]
      rw [h1]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have huun : ∀ j, 0 ≤ uu j := fun j =>
    add_nonneg (hwnn j) (by positivity)
  have huu_pos : ∀ j ∈ Finset.range (S+1), 0 < uu j := by
    intro j _
    have h1 : 0 < (1/2:ℝ)^(j+1) := by positivity
    have h2 : 0 ≤ w j := hwnn j
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_left h2)
  have hminKnn : ∀ j, (0:ℝ) ≤ min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) := fun j =>
    le_min (by positivity) (add_nonneg (mul_nonneg hc₀pos.le (Nat.cast_nonneg _)) zero_le_one)
  have huu_bound : ∀ j ∈ Finset.range (S+1),
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls j y) ^ 2
        ≤ ENNReal.ofReal ((uu j) ^ 2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
    · have h1 : uu j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) + (1/2:ℝ)^(j+1) := by
        have hwj : w j = (2 * (1/2:ℝ)^(S-j-1))
            * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
          dsimp only [w]
          rw [if_pos hlt]
        show w j + (1/2:ℝ)^(j+1) = _
        rw [hwj]
      rw [h1]
      refine (hcls_bound j hlt).trans (ENNReal.ofReal_le_ofReal ?_)
      have hb : 0 ≤ (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hsq : ((2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))) ^ 2
          = (2 * (1/2:ℝ)^(S-j-1)) ^ 2 * min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) := by
        rw [mul_pow, Real.sq_sqrt (hminKnn j)]
      rw [← hsq]
      exact pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 2
    · rw [heq]
      have h1 : uu S = Real.sqrt c₁ * D + (1/2:ℝ)^(S+1) := by
        have hwS : w S = Real.sqrt c₁ * D := by
          dsimp only [w]
          rw [if_neg (lt_irrefl S)]
        show w S + (1/2:ℝ)^(S+1) = _
        rw [hwS]
      rw [h1]
      refine htop_bound.trans ?_
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (le_add_of_nonneg_right (by positivity)) 2
  obtain hmain := BourgainSmoothWindow.lintegral_sq_sum_le_of_class_bounds (Finset.range (S+1)) Acls uu huu_pos
    (fun j _ y => hAcls_nn j y)
    (fun j _ => ((hAcls_cont j).measurable.ennreal_ofReal.pow_const 2).aemeasurable)
    huu_bound
  have hstep1 : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
      (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (∑ j ∈ Finset.range (S+1), Acls j y) ^ 2 := by
    apply lintegral_mono
    intro y
    simp only
    have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (S+1), Acls j y :=
      Finset.sum_nonneg (fun j _ => hAcls_nn j y)
    rw [← ENNReal.ofReal_pow hsum0 2, ← ENNReal.ofReal_pow (hsup0 y) 2]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hsup0 y) (hdom y) 2)
  refine le_trans hstep1 (le_trans hmain ?_)
  apply ENNReal.ofReal_le_ofReal
  -- final numerical bound on `(∑ uu)²`
  have hDnn : 0 ≤ D := Real.sqrt_nonneg _
  have hXnn' : ∀ t, 0 ≤ X t := hXnn
  have hTsum_ge_one : 1 ≤ Tsum := by
    have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
    have hX0 : 1 ≤ X 0 := by
      have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
      have hM1 : 1 ≤ M 0 := by
        have h1 : 1 ≤ (Finset.univ.image (σ 0)).card :=
          Finset.card_pos.mpr (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)
        exact le_trans h1 (hcard 0 (by omega))
      have hM01 : (1:ℝ) ≤ (M 0 : ℝ) := by exact_mod_cast hM1
      have hmin1 : (1:ℝ) ≤ min (K:ℝ) ((M 0 : ℝ) + 1) :=
        le_min hK1 (by linarith)
      show (1:ℝ) ≤ Real.sqrt (min (K:ℝ) ((M 0 : ℝ) + 1))
      rw [Real.le_sqrt (by norm_num) (by linarith [hmin1])]
      simpa using hmin1
    calc (1:ℝ) ≤ X 0 := hX0
      _ = (1/2:ℝ)^0 * X 0 := by rw [pow_zero, one_mul]
      _ ≤ Tsum := Finset.single_le_sum (f := fun t => (1/2:ℝ)^t * X t)
          (fun t _ => mul_nonneg (by positivity) (hXnn' t)) hmem
  have hgeom : ∑ j ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - j - 1) ≤ 4 := by
    have hrefl : (∑ j ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - j - 1))
        = ∑ j ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^j := by
      rw [show (∑ j ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - j - 1))
          = ∑ j ∈ Finset.range S, (2:ℝ) * (1/2:ℝ)^(S - 1 - j) from
        Finset.sum_congr rfl (fun j _ => by rw [show S - j - 1 = S - 1 - j from by omega])]
      exact Finset.sum_range_reflect (fun j => (2:ℝ) * (1/2:ℝ)^j) S
    rw [hrefl, ← Finset.mul_sum]
    have hgs : ∑ j ∈ Finset.range S, (1/2:ℝ)^j ≤ 2 := by
      have h1 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1)) = 1 - (1/2:ℝ)^S := by
        have h3 := Finset.sum_range_sub (fun j => (1/2:ℝ)^j) S
        rw [pow_zero] at h3
        have h4 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
            = -∑ j ∈ Finset.range S, ((1/2:ℝ)^(j+1) - (1/2:ℝ)^j) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [h4, h3]; ring
      have h2 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
          = (1/2) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_succ]; ring
      rw [h2] at h1
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) S]
    linarith
  have hgeom2 : ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) ≤ 1 := by
    rw [show (∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1))
        = (1/2:ℝ) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          rw [pow_succ]; ring]
    have hgs : ∑ j ∈ Finset.range S, (1/2:ℝ)^j ≤ 2 := by
      have h1 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1)) = 1 - (1/2:ℝ)^S := by
        have h3 := Finset.sum_range_sub (fun j => (1/2:ℝ)^j) S
        rw [pow_zero] at h3
        have h4 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
            = -∑ j ∈ Finset.range S, ((1/2:ℝ)^(j+1) - (1/2:ℝ)^j) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [h4, h3]; ring
      have h2 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
          = (1/2) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_succ]; ring
      rw [h2] at h1
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) S]
    linarith
  have hBcard_le : ∀ j, j < S → (B j).card ≤ M (S-j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [Nat.sub_zero]
      exact le_trans hqcard0diff hNM
    · exact le_trans (hqcard j hjpos hj) (hcard (S-j) (by omega))
  have hwbound : ∑ j ∈ Finset.range S, w j ≤ 4 * Real.sqrt (c₀ + 1) * Tsum := by
    have hterm : ∀ j ∈ Finset.range S, w j
        ≤ 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hweq : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
        dsimp only [w]; rw [if_pos hj]
      rw [hweq]
      have h1 : Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
          ≤ Real.sqrt (c₀+1) * X (S-j) := by
        have h4 : ((B j).card : ℝ) ≤ (M (S-j) : ℝ) := by exact_mod_cast hBcard_le j hj
        have hx : c₀ * ((B j).card : ℝ) + 1 ≤ (c₀+1) * ((M (S-j) : ℝ) + 1) := by
          have hM' : (0:ℝ) ≤ (M (S-j) : ℝ) := Nat.cast_nonneg _
          have h5 := mul_le_mul_of_nonneg_left h4 hc₀pos.le
          nlinarith [h5, hM', hc₀pos]
        have hmin : min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)
            ≤ (c₀+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1) := by
          rcases le_total ((M (S-j) : ℝ) + 1) (K:ℝ) with hle | hle
          · rw [min_eq_right hle]
            exact le_trans (min_le_right _ _) hx
          · rw [min_eq_left hle]
            calc min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) ≤ (K:ℝ) := min_le_left _ _
              _ ≤ (c₀+1) * K := by nlinarith [mul_nonneg hc₀pos.le (Nat.cast_nonneg K)]
        calc Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
            ≤ Real.sqrt ((c₀+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1)) := Real.sqrt_le_sqrt hmin
          _ = Real.sqrt (c₀+1) * X (S-j) := by
              rw [Real.sqrt_mul (show (0:ℝ) ≤ c₀+1 by linarith)]
      calc (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
          ≤ (2 * (1/2:ℝ)^(S-j-1)) * (Real.sqrt (c₀+1) * X (S-j)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcongr : (∑ j ∈ Finset.range S, 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j))
        = ∑ j ∈ Finset.range S,
            2 * (1/2:ℝ)^(S-1-j) * Real.sqrt (c₀+1) * X (S-1-j+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have h4 : S - j - 1 = S - 1 - j := tsub_right_comm
      have h5 : S - j = S - 1 - j + 1 := by
        rw [← h4, Nat.sub_add_cancel (by omega : 1 ≤ S - j)]
      rw [h4, h5]
    have hrefl : (∑ j ∈ Finset.range S, 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j))
        = ∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1) := by
      rw [hcongr]
      exact Finset.sum_range_reflect
        (fun i => 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1)) S
    rw [hrefl]
    have himg : (∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1))
        = 4 * Real.sqrt (c₀+1)
          * ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [pow_succ]; ring
    rw [himg]
    have hsubset : (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t := by
      rw [Finset.sum_range_succ']
      have h0 : 0 ≤ (1/2:ℝ)^0 * X 0 := mul_nonneg (by norm_num) (hXnn' 0)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hXnn' (i+1)))
      linarith [h0, hsum0]
    calc 4 * Real.sqrt (c₀+1) * (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ 4 * Real.sqrt (c₀+1) * Tsum := by
          apply mul_le_mul_of_nonneg_left hsubset (by positivity)
      _ = 4 * Real.sqrt (c₀+1) * Tsum := rfl
  have hsum_uu : ∑ j ∈ Finset.range (S+1), uu j ≤ 100 * (c₀ + c₁ + 1) * (D + Tsum) := by
    rw [Finset.sum_range_succ]
    have hfirst : ∑ j ∈ Finset.range S, uu j
        ≤ 4 * Real.sqrt (c₀+1) * Tsum + 1 := by
      have h2 : ∑ j ∈ Finset.range S, uu j
          ≤ ∑ j ∈ Finset.range S, w j + ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) := by
        have h2' : ∑ j ∈ Finset.range S, uu j
            = ∑ j ∈ Finset.range S, (w j + (1/2:ℝ)^(j+1)) := rfl
        rw [h2', Finset.sum_add_distrib]
      linarith [h2, hwbound, hgeom2]
    have hlast : uu S ≤ Real.sqrt c₁ * D + 1 := by
      have h1 : uu S = w S + (1/2:ℝ)^(S+1) := rfl
      have hwS : w S = Real.sqrt c₁ * D := by
        dsimp only [w]; rw [if_neg (lt_irrefl S)]
      rw [h1, hwS]
      have : (1/2:ℝ)^(S+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hsqrtc01 : Real.sqrt (c₀+1) ≤ c₀ + 1 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c₀+1), Real.sqrt_nonneg (c₀+1),
        sq_nonneg (Real.sqrt (c₀+1) - 1)]
    have hsqrtc1 : Real.sqrt c₁ ≤ c₁ + 1 := by
      nlinarith [Real.sq_sqrt hc₁pos.le, Real.sqrt_nonneg c₁, sq_nonneg (Real.sqrt c₁ - 1)]
    have hDsum : 1 ≤ D + Tsum := le_trans hTsum_ge_one (le_add_of_nonneg_left hDnn)
    have hTnn : 0 ≤ Tsum := Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity) (hXnn' t))
    have hTle : Tsum ≤ D + Tsum := le_add_of_nonneg_left hDnn
    have hDle : D ≤ D + Tsum := le_add_of_nonneg_right hTnn
    nlinarith [hfirst, hlast, hsqrtc01, hsqrtc1, hDsum, hDle, hTle, hDnn, hTnn,
      Real.sqrt_nonneg (c₀+1), Real.sqrt_nonneg c₁, mul_nonneg hc₀pos.le hTnn,
      mul_nonneg (Real.sqrt_nonneg (c₀+1)) hTnn]
  have hnn : 0 ≤ ∑ j ∈ Finset.range (S+1), uu j := Finset.sum_nonneg (fun j hj => (huu_pos j hj).le)
  calc (∑ j ∈ Finset.range (S+1), uu j) ^ 2
      ≤ (100 * (c₀ + c₁ + 1) * (D + Tsum)) ^ 2 := pow_le_pow_left₀ hnn hsum_uu 2
    _ ≤ (200 * (c₀ + c₁ + 1) * (D + Tsum)) ^ 2 := by
        have hDsum0 : 0 ≤ D + Tsum := le_trans (le_trans zero_le_one hTsum_ge_one) (le_add_of_nonneg_left hDnn)
        have hnn1 : 0 ≤ 100 * (c₀ + c₁ + 1) * (D + Tsum) :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hDsum0
        have hle2 : 100 * (c₀ + c₁ + 1) * (D + Tsum) ≤ 200 * (c₀ + c₁ + 1) * (D + Tsum) := by
          nlinarith [hc₀pos, hc₁pos, hDsum0]
        exact pow_le_pow_left₀ hnn1 hle2 2


/-- **The entropy chain bound for a family that fits in a ball of radius `2`, in entropy form.** -/
theorem chain_curve_le_entropy (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ) (M : ℕ → ℕ)
        (x₀ : Fin K → ℂ),
      1 ≤ S →
      (∀ t, 1 ≤ M t) →
      (∀ i : Fin (N+1), ∑ k : Fin K, ‖a i k - x₀ k‖ ^ 2 ≤ 4) →
      (∃ σ : ℕ → Fin (N+1) → Fin (N+1),
        (∀ i : Fin (N+1), σ 0 i = σ 0 0) ∧
        (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) ∧
        ((Finset.univ.image (fun i : Fin (N+1) => a i - a (σ (S-1) i))).card : ℕ) ≤ M S ∧
        (∀ t, t ≤ S → ∀ i : Fin (N+1),
          ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2)) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
          (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    refine ⟨1, one_pos, ?_⟩
    intro N S a M x₀ hS hM1 hball hσ
    have hz : (fun y : ℝ => ENNReal.ofReal
        (⨆ i : Fin (N+1), ‖∑ k : Fin 0, a i k * expChar (lam k) y‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) := by
      funext y
      simp
    rw [hz, lintegral_zero]
    exact bot_le
  obtain ⟨c, hcpos, hc⟩ := chain_exp_sum_le_entropy K lam hsep
  refine ⟨10 * (c + 1), by positivity, ?_⟩
  intro N S a M x₀ hS hM1 hball hσ
  obtain ⟨σ, hconst, hcard, hcardD, hnet⟩ := hσ
  set i₀ : Fin (N+1) := σ 0 0 with hi₀
  -- base point comparison
  have hbase : Real.sqrt (∑ k : Fin K, ‖a i₀ k‖ ^ 2) ≤ Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2) + 2 := by
    have h1 : Real.sqrt (∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2) ≤ 2 := by
      have hb := hball i₀
      rw [show (4:ℝ) = 2 ^ 2 by norm_num] at hb
      calc Real.sqrt (∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt hb
        _ = 2 := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
    set U : ℝ := Real.sqrt (∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2) with hU
    set V : ℝ := Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2) with hV
    have hUnn : 0 ≤ U := hU ▸ Real.sqrt_nonneg _
    have hVnn : 0 ≤ V := hV ▸ Real.sqrt_nonneg _
    have hU2 : U ^ 2 = ∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2 :=
      hU ▸ Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))
    have hV2 : V ^ 2 = ∑ k : Fin K, ‖x₀ k‖ ^ 2 :=
      hV ▸ Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))
    have hpt : ∑ k : Fin K, ‖a i₀ k‖ ^ 2
        ≤ ∑ k : Fin K, (‖a i₀ k - x₀ k‖ + ‖x₀ k‖) ^ 2 := by
      apply Finset.sum_le_sum; intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc ‖a i₀ k‖ = ‖(a i₀ k - x₀ k) + x₀ k‖ := by ring_nf
        _ ≤ ‖a i₀ k - x₀ k‖ + ‖x₀ k‖ := norm_add_le _ _
    have hexp : ∑ k : Fin K, (‖a i₀ k - x₀ k‖ + ‖x₀ k‖) ^ 2
        = (∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2)
          + 2 * (∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖)
          + (∑ k : Fin K, ‖x₀ k‖ ^ 2) := by
      simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    have hcs : ∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖ ≤ U * V := by
      have h2 : (∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖) ^ 2
          ≤ (∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2) * (∑ k : Fin K, ‖x₀ k‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      rw [← hU2, ← hV2] at h2
      have h3 : 0 ≤ ∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖ :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      calc ∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖
          = Real.sqrt ((∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖) ^ 2) :=
            (Real.sqrt_sq h3).symm
        _ ≤ Real.sqrt (U ^ 2 * V ^ 2) := Real.sqrt_le_sqrt h2
        _ = U * V := by
            rw [Real.sqrt_mul (sq_nonneg U), Real.sqrt_sq hUnn, Real.sqrt_sq hVnn]
    have hsumle : ∑ k : Fin K, ‖a i₀ k‖ ^ 2 ≤ (U + V) ^ 2 := by
      calc ∑ k : Fin K, ‖a i₀ k‖ ^ 2
          ≤ ∑ k : Fin K, (‖a i₀ k - x₀ k‖ + ‖x₀ k‖) ^ 2 := hpt
        _ = (∑ k : Fin K, ‖a i₀ k - x₀ k‖ ^ 2)
              + 2 * (∑ k : Fin K, (‖a i₀ k - x₀ k‖) * ‖x₀ k‖)
              + (∑ k : Fin K, ‖x₀ k‖ ^ 2) := hexp
        _ ≤ U ^ 2 + 2 * (U * V) + V ^ 2 := by rw [← hU2, ← hV2]; linarith [hcs]
        _ = (U + V) ^ 2 := by ring
    calc Real.sqrt (∑ k : Fin K, ‖a i₀ k‖ ^ 2) ≤ Real.sqrt ((U + V) ^ 2) :=
          Real.sqrt_le_sqrt hsumle
      _ = U + V := Real.sqrt_sq (add_nonneg hUnn hVnn)
      _ ≤ Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2) + 2 := by rw [← hV]; linarith
  -- the entropy sum is at least one
  have hB1 : (1:ℝ) ≤ ∑ t ∈ Finset.range (S+1),
      (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)) := by
    have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
    have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
    have hM0 : (1:ℝ) ≤ (M 0 : ℝ) := by exact_mod_cast hM1 0
    have h5 : (1:ℝ) ≤ (1/2:ℝ)^0 * Real.sqrt (min (K:ℝ) ((M 0 : ℝ) + 1)) := by
      rw [pow_zero, one_mul]
      have h6 : (1:ℝ) ≤ min (K:ℝ) ((M 0 : ℝ) + 1) := le_min hK1 (by linarith)
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (min (K:ℝ) ((M 0 : ℝ) + 1)) := Real.sqrt_le_sqrt h6
    refine le_trans h5 (Finset.single_le_sum (s := Finset.range (S+1))
      (f := fun t => (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) ?_ hmem)
    intro t _
    exact mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t) (Real.sqrt_nonneg _)
  have hmain := hc N S a σ M hS hconst hcardD hcard hnet
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hstep1 : Real.sqrt (∑ k : Fin K, ‖a i₀ k‖ ^ 2)
      + ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))
      ≤ 3 * (Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2)
        + ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) := by
    linarith [hbase, hB1, Real.sqrt_nonneg (∑ k : Fin K, ‖x₀ k‖ ^ 2)]
  calc (c * (Real.sqrt (∑ k : Fin K, ‖a i₀ k‖ ^ 2)
        + ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2
      ≤ (c * (3 * (Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2)
          + ∑ t ∈ Finset.range (S+1),
              (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))))) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left hstep1 hcpos.le
    _ ≤ (10 * (c + 1) * (Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2)
          + ∑ t ∈ Finset.range (S+1),
              (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        have hX : (0:ℝ) ≤ Real.sqrt (∑ k : Fin K, ‖x₀ k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)) := by
          have := Finset.sum_nonneg (s := Finset.range (S+1))
            (f := fun t => (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
            (fun t _ => mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t)
              (Real.sqrt_nonneg _))
          linarith [Real.sqrt_nonneg (∑ k : Fin K, ‖x₀ k‖ ^ 2)]
        nlinarith [hcpos, hX]

end BourgainChain

namespace BourgainEntropy

/-- **Curve-point nets from an arbitrary cover.** -/
theorem exists_netmap_of_cover {N K : ℕ} (a : Fin N → Fin K → ℂ) (S : Finset (Fin K → ℂ)) {r : ℝ}
    (hr : 0 < r)
    (hcover : ∀ i : Fin N, ∃ s ∈ S, ∑ k : Fin K, ‖a i k - s k‖ ^ 2 ≤ (r / 2) ^ 2) :
    ∃ σ : Fin N → Fin N, (Finset.univ.image σ).card ≤ S.card ∧
      ∀ i : Fin N, ∑ k : Fin K, ‖a i k - a (σ i) k‖ ^ 2 ≤ r ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨fun i => i.elim0, by simp, fun i => i.elim0⟩
  let τ : Fin N → S := fun i => ⟨(hcover i).choose, (hcover i).choose_spec.1⟩
  have hτ : ∀ i, ∑ k : Fin K, ‖a i k - ((τ i : S) : Fin K → ℂ) k‖ ^ 2 ≤ (r / 2) ^ 2 :=
    fun i => (hcover i).choose_spec.2
  let κ : S → Fin N := fun s => if h : ∃ j, τ j = s then h.choose else ⟨0, hN⟩
  have hκ : ∀ s (h : ∃ j, τ j = s), τ (κ s) = s := by
    intro s h
    dsimp only [κ]
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨fun i => κ (τ i), ?_, ?_⟩
  · calc (Finset.univ.image (fun i => κ (τ i))).card
        ≤ (Finset.univ.image κ).card := Finset.card_le_card (by
          intro j hj
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
          exact Finset.mem_image.mpr ⟨τ i, Finset.mem_univ _, rfl⟩)
      _ ≤ S.card := by
          calc (Finset.univ.image κ).card ≤ (Finset.univ : Finset S).card := Finset.card_image_le
            _ = S.card := by rw [Finset.card_univ, Fintype.card_coe]
  · intro i
    have h1 := hτ i
    have h2 : κ (τ i) = κ (τ i) := rfl
    have hτκ : τ (κ (τ i)) = τ i := hκ (τ i) ⟨i, rfl⟩
    have hcent : ((τ (κ (τ i)) : S) : Fin K → ℂ) = ((τ i : S) : Fin K → ℂ) := by
      rw [hτκ]
    have h3 : ∑ k : Fin K, ‖a (κ (τ i)) k - ((τ i : S) : Fin K → ℂ) k‖ ^ 2 ≤ (r / 2) ^ 2 := by
      rw [← hcent]
      exact hτ (κ (τ i))
    have h4 : ∑ k : Fin K, ‖a i k - a (κ (τ i)) k‖ ^ 2
        ≤ 2 * ∑ k : Fin K, ‖a i k - ((τ i : S) : Fin K → ℂ) k‖ ^ 2
          + 2 * ∑ k : Fin K, ‖a (κ (τ i)) k - ((τ i : S) : Fin K → ℂ) k‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro k _
      have h5 : a i k - a (κ (τ i)) k
          = (a i k - ((τ i : S) : Fin K → ℂ) k)
            + (((τ i : S) : Fin K → ℂ) k - a (κ (τ i)) k) := by ring
      have key : ∀ x y : ℂ, ‖x + (-y)‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
        intro x y
        have hle := norm_add_le x (-y)
        rw [norm_neg] at hle
        refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hle 2) ?_
        nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
      have h6 : ((τ i : S) : Fin K → ℂ) k - a (κ (τ i)) k
          = -(a (κ (τ i)) k - ((τ i : S) : Fin K → ℂ) k) := by ring
      rw [h5, h6]
      exact key _ _
    have hr2 : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
    nlinarith [h4, h1, h3]

end BourgainEntropy


namespace BourgainMax

open _root_.MeasureTheory

/-- The dyadic window scale `h_j = 2^{-j-1}`. -/
noncomputable def winScale (j : ℕ) : ℝ := (2:ℝ) ^ (-(j:ℝ) - 1)

lemma winScale_pos (j : ℕ) : 0 < winScale j := Real.rpow_pos_of_pos (by norm_num) _

lemma inv_winScale_pos (j : ℕ) : 0 < (winScale j)⁻¹ := inv_pos.mpr (winScale_pos j)

/-- The `L¹`-normalised dilation `h_j · Ψ(h_j ·)` of the window `Ψ`. -/
noncomputable def winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ → ℂ :=
  fun u => ((winScale j : ℝ) : ℂ) * Ψ (winScale j * u)

/-- The band-pass operator at the dyadic scale `j`. -/
noncomputable def bandScaleOpJ (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
    (∫ y : ℝ, H k y * winK Ψ j (x - y))

/-- The continuum version (used only to invoke the published dilation maximal estimate). -/
noncomputable def bandScaleOpC (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (t : {t : ℝ // 0 < t}) (x : ℝ) : ℂ :=
  ∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
    (∫ y : ℝ, H k y * ((t:ℝ)⁻¹ • Ψ ((x - y) / (t:ℝ))))

/-- The `ℓ²`-energy of the tuple `H`. -/
noncomputable def bandSq {K : ℕ} (H : Fin K → ℝ → ℂ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2)

/-- The maximal band-pass operator over the dyadic scales. -/
noncomputable def bandMax (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) : ENNReal :=
  ∫⁻ x, (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam H j x‖ₑ) ^ (2:ℝ)

/-- Translation of the tuple `H` by `y`. -/
noncomputable def transl {K : ℕ} (H : Fin K → ℝ → ℂ) (y : ℝ) : Fin K → ℝ → ℂ :=
  fun k u => H k (u + y)

/-- The dyadic operator is the continuum operator at `t = h_j⁻¹`. -/
lemma bandScaleOpJ_eq_C (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (j : ℕ) (x : ℝ) :
    bandScaleOpJ Ψ lam H j x
      = bandScaleOpC Ψ lam H ⟨(winScale j)⁻¹, inv_winScale_pos j⟩ x := by
  unfold bandScaleOpJ bandScaleOpC
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  rw [winK, inv_inv, div_inv_eq_mul, mul_comm (x - y) (winScale j), Complex.real_smul]

/-- **A priori bound.** -/
theorem bandMax_apriori (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Fin K → ℝ → ℂ), (∀ k, MemLp (H k) 2 (volume : Measure ℝ)) →
      bandMax Ψ lam H ≤ ENNReal.ofReal (C * (K:ℝ)) * bandSq H := by
  obtain ⟨C, hC, h⟩ := lintegral_iSup_band_sum_dilation_le K lam Ψ
  refine ⟨C, hC, fun H hH => ?_⟩
  refine le_trans ?_ (h H hH)
  rw [bandMax]
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 2)
  refine iSup_le fun j => ?_
  rw [bandScaleOpJ_eq_C]
  exact le_iSup (fun t : {t : ℝ // 0 < t} => ‖bandScaleOpC Ψ lam H t x‖ₑ) _

private lemma ENNReal_sq_add_le (p q : ENNReal) :
    (p + q) ^ (2:ℝ) ≤ 2 * p ^ (2:ℝ) + 2 * q ^ (2:ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two, pow_two, pow_two, pow_two]
  rcases eq_or_ne p ⊤ with hp | hp
  · subst hp
    rcases eq_or_ne q ⊤ with hq | hq
    · subst hq; simp
    · have h2 : (⊤:ENNReal) + q = ⊤ := top_add q
      rw [h2]; simp [ENNReal.mul_top (by norm_num : (2:ENNReal) ≠ 0)]
  · rcases eq_or_ne q ⊤ with hq | hq
    · subst hq
      have h2 : p + (⊤:ENNReal) = ⊤ := add_top p
      rw [h2]; simp [ENNReal.mul_top (by norm_num : (2:ENNReal) ≠ 0)]
    · have ha : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      have hb : 0 ≤ q.toReal := ENNReal.toReal_nonneg
      rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_toReal hq, ← ENNReal.ofReal_add ha hb]
      have hs : (0:ℝ) ≤ p.toReal + q.toReal := by positivity
      rw [← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb]
      rw [show (2:ENNReal) = ENNReal.ofReal (2:ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg (p.toReal - q.toReal)]

lemma bandSq_eq_sum {K : ℕ} (H : Fin K → ℝ → ℂ) (hH : ∀ k, Measurable (H k)) :
    bandSq H = ∑ k : Fin K, ∫⁻ x, ‖H k x‖ₑ ^ (2:ℝ) := by
  rw [bandSq, ← lintegral_finsetSum]
  · apply lintegral_congr; intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two])
  · intro k _
    exact (hH k).enorm.pow_const 2

lemma integrable_mul_winK (Ψ : SchwartzMap ℝ ℂ) {G : ℝ → ℂ} (hG : Integrable G)
    (j : ℕ) (x : ℝ) :
    Integrable (fun y => G y * winK Ψ j (x - y)) := by
  obtain ⟨C, hCpos, hC⟩ := Ψ.decay 0 0
  refine Integrable.mul_bdd hG ?_ (c := winScale j * C) ?_
  · refine (Continuous.mul continuous_const ?_).aestronglyMeasurable
    exact Ψ.continuous.comp (by fun_prop : Continuous fun y : ℝ => winScale j * (x - y))
  · filter_upwards with y
    rw [winK, norm_mul, Complex.norm_real, Real.norm_of_nonneg (winScale_pos j).le]
    exact mul_le_mul_of_nonneg_left (by simpa using hC (winScale j * (x - y))) (winScale_pos j).le

/-- **Energy contraction.** -/
theorem bandSq_translate_sub_le {K : ℕ} (H : Fin K → ℝ → ℂ) {y a : ℝ} (ha : 0 ≤ a)
    (hH1 : ∀ k, Integrable (H k)) (hH2 : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hHm : ∀ k, Measurable (H k)) (hsupp : ∀ k ξ, a < |ξ| → 𝓕 (H k) ξ = 0) :
    bandSq (fun k u => H k (u + y) - H k u)
      ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * bandSq H := by
  have hmm : ∀ k : Fin K, Measurable (fun u : ℝ => H k (u + y) - H k u) :=
    fun k => ((hHm k).comp (measurable_id.add_const y)).sub (hHm k)
  rw [bandSq_eq_sum (fun k u => H k (u + y) - H k u) hmm, bandSq_eq_sum H hHm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact lintegral_translate_sub_sq_le_of_fourier_support (hH1 k) (hH2 k) ha (hsupp k)

/-- **Subadditivity.** -/
theorem bandMax_subadd (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (y : ℝ)
    (hH1 : ∀ k, Integrable (H k)) (hH2 : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hP : AEMeasurable (fun x : ℝ => (⨆ j : ℕ,
      ‖bandScaleOpJ Ψ lam (transl H y) j x‖ₑ) ^ (2:ℝ))) :
    bandMax Ψ lam H
      ≤ 2 * bandMax Ψ lam (transl H y)
        + 2 * bandMax Ψ lam (fun k u => H k u - H k (u + y)) := by
  have hshift : ∀ k : Fin K, Integrable (fun u => H k (u + y)) := fun k =>
    ((measurePreserving_add_right (volume : Measure ℝ) y).integrable_comp
      (hH1 k).aestronglyMeasurable).mpr (hH1 k)
  have hpt : ∀ j : ℕ, ∀ x : ℝ,
      bandScaleOpJ Ψ lam H j x
        = bandScaleOpJ Ψ lam (transl H y) j x
          + bandScaleOpJ Ψ lam (fun k u => H k u - H k (u + y)) j x := by
    intro j x
    have hk : ∀ k : Fin K,
        (∫ y', (H k y' - H k (y' + y)) * winK Ψ j (x - y'))
          = (∫ y', H k y' * winK Ψ j (x - y'))
            - (∫ y', H k (y' + y) * winK Ψ j (x - y')) := by
      intro k
      rw [← integral_sub (integrable_mul_winK Ψ (hH1 k) j x)
        (integrable_mul_winK Ψ (hshift k) j x)]
      apply integral_congr_ae; filter_upwards with y'; ring_nf
    simp only [bandScaleOpJ, transl]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hk k, mul_sub]
    ring
  set P : ℝ → ENNReal := fun x => (⨆ j : ℕ,
      ‖bandScaleOpJ Ψ lam (transl H y) j x‖ₑ) ^ (2:ℝ) with hPdef
  set Q : ℝ → ENNReal := fun x => (⨆ j : ℕ,
      ‖bandScaleOpJ Ψ lam (fun k u => H k u - H k (u + y)) j x‖ₑ) ^ (2:ℝ) with hQdef
  have hP' : AEMeasurable P := hP
  have hstep : bandMax Ψ lam H ≤ ∫⁻ x, (2 * P x + 2 * Q x) := by
    rw [bandMax]
    apply lintegral_mono; intro x
    rw [hPdef, hQdef]
    calc (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam H j x‖ₑ) ^ (2:ℝ)
        = (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam (transl H y) j x
            + bandScaleOpJ Ψ lam (fun k u => H k u - H k (u + y)) j x‖ₑ) ^ (2:ℝ) := by
          congr 1; apply iSup_congr; intro j; rw [hpt j x]
      _ ≤ ((⨆ j : ℕ, ‖bandScaleOpJ Ψ lam (transl H y) j x‖ₑ)
            + (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam (fun k u => H k u - H k (u + y)) j x‖ₑ)) ^ (2:ℝ) := by
          apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 2)
          refine iSup_le fun j => ?_
          exact le_trans (_root_.enorm_add_le _ _)
            (add_le_add (le_iSup (fun j => ‖bandScaleOpJ Ψ lam (transl H y) j x‖ₑ) j)
              (le_iSup (fun j => ‖bandScaleOpJ Ψ lam (fun k u => H k u - H k (u + y)) j x‖ₑ) j))
      _ ≤ 2 * (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam (transl H y) j x‖ₑ) ^ (2:ℝ)
            + 2 * (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam (fun k u => H k u - H k (u + y)) j x‖ₑ) ^ (2:ℝ) :=
          ENNReal_sq_add_le _ _
  refine le_trans hstep ?_
  have hstep2 : (∫⁻ x, (2 * P x + 2 * Q x)) = 2 * ∫⁻ x, (P x + Q x) := by
    rw [show (fun x => 2 * P x + 2 * Q x) = fun x => 2 * (P x + Q x) from by
      funext x; ring]
    exact lintegral_const_mul' 2 _ (by norm_num)
  rw [hstep2, lintegral_add_left' hP', mul_add, bandMax, bandMax]

end BourgainMax


namespace BourgainMax

open _root_.MeasureTheory

/-- The phased curve point `j ↦ (e^{-Iλ_k z}(H_k * winK_j)(z))_k`. -/
noncomputable def curvePtJ (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ) : Fin K → ℂ :=
  fun k => Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ))) *
    (∫ v : ℝ, H k v * winK Ψ j (z - v))

/-- **u-averaging.**  The translated band operator is the phase-twisted translated curve point:
`A_j(T_y H)(x) = Σ_k e^{Iλ_k y} curvePt_j(x+y)`. -/
theorem bandScaleOpJ_transl (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (y : ℝ) (j : ℕ) (x : ℝ) :
    bandScaleOpJ Ψ lam (transl H y) j x
      = ∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) *
          curvePtJ Ψ lam H j (x + y) k := by
  unfold bandScaleOpJ transl curvePtJ
  apply Finset.sum_congr rfl
  intro k _
  have hcv : (∫ u, H k (u+y) * winK Ψ j (x-u)) = ∫ v, H k v * winK Ψ j ((x+y)-v) := by
    have key : (∫ u, H k (u+y) * winK Ψ j (x-u))
        = ∫ u, (fun w : ℝ => H k w * winK Ψ j ((x+y) - w)) (u+y) := by
      apply integral_congr_ae; filter_upwards with u
      have harg : (x+y) - (u+y) = x - u := by ring
      rw [harg]
    rw [key]
    exact integral_add_right_eq_self (fun w : ℝ => H k w * winK Ψ j ((x+y) - w)) y
  rw [hcv, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

end BourgainMax


namespace BourgainMax

open _root_.MeasureTheory

private lemma cast_max' (c : ℕ) : ((max 1 c : ℕ) : ENNReal) = max (1:ENNReal) (c:ENNReal) := by
  rcases max_cases 1 c with ⟨h, hc⟩ | ⟨h, hc⟩
  · rw [h, Nat.cast_one]; exact (max_eq_left (by exact_mod_cast hc)).symm
  · rw [h]; exact (max_eq_right (by exact_mod_cast (le_of_lt hc))).symm

/-- Splitting a natural-number `max` inside `ℝ≥0∞` (the `max 1 _` case is `cast_max'`). -/
private lemma cast_max'' (a b : ℕ) : ((max a b : ℕ) : ENNReal) = max (a : ENNReal) (b : ENNReal) := by
  rcases max_cases a b with ⟨h, hc⟩ | ⟨h, hc⟩
  · rw [h]; exact (max_eq_left (by exact_mod_cast hc)).symm
  · rw [h]; exact (max_eq_right (by exact_mod_cast (le_of_lt hc))).symm

/-- **Pointwise-in-`x` entropy chain for the maximal exponential sum.**  If the family `a` lies in
an `ℓ²`-ball of radius `2` around `x₀` and carries chain nets `σ t` with cardinalities dominated
by an antitone entropy function `E`, then the `y`-integral of the maximal exponential sum is
controlled by the base point plus the entropy integral. -/
theorem chain_curvePt_bound (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J S : ℕ) (a : Fin (J+1) → Fin K → ℂ) (σ : ℕ → Fin (J+1) → Fin (J+1))
        (x₀ : Fin K → ℂ) (E : ℝ → ENNReal),
      1 ≤ S →
      (∀ i : Fin (J+1), ∑ k : Fin K, ‖a i k - x₀ k‖^2 ≤ 4) →
      (∀ r r' : ℝ, 0 < r → r ≤ r' → E r' ≤ E r) → (1 : ENNReal) ≤ E 1 →
      (∀ i : Fin (J+1), σ 0 i = σ 0 0) →
      (((Finset.univ.image (fun j : Fin (J+1) => a j - a (σ (S-1) j))).card : ENNReal)
        ≤ E ((1/2:ℝ)^S)) →
      (∀ t, t ≤ S → ((Finset.univ.image (σ t)).card : ENNReal) ≤ E ((1/2:ℝ)^t)) →
      (∀ t, t ≤ S → ∀ i : Fin (J+1), ∑ k : Fin K, ‖a i k - a (σ t i) k‖^2 ≤ (2*(1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1,
          ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖)^2
        ≤ ENNReal.ofReal (C^2) *
            (ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖x₀ k‖^2))
              + 2 * ∫⁻ r in Set.Ioc (0:ℝ) 1,
                  min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r + 1)^(1/2:ℝ)))^2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := BourgainChain.chain_curve_le_entropy K lam hsep
  refine ⟨C₀, hC₀pos, ?_⟩
  intro J S a σ x₀ E hS hball hEanti hE1 hσ0 hcardS hcard hnet
  set D0 : ℕ := (Finset.univ.image (fun j : Fin (J+1) => a j - a (σ (S-1) j))).card with hD0
  set M : ℕ → ℕ := fun t => if t ≤ S then max 1 (max ((Finset.univ.image (σ t)).card)
    (if t = S then D0 else (0 : ℕ))) else 1 with hM
  have hM1 : ∀ t, 1 ≤ M t := by
    intro t
    rw [hM]
    dsimp only
    by_cases ht : t ≤ S
    · rw [if_pos ht]; exact le_max_left _ _
    · rw [if_neg ht]
  have hMcard : ∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t := by
    intro t ht
    rw [hM]
    dsimp only
    rw [if_pos ht]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hMS : D0 ≤ M S := by
    rw [hM]
    dsimp only
    rw [if_pos (le_refl S), if_pos rfl]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hD0E : (D0 : ENNReal) ≤ E ((1/2:ℝ)^S) := by rw [hD0]; exact hcardS
  have hME : ∀ t : ℕ, (M t : ENNReal) ≤ E ((1/2:ℝ)^t) := by
    intro t
    rw [hM]
    dsimp only
    by_cases ht : t ≤ S
    · rw [if_pos ht, cast_max']
      refine max_le ?_ ?_
      · exact le_trans hE1 (hEanti ((1/2:ℝ)^t) 1 (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num)))
      · rw [cast_max'']
        refine max_le (hcard t ht) ?_
        by_cases htS : t = S
        · subst htS; rw [if_pos rfl]; exact hD0E
        · rw [if_neg htS]; simp
    · rw [if_neg ht]
      simpa using le_trans hE1 (hEanti ((1/2:ℝ)^t) 1 (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num)))
  have hchain := hC₀ J S a M x₀ hS hM1 hball
    ⟨σ, hσ0, fun t ht => hMcard t ht, by rw [← hD0]; exact hMS, fun t ht i => hnet t ht i⟩
  have hdyad := Commons.Analysis.Real.ofReal_sum_dyadic_le_lintegral_entropy_Ioc E hEanti K M hME S
  set X : ℝ := Real.sqrt (∑ k : Fin K, ‖x₀ k‖^2) with hX
  set Y : ℝ := ∑ t ∈ Finset.range (S + 1),
      (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t:ℝ) + 1)) with hY
  set I : ENNReal := ∫⁻ r in Set.Ioc (0:ℝ) 1,
      min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r + 1)^(1/2:ℝ)) with hI
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun t _ =>
    mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
  have hdyad' : ENNReal.ofReal Y ≤ 2 * I := by rw [hY, hI]; exact hdyad
  calc ∫⁻ y in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖)^2
      ≤ ENNReal.ofReal ((C₀ * (X + Y))^2) := by rw [hX, hY]; exact hchain
    _ = ENNReal.ofReal (C₀^2) * ENNReal.ofReal ((X + Y)^2) := by
        rw [show (C₀ * (X + Y))^2 = C₀^2 * (X + Y)^2 by ring,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₀^2),
          ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ C₀) 2]
    _ = ENNReal.ofReal (C₀^2) * (ENNReal.ofReal (X + Y))^2 := by
        rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ X + Y) 2]
    _ = ENNReal.ofReal (C₀^2) * (ENNReal.ofReal X + ENNReal.ofReal Y)^2 := by
        rw [ENNReal.ofReal_add hX0 hY0]
    _ ≤ ENNReal.ofReal (C₀^2) * (ENNReal.ofReal X + 2 * I)^2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left' (add_le_add le_rfl hdyad') 2) (bot_le)

end BourgainMax

namespace BourgainMax

open _root_.MeasureTheory

/-- **Division commutes with a finite supremum of reals.**  (Not `ciSup_div`, which needs a
multiplicative group; `ℝ` is only a `GroupWithZero`.) -/
lemma iSup_div_eq' {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) {D : ℝ} (hD : 0 < D) :
    (⨆ i, f i) / D = ⨆ i, f i / D := by
  have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  have hbdd2 : BddAbove (Set.range (fun i => f i / D)) := (Set.finite_range _).bddAbove
  have h1 : (⨆ i, f i) / D ≤ ⨆ i, f i / D := by
    rw [div_le_iff₀ hD]
    refine ciSup_le (fun i => ?_)
    rw [show f i = (f i / D) * D from by field_simp]
    exact mul_le_mul_of_nonneg_right (le_ciSup hbdd2 i) hD.le
  have h2 : (⨆ i, f i / D) ≤ (⨆ i, f i) / D :=
    ciSup_le (fun i => div_le_div_of_nonneg_right (le_ciSup hbdd i) hD.le)
  exact le_antisymm h1 h2

/-- Norm of a complex number divided by a positive real. -/
private lemma norm_div_real'' (z : ℂ) {D : ℝ} (hD : 0 < D) : ‖z / (D:ℂ)‖ = ‖z‖ / D := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hD.le]

/-- **Scaling identity for the maximal exponential sum.** -/
lemma iSup_expSum_div' {K : ℕ} (lam : Fin K → ℝ) {J : ℕ} (a : Fin (J+1) → Fin K → ℂ)
    (y : ℝ) {D : ℝ} (hD : 0 < D) :
    (⨆ i : Fin (J+1), ‖∑ k : Fin K, (a i k / (D:ℂ)) * expChar (lam k) y‖)
      = (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖) / D := by
  have h1 : ∀ i : Fin (J+1), ‖∑ k : Fin K, (a i k / (D:ℂ)) * expChar (lam k) y‖
      = ‖∑ k : Fin K, a i k * expChar (lam k) y‖ / D := by
    intro i
    have he : (∑ k : Fin K, (a i k / (D:ℂ)) * expChar (lam k) y)
        = (∑ k : Fin K, a i k * expChar (lam k) y) / (D:ℂ) := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro k _; ring
    rw [he, norm_div_real'' _ hD]
  refine (iSup_congr h1).trans ?_
  exact (iSup_div_eq' (fun i : Fin (J+1) =>
    ‖∑ k : Fin K, a i k * expChar (lam k) y‖) hD).symm

/-- **Rescaling of the `ofReal`-square.** -/
lemma ofReal_div_sq {x D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) :
    ENNReal.ofReal x ^ 2 = ENNReal.ofReal (D^2) * ENNReal.ofReal (x / D) ^ 2 := by
  rw [← ENNReal.ofReal_pow hx 2,
    show x^2 = D^2 * (x/D)^2 by field_simp,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ D^2),
    ENNReal.ofReal_pow (div_nonneg hx hD.le) 2]

/-- **Rescaling of the `ℓ²`-norm.** -/
lemma sqrt_sum_div {K : ℕ} (x : Fin K → ℂ) {D : ℝ} (hD : 0 < D) :
    Real.sqrt (∑ k : Fin K, ‖x k / (D:ℂ)‖^2)
      = Real.sqrt (∑ k : Fin K, ‖x k‖^2) / D := by
  have h1 : ∀ k : Fin K, ‖x k / (D:ℂ)‖^2 = ‖x k‖^2 / D^2 := by
    intro k; rw [norm_div_real'' _ hD, div_pow]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.sum_div]
  rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ ∑ k : Fin K, ‖x k‖^2), Real.sqrt_sq hD.le]

end BourgainMax

namespace BourgainMax

open _root_.MeasureTheory

/-- **Pointwise-in-`x` entropy chain, general radius `D`.** -/
theorem chain_curvePt_bound_scaled (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J S : ℕ) (a : Fin (J+1) → Fin K → ℂ) (σ : ℕ → Fin (J+1) → Fin (J+1))
        (x₀ : Fin K → ℂ) (D : ℝ) (E : ℝ → ENNReal),
      0 < D → 1 ≤ S →
      (∀ i : Fin (J+1), ∑ k : Fin K, ‖a i k - x₀ k‖^2 ≤ D^2) →
      (∀ r r' : ℝ, 0 < r → r ≤ r' → E r' ≤ E r) → (1 : ENNReal) ≤ E 1 →
      (∀ i : Fin (J+1), σ 0 i = σ 0 0) →
      (((Finset.univ.image (fun j : Fin (J+1) => a j - a (σ (S-1) j))).card : ENNReal)
        ≤ E ((1/2:ℝ)^S)) →
      (∀ t, t ≤ S → ((Finset.univ.image (σ t)).card : ENNReal) ≤ E ((1/2:ℝ)^t)) →
      (∀ t, t ≤ S → ∀ i : Fin (J+1), ∑ k : Fin K, ‖a i k - a (σ t i) k‖^2 ≤ (2*D*(1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1,
          ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖)^2
        ≤ ENNReal.ofReal (C^2) *
            (ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖x₀ k‖^2))
              + ENNReal.ofReal D * (2 * ∫⁻ r in Set.Ioc (0:ℝ) 1,
                  min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r + 1)^(1/2:ℝ))))^2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := chain_curvePt_bound K lam hsep
  refine ⟨C₀, hC₀pos, ?_⟩
  intro J S a σ x₀ D E hD hS hball hEanti hE1 hσ0 hcardS hcard hnet
  set a' : Fin (J+1) → Fin K → ℂ := fun i k => a i k / (D:ℂ) with ha'
  set x' : Fin K → ℂ := fun k => x₀ k / (D:ℂ) with hx'
  -- (i) the rescaled family lies in a ball of radius 2
  have hball' : ∀ i : Fin (J+1), ∑ k : Fin K, ‖a' i k - x' k‖^2 ≤ 4 := by
    intro i
    have h1 : ∀ k : Fin K, ‖a' i k - x' k‖^2 = ‖a i k - x₀ k‖^2 / D^2 := by
      intro k
      have he : a' i k - x' k = (a i k - x₀ k) / (D:ℂ) := by rw [ha', hx']; ring
      rw [he, norm_div_real'' _ hD, div_pow]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.sum_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < D^2)]
    nlinarith [hball i, sq_nonneg D]
  -- (ii) the rescaled family satisfies the chain net property
  have hnet' : ∀ t, t ≤ S → ∀ i : Fin (J+1),
      ∑ k : Fin K, ‖a' i k - a' (σ t i) k‖^2 ≤ (2*(1/2:ℝ)^t)^2 := by
    intro t ht i
    have h1 : ∀ k : Fin K, ‖a' i k - a' (σ t i) k‖^2 = ‖a i k - a (σ t i) k‖^2 / D^2 := by
      intro k
      have he : a' i k - a' (σ t i) k = (a i k - a (σ t i) k) / (D:ℂ) := by rw [ha']; ring
      rw [he, norm_div_real'' _ hD, div_pow]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.sum_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < D^2)]
    refine le_trans (hnet t ht i) (le_of_eq ?_)
    ring
  -- (iii) the unscaled chain bound
  have hDc : (D:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  set Dc : Fin K → ℂ := fun _ => (D:ℂ) with hDc'
  have hpt0 : ∀ i : Fin (J+1), a' i - a' (σ (S-1) i) = (a i - a (σ (S-1) i)) / Dc := by
    intro i
    funext k
    simp only [ha', hDc', Pi.sub_apply, Pi.div_apply]
    ring
  have hinj0 : Function.Injective (fun z : Fin K → ℂ => z / Dc) := by
    intro z w hz
    funext k
    have h : z k / (D:ℂ) = w k / (D:ℂ) := by
      have h1 := congrFun hz k
      simpa [hDc', Pi.div_apply] using h1
    have h2 : z k / (D:ℂ) * (D:ℂ) = w k / (D:ℂ) * (D:ℂ) := by rw [h]
    simpa [div_mul_cancel₀ _ hDc] using h2
  have hcardS' : ((Finset.univ.image (fun i : Fin (J+1) => a' i - a' (σ (S-1) i))).card : ENNReal)
      ≤ E ((1/2:ℝ)^S) := by
    have himg : (Finset.univ.image (fun i : Fin (J+1) => a' i - a' (σ (S-1) i)))
        = (Finset.univ.image (fun i : Fin (J+1) => a i - a (σ (S-1) i))).image
            (fun z : Fin K → ℂ => z / Dc) := by
      rw [Finset.image_image]
      refine Finset.image_congr (fun i _ => ?_)
      simpa using hpt0 i
    have hcard_eq : (Finset.univ.image (fun i : Fin (J+1) => a' i - a' (σ (S-1) i))).card
        = (Finset.univ.image (fun i : Fin (J+1) => a i - a (σ (S-1) i))).card := by
      rw [himg]
      exact Finset.card_image_of_injective _ hinj0
    rw [hcard_eq]; exact hcardS
  have hchain := hC₀ J S a' σ x' E hS hball' hEanti hE1 hσ0 hcardS' hcard hnet'
  -- (iv) the base point rescales
  have hbase : Real.sqrt (∑ k : Fin K, ‖x' k‖^2) = Real.sqrt (∑ k : Fin K, ‖x₀ k‖^2) / D := by
    rw [hx']; exact sqrt_sum_div x₀ hD
  -- (v) the pointwise rescaling of the integrand
  have hpt : ∀ y : ℝ, ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖)^2
      = ENNReal.ofReal (D^2) *
        ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a' i k * expChar (lam k) y‖)^2 := by
    intro y
    have hs' : (⨆ i : Fin (J+1), ‖∑ k : Fin K, a' i k * expChar (lam k) y‖)
        = (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖) / D := by
      rw [ha']; exact iSup_expSum_div' lam a y hD
    rw [hs']
    exact ofReal_div_sq (Real.iSup_nonneg (fun i => norm_nonneg _)) hD
  -- (vi) the `y`-integral rescales
  set I : ENNReal := 2 * ∫⁻ r in Set.Ioc (0:ℝ) 1,
      min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r + 1)^(1/2:ℝ)) with hI
  set Y : ENNReal := ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖x' k‖^2)) + I with hY
  have hchain' : ∫⁻ y in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a' i k * expChar (lam k) y‖)^2
      ≤ ENNReal.ofReal (C₀^2) * Y^2 := by rw [hY, hI]; exact hchain
  have hkey : ∫⁻ y in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a i k * expChar (lam k) y‖)^2
      = ENNReal.ofReal (D^2) * ∫⁻ y in Set.Ioc (0:ℝ) 1,
          ENNReal.ofReal (⨆ i : Fin (J+1), ‖∑ k : Fin K, a' i k * expChar (lam k) y‖)^2 := by
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- (vii) assemble
  have hD2 : ENNReal.ofReal (D^2) * (ENNReal.ofReal (C₀^2) * Y^2)
      = ENNReal.ofReal (C₀^2) * (ENNReal.ofReal D * Y)^2 := by
    rw [mul_pow, ENNReal.ofReal_pow hD.le 2]; ring
  have hYeq : ENNReal.ofReal D * Y
      = ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖x₀ k‖^2)) + ENNReal.ofReal D * I := by
    rw [hY, mul_add, hbase, ← ENNReal.ofReal_mul hD.le, mul_div_cancel₀ _ (ne_of_gt hD)]
  rw [hkey]
  refine le_trans (mul_le_mul_of_nonneg_left hchain' bot_le) ?_
  rw [hD2, hYeq, hI]

end BourgainMax

namespace BourgainMax

open _root_.MeasureTheory

/-- **Chain nets from covers.** -/
lemma exists_chain_nets {K J S : ℕ} (hS : 1 ≤ S) (a : Fin (J+1) → Fin K → ℂ) {D : ℝ}
    (hD : 0 < D) (Sc : ℕ → Finset (Fin K → ℂ))
    (hcov : ∀ t, 1 ≤ t → t ≤ S → ∀ i : Fin (J+1),
      ∃ s ∈ Sc t, ∑ k : Fin K, ‖a i k - s k‖^2 ≤ (D*(1/2:ℝ)^t)^2) :
    ∃ σ : ℕ → Fin (J+1) → Fin (J+1),
      (σ S = fun i => i) ∧ (∀ i : Fin (J+1), σ 0 i = σ 0 0) ∧
      (∀ t, 1 ≤ t → t ≤ S → ∀ i : Fin (J+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖^2 ≤ (2*D*(1/2:ℝ)^t)^2) ∧
      (∀ t, 1 ≤ t → t < S → ((Finset.univ.image (σ t)).card : ℕ) ≤ (Sc t).card) := by
  classical
  have h0 : 0 < J + 1 := Nat.succ_pos J
  have hnet : ∀ t, 1 ≤ t → t ≤ S → ∃ σ : Fin (J+1) → Fin (J+1),
      ((Finset.univ.image σ).card : ℕ) ≤ (Sc t).card ∧
      ∀ i, ∑ k : Fin K, ‖a i k - a (σ i) k‖^2 ≤ (2*D*(1/2:ℝ)^t)^2 := by
    intro t ht htS
    have hr : (0:ℝ) < 2*D*(1/2:ℝ)^t := by positivity
    obtain ⟨σ, hc, hn⟩ := BourgainEntropy.exists_netmap_of_cover a (Sc t) hr
      (fun i => by
        obtain ⟨s, hs, hb⟩ := hcov t ht htS i
        exact ⟨s, hs, by rwa [show D*(1/2:ℝ)^t = 2*D*(1/2:ℝ)^t/2 by ring] at hb⟩)
    exact ⟨σ, hc, hn⟩
  let σ : ℕ → Fin (J+1) → Fin (J+1) := fun t =>
    match t with
    | 0 => fun _ => ⟨0, h0⟩
    | (k+1) => if h : (k+1) = S then id
               else if hle : (k+1) ≤ S then
                 (hnet (k+1) (Nat.succ_le_succ (Nat.zero_le k)) hle).choose
               else id
  have hsigS : σ S = id := by
    cases hSc : S with
    | zero => omega
    | succ k =>
        simp only [σ]
        rw [dif_pos hSc.symm]
  refine ⟨σ, hsigS, ?_, ?_, ?_⟩
  · intro i; rfl
  · intro t ht htS i
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    by_cases hEq : k + 1 = S
    · have hsig : σ (k+1) = id := by rw [hEq]; exact hsigS
      rw [hsig]
      simp only [id_eq]
      have hz : ∑ k : Fin K, ‖a i k - a i k‖^2 = 0 := by
        apply Finset.sum_eq_zero; intro k _; simp
      rw [hz]; positivity
    · have hle : k + 1 ≤ S := by omega
      simp only [σ]; rw [dif_neg hEq, dif_pos hle]
      exact (hnet (k+1) (Nat.succ_le_succ (Nat.zero_le k)) hle).choose_spec.2 i
  · intro t ht htS'
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    have hne : k + 1 ≠ S := by omega
    have hle : k + 1 ≤ S := by omega
    simp only [σ]; rw [dif_neg hne, dif_pos hle]
    exact (hnet (k+1) (Nat.succ_le_succ (Nat.zero_le k)) hle).choose_spec.1

end BourgainMax

namespace BourgainMax

open _root_.MeasureTheory

/-- The unphased window curve point at the dyadic scale `j`. -/
noncomputable def winPtJ (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) (j : ℕ) (x : ℝ) :
    Fin K → ℂ :=
  fun k => ∫ v : ℝ, H k v * winK Ψ j (x - v)

/-- `curvePtJ` is the coordinate-wise phase image of `winPtJ`. -/
lemma curvePtJ_eq_phase (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (j : ℕ) (x : ℝ) :
    curvePtJ Ψ lam H j x
      = fun k => Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * winPtJ Ψ H j x k :=
  rfl

/-- The window kernel as the curve kernel at `t = h_j⁻¹`. -/
lemma winK_eq_curve (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) (z : ℝ) :
    ((winScale j)⁻¹)⁻¹ • Ψ (z / (winScale j)⁻¹) = winK Ψ j z := by
  rw [inv_inv, winK, ← Complex.real_smul, div_inv_eq_mul, mul_comm z (winScale j)]

/-- The unphased point lies on the window curve. -/
lemma winPtJ_mem (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) (j : ℕ) (x : ℝ) :
    winPtJ Ψ H j x ∈ winCurve K (⇑Ψ) H x := by
  refine Set.mem_range.mpr ⟨⟨(winScale j)⁻¹, inv_winScale_pos j⟩, ?_⟩
  funext k
  simp only [winPtJ]
  apply integral_congr_ae
  filter_upwards with y
  rw [winK_eq_curve]

/-- **Phased covers.**  A cover of the window curve at radius `r` gives a cover of the phased curve
points `curvePtJ Ψ lam H i x`. -/
lemma curvePtJ_cover (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (x r : ℝ) {S : Finset (Fin K → ℂ)} (hS : winCovers K (⇑Ψ) H x r S) (i : ℕ) :
    ∃ s ∈ S.image (fun s k => Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * s k),
      ∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - s k‖^2 ≤ r^2 := by
  obtain ⟨s, hsS, hs⟩ := hS (winPtJ Ψ H i x) (winPtJ_mem Ψ H i x)
  refine ⟨fun k => Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * s k,
    Finset.mem_image.mpr ⟨s, hsS, rfl⟩, ?_⟩
  have hph : ∀ k : Fin K, ‖curvePtJ Ψ lam H i x k
        - Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * s k‖
      = ‖winPtJ Ψ H i x k - s k‖ := by
    intro k
    have he : curvePtJ Ψ lam H i x k
          - Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * s k
        = Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ)))
            * (winPtJ Ψ H i x k - s k) := by
      rw [curvePtJ_eq_phase]; ring
    rw [he, norm_mul,
      show ‖Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ)))‖ = 1 from by
        rw [show -(Complex.I * (lam k : ℂ) * (x : ℂ))
            = (((-(lam k * x)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _,
      one_mul]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hph k])]
  exact hs

end BourgainMax

namespace BourgainMax

open _root_.MeasureTheory

/-- The `ℓ²`-diameter bound for the family `{curvePtJ Ψ lam H j x : j ≤ J}`, based at the scale-`0`
point.  Always `≥ 1`, hence positive. -/
noncomputable def curveDiam (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (J : ℕ) (x : ℝ) : ℝ :=
  max 1 ((Finset.univ : Finset (Fin (J+1))).sup' Finset.univ_nonempty (fun i : Fin (J+1) =>
    Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2)))

lemma curveDiam_pos (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (J : ℕ) (x : ℝ) : 0 < curveDiam Ψ lam H J x :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- **Diameter bound.**  Every curve point lies within `curveDiam` (in `ℓ²`) of the scale-`0` point. -/
lemma curvePtJ_ball (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (J : ℕ) (x : ℝ) :
    ∀ i : Fin (J+1), ∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2
      ≤ (curveDiam Ψ lam H J x)^2 := by
  intro i
  have h1 : Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2)
      ≤ curveDiam Ψ lam H J x :=
    le_trans (Finset.le_sup' (fun i : Fin (J+1) => Real.sqrt
      (∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2)) (Finset.mem_univ i))
      (le_max_right _ _)
  have h2 : (0:ℝ) ≤ ∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  calc ∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2
      = (Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - curvePtJ Ψ lam H 0 x k‖^2))^2 :=
        (Real.sq_sqrt h2).symm
    _ ≤ (curveDiam Ψ lam H J x)^2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

end BourgainMax

namespace BourgainMax

open _root_.MeasureTheory

/-- **The `t`-indexed phased covers.**  For each level `t`, a cover `Sc t` of the phased family
`{curvePtJ Ψ lam H i x}` at radius `D·2^{-t}`, of cardinality at most
`winEntropy K ⇑Ψ H x (D·2^{-t}) + 1`. -/
lemma exists_phased_covers (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (J S : ℕ) (x D : ℝ)
    (hfin : ∀ t : ℕ, winEntropy K (⇑Ψ) H x (D*(1/2:ℝ)^t) ≠ ⊤) :
    ∃ Sc : ℕ → Finset (Fin K → ℂ),
      (∀ t, 1 ≤ t → t ≤ S →
        ((Sc t).card : ENNReal) ≤ winEntropy K (⇑Ψ) H x (D*(1/2:ℝ)^t) + 1) ∧
      (∀ t, 1 ≤ t → t ≤ S → ∀ i : Fin (J+1),
        ∃ s ∈ Sc t, ∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - s k‖^2 ≤ (D*(1/2:ℝ)^t)^2) := by
  classical
  have hcov : ∀ t : ℕ, ∃ S' : Finset (Fin K → ℂ),
      (∀ i : Fin (J+1), ∃ s ∈ S',
        ∑ k : Fin K, ‖curvePtJ Ψ lam H i x k - s k‖^2 ≤ (D*(1/2:ℝ)^t)^2) ∧
      ((S'.card : ℕ) : ENNReal) ≤ winEntropy K (⇑Ψ) H x (D*(1/2:ℝ)^t) + 1 := by
    intro t
    obtain ⟨S', hcov', hcard'⟩ := exists_cover_of_winEntropy
      (K := K) (Ψ := (⇑Ψ)) (f := H) (x := x) (r := D*(1/2:ℝ)^t) (hfin t)
    refine ⟨S'.image (fun s k => Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) * s k),
      ?_, ?_⟩
    · intro i
      obtain ⟨s, hsS, hs⟩ := curvePtJ_cover Ψ lam H x (D*(1/2:ℝ)^t) hcov' i
      exact ⟨s, hsS, hs⟩
    · exact le_trans (by exact_mod_cast Finset.card_image_le) hcard'
  exact ⟨fun t => (hcov t).choose,
    fun t _ _ => (hcov t).choose_spec.2,
    fun t _ _ i => (hcov t).choose_spec.1 i⟩

end BourgainMax

/-! ## Identification: the target's operator is `bandScaleOpJ`

This is step (a) of the assembly: for `f ∈ L¹ ∩ L²` (the case to which the Fatou step reduces
everything) the target's band-sum operator at scale `j` is the tuple operator `bandScaleOpJ` of
`BourgainMax`, applied to the window `Ψ = hat φ` and to the modulated tuple
`H k y = f y · e^{I λ_k y}`.  The identity is exactly `bandSum_windowed` plus `winPsi_coe`. -/


/-! ## Change of variables for the windowed curve

The pointwise curve of the assembly is `t ↦ (f_k * Ψ_t)(x)`, `Ψ_t(z) = t⁻¹ Ψ(z/t)`.  Two change-of-
variables facts about it are used repeatedly below: the affine substitution `y ↦ (x-y)/t` on the
Lebesgue integral (Jacobian `t`), and the resulting `L²` mass `t⁻¹∫‖Ψ‖²` of the dilated window. -/

namespace BourgainWindow

open _root_.MeasureTheory Filter
open scoped BigOperators ENNReal Topology

/-- **Change of variables `y ↦ (x - y)/t`.**  The affine map has slope `-1/t`, so it pushes
`volume` to `|t| • volume`; for `t > 0` the integral picks up the Jacobian `t`. -/
theorem lintegral_comp_div_sub (G : ℝ → ENNReal) (hG : Measurable G) (x : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ y, G ((x - y) / t) = ENNReal.ofReal t * ∫⁻ u, G u := by
  have htne : t ≠ 0 := ne_of_gt ht
  have h1 : ∫⁻ y, G ((x - y) / t) = ∫⁻ y, G ((y + x) / t) := by
    have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ => G ((y + x) / t))
    rw [← h]
    refine lintegral_congr (fun y => ?_)
    congr 1
    ring
  have h2 : ∫⁻ y, G ((y + x) / t) = ∫⁻ y, G (y / t) :=
    lintegral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun w : ℝ => G (w / t)) x
  have h3 : ∫⁻ y, G (y / t) = ENNReal.ofReal t * ∫⁻ u, G u := by
    have hdiv : ∀ y : ℝ, y / t = t⁻¹ * y := fun y => by rw [div_eq_inv_mul]
    simp_rw [hdiv]
    rw [← lintegral_map hG (by fun_prop : Measurable fun v : ℝ => t⁻¹ * v)]
    rw [Real.map_volume_mul_left (a := t⁻¹) (inv_ne_zero htne)]
    rw [show ((t⁻¹)⁻¹) = t by rw [inv_inv], abs_of_pos ht]
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [h1, h2, h3]

/-- The `L²` mass of the dilated window `t⁻¹ Ψ(·/t)` is `t⁻¹` times the mass of the window. -/
theorem lintegral_dilated_window (Ψ : SchwartzMap ℝ ℂ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ y : ℝ, ‖(t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal t⁻¹ * ∫⁻ u : ℝ, ‖(Ψ : ℝ → ℂ) u‖ₑ ^ (2:ℝ) := by
  have hnorm : ‖(t⁻¹ : ℝ)‖ₑ = ENNReal.ofReal t⁻¹ := by
    rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg (inv_nonneg.mpr ht.le), ENNReal.ofReal,
      Real.toNNReal_of_nonneg (inv_nonneg.mpr ht.le)]
  have hpt : ∀ y : ℝ, ‖(t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal t⁻¹ ^ (2:ℝ) * ‖(Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ ^ (2:ℝ) := by
    intro y
    rw [enorm_smul, hnorm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  have hmeas1 : Measurable (fun v : ℝ => ‖(Ψ : ℝ → ℂ) v‖ₑ ^ (2:ℝ)) := by
    have hc : Continuous fun v : ℝ => ‖(Ψ : ℝ → ℂ) v‖ₑ := continuous_enorm.comp Ψ.continuous
    have h2 : Measurable (fun v : ℝ => ‖(Ψ : ℝ → ℂ) v‖ₑ * ‖(Ψ : ℝ → ℂ) v‖ₑ) :=
      hc.measurable.mul hc.measurable
    simpa only [ENNReal.rpow_two, pow_two] using h2
  have hmeas2 : Measurable (fun y : ℝ => ‖(Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ ^ (2:ℝ)) := by
    have hc : Continuous fun y : ℝ => ‖(Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ :=
      continuous_enorm.comp (Ψ.continuous.comp (by fun_prop))
    have h2 : Measurable (fun y : ℝ =>
        ‖(Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ * ‖(Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ) :=
      hc.measurable.mul hc.measurable
    simpa only [ENNReal.rpow_two, pow_two] using h2
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_const_mul _ hmeas2]
  rw [lintegral_comp_div_sub (G := fun v : ℝ => ‖(Ψ : ℝ → ℂ) v‖ₑ ^ (2:ℝ)) hmeas1 x ht]
  rw [← mul_assoc]
  congr 1
  rw [ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp


/-- A finite real majorant of a square root: `x ^ (1/2) ≤ ofReal ((x.toReal + 1) ^ (1/2))` for
`x ≠ ⊤`.  This is what turns the finite `L²` masses `A`, `B` of the `t → ∞` decay into an honest
real constant. -/
lemma rpow_half_le_ofReal (x : ENNReal) (hx : x < ⊤) :
    x ^ (1/2:ℝ) ≤ ENNReal.ofReal ((x.toReal + 1) ^ (1/2:ℝ)) := by
  have hx' : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx.ne).symm
  have h1 : x ≤ ENNReal.ofReal ((x.toReal : ℝ) + 1) := by
    calc x = ENNReal.ofReal x.toReal := hx'
      _ ≤ ENNReal.ofReal (x.toReal + 1) := by
          apply ENNReal.ofReal_le_ofReal
          linarith
  calc x ^ (1/2:ℝ) ≤ (ENNReal.ofReal ((x.toReal : ℝ) + 1)) ^ (1/2:ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ENNReal.ofReal ((x.toReal + 1) ^ (1/2:ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (x := (x.toReal : ℝ) + 1) (p := (1/2:ℝ))
          (by positivity) (by norm_num)


/-- **The `t → ∞` half of the total-boundedness lemma.**  For `f ∈ L²` and a Schwartz window the
windowed value `∫ y, f y · t⁻¹Ψ((x-y)/t)` tends to `0` as `t → ∞` (Cauchy–Schwarz in `L²` plus
`‖t⁻¹Ψ(·/t)‖₂ = t^{-1/2}‖Ψ‖₂ → 0`).  It holds for every `x`. -/
theorem winVal_tendsto_zero (Ψ : SchwartzMap ℝ ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    Tendsto (fun t : ℝ => ∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)))
      atTop (𝓝 0) := by
  set A : ENNReal := ∫⁻ u : ℝ, ‖(Ψ : ℝ → ℂ) u‖ₑ ^ (2:ℝ) with hA_def
  set B : ENNReal := ∫⁻ u : ℝ, ‖f u‖ₑ ^ (2:ℝ) with hB_def
  have hA : A < ⊤ := by
    rw [hA_def]
    have hint : Integrable (fun u : ℝ => ‖(Ψ : ℝ → ℂ) u‖ ^ 2) (volume : Measure ℝ) :=
      ((Ψ.memLp (2:ENNReal) (volume : Measure ℝ)).norm).integrable_sq
    refine lt_of_le_of_lt (lintegral_mono (fun u => ?_)) hint.lintegral_lt_top
    rw [show ‖(Ψ : ℝ → ℂ) u‖ₑ = ENNReal.ofReal ‖(Ψ : ℝ → ℂ) u‖ by simp [enorm_eq_nnnorm],
      ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact le_of_eq (by congr 1; ring)
  have hB : B < ⊤ := by
    rw [hB_def]
    have hint : Integrable (fun u : ℝ => ‖f u‖ ^ 2) (volume : Measure ℝ) := hf.norm.integrable_sq
    refine lt_of_le_of_lt (lintegral_mono (fun u => ?_)) hint.lintegral_lt_top
    rw [show ‖f u‖ₑ = ENNReal.ofReal ‖f u‖ by simp [enorm_eq_nnnorm],
      ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact le_of_eq (by congr 1; ring)
  have hbound : ∀ t : ℝ, 0 < t →
      ‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ₑ
        ≤ ENNReal.ofReal (t ^ (-(1/2:ℝ))
            * ((A.toReal + 1) ^ (1/2:ℝ) * (B.toReal + 1) ^ (1/2:ℝ))) := by
    intro t ht
    -- step 1: `‖∫ ·‖ₑ ≤ ∫⁻ ‖·‖ₑ`
    have hcs : ‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ₑ
        ≤ ∫⁻ y : ℝ, ‖f y‖ₑ * ‖(t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ := by
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine lintegral_mono (fun y => ?_)
      rw [enorm_mul]
    -- step 2: Cauchy–Schwarz in `L²`
    have hmeasw : AEMeasurable
        (fun y : ℝ => ‖(t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ) (volume : Measure ℝ) := by
      have h2 : AEMeasurable (fun y : ℝ => ‖(Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ) (volume : Measure ℝ) :=
        ((Ψ.continuous.comp (by fun_prop : Continuous fun y : ℝ => (x - y) / t)).aestronglyMeasurable).enorm
      have h3 := (aemeasurable_const (b := ‖(t : ℝ)⁻¹‖ₑ)).mul h2
      refine h3.congr ?_
      filter_upwards with y
      simp only [Pi.mul_apply, enorm_smul]
    have hholder : ∫⁻ y : ℝ, ‖f y‖ₑ * ‖(t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ
        ≤ B ^ (1/2:ℝ) * (∫⁻ y : ℝ, ‖(t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t)‖ₑ ^ (2:ℝ))
            ^ (1/2:ℝ) := by
      have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ) (p := 2) (q := 2)
        (by rw [Real.holderConjugate_iff]; norm_num) (hf.aestronglyMeasurable.enorm) hmeasw
      simpa only [Pi.mul_apply, hB_def, one_div, inv_one, Real.rpow_two] using h
    rw [lintegral_dilated_window Ψ x ht] at hholder
    -- step 3: substitute the finite masses
    have hA' := rpow_half_le_ofReal A hA
    have hB' := rpow_half_le_ofReal B hB
    have htx : ENNReal.ofReal t⁻¹ ^ (1/2:ℝ) = ENNReal.ofReal (t ^ (-(1/2:ℝ))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (x := t⁻¹) (p := (1/2:ℝ))
        (by positivity : (0:ℝ) ≤ t⁻¹) (by norm_num : (0:ℝ) ≤ 1/2)]
      congr 1
      rw [Real.inv_rpow ht.le (1/2:ℝ), ← Real.rpow_neg ht.le]
    have hstep3 : B ^ (1/2:ℝ) * (ENNReal.ofReal t⁻¹ * A) ^ (1/2:ℝ)
        ≤ ENNReal.ofReal (t ^ (-(1/2:ℝ))
            * ((A.toReal + 1) ^ (1/2:ℝ) * (B.toReal + 1) ^ (1/2:ℝ))) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
      calc B ^ (1/2:ℝ) * (ENNReal.ofReal t⁻¹ ^ (1/2:ℝ) * A ^ (1/2:ℝ))
          ≤ ENNReal.ofReal ((B.toReal + 1) ^ (1/2:ℝ))
              * (ENNReal.ofReal (t ^ (-(1/2:ℝ))) * ENNReal.ofReal ((A.toReal + 1) ^ (1/2:ℝ))) := by
            rw [htx]
            exact mul_le_mul' hB' (mul_le_mul' le_rfl hA')
        _ = ENNReal.ofReal (t ^ (-(1/2:ℝ))
              * ((A.toReal + 1) ^ (1/2:ℝ) * (B.toReal + 1) ^ (1/2:ℝ))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    exact le_trans (le_trans hcs hholder) hstep3
  -- step 4: the upper bound tends to `0`, hence so does `‖·‖ₑ`
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (-(1/2:ℝ))
      * ((A.toReal + 1) ^ (1/2:ℝ) * (B.toReal + 1) ^ (1/2:ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ (-(1/2:ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)
    have h2 : Tendsto (fun t : ℝ => t ^ (-(1/2:ℝ))
        * ((A.toReal + 1) ^ (1/2:ℝ) * (B.toReal + 1) ^ (1/2:ℝ))) atTop (𝓝 0) := by
      simpa using h1.mul_const (((A.toReal + 1) ^ (1/2:ℝ) * (B.toReal + 1) ^ (1/2:ℝ)))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp h2
  have henorm : Tendsto (fun t : ℝ =>
      ‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (fun t => bot_le)) ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact hbound t ht
  -- transfer `‖·‖ₑ → 0` to the `ℂ`-valued function
  rw [tendsto_zero_iff_norm_tendsto_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero] at henorm
  have hε2 : (0:ENNReal) < ENNReal.ofReal (ε/2) := ENNReal.ofReal_pos.mpr (by linarith)
  filter_upwards [henorm (ENNReal.ofReal (ε/2)) hε2] with t ht
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  have h2 : (‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ₑ).toReal ≤ ε/2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) ht
  have h3 : (‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ₑ).toReal
      = ‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ := by
    rw [show ‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ₑ
        = ENNReal.ofReal ‖∫ y : ℝ, f y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / t))‖ from by
          simp [enorm_eq_nnnorm],
      ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [h3] at h2
  linarith

end BourgainWindow

namespace BourgainIdent

open _root_.MeasureTheory Finset
open scoped ContDiff
open scoped BigOperators ENNReal

theorem bandSum_target_eq_bandScaleOpJ (K : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hbd : ∀ x, ‖φ x‖ ≤ 1) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (lam : Fin K → ℝ)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (j : ℕ) (x : ℝ) :
    (∫ y, f y * (∑ k : Fin K, BandDecomp.bandTerm φ (lam k) (BourgainMax.winScale j) x y))
      = BourgainMax.bandScaleOpJ (BandDecomp.winPsi φ hφ hsupp) lam
          (fun k y => f y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) j x := by
  rw [BandDecomp.bandSum_windowed K φ hφ hbd hsupp lam (BourgainMax.winScale_pos j) hf1 hf2 x]
  simp only [BourgainMax.bandScaleOpJ, BourgainMax.winK,
    BandDecomp.winPsi_coe φ hφ hsupp]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_comm]

end BourgainIdent

namespace BourgainMax

open _root_.MeasureTheory

/-- Translation invariance of the Lebesgue integral against `x ↦ x - y` (for `ℝ≥0∞`-valued
integrands). -/
lemma lintegral_sub_right_eq_self (F : ℝ → ℝ≥0∞) (y : ℝ) :
    (∫⁻ x : ℝ, F (x - y)) = ∫⁻ x : ℝ, F x := by
  have h := MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun z : ℝ => F (z - y)) y
  simpa only [add_sub_cancel_right] using h.symm

/-- **The translated maximal is the `y`-phase-averaged sum.**  For a tuple `H`,
`bandMax Ψ lam (transl H y)` equals the `x`-integral of the sup over the dyadic scales of the
Fourier sums `Σ_k e^{I λ_k y} c_j(k)(x)`, where `c_j(k)(x) := e^{-I λ_k x}(H_k * winK_j)(x)`
does not depend on `y`.  This is the change of variables `z = x - y` in `bandMax` together with
the elementary identity `e^{-I λ_k (x - y)} = e^{I λ_k y} e^{-I λ_k x}`. -/
theorem bandMax_transl_eq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (y : ℝ) :
    bandMax Ψ lam (transl H y)
      = ∫⁻ x : ℝ, (⨆ j : ℕ, ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) *
            (Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
              (∫ u : ℝ, H k u * winK Ψ j (x - u)))‖ₑ) ^ (2 : ℝ) := by
  have key : ∀ (x : ℝ) (j : ℕ),
      (∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) *
            (Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
              (∫ u : ℝ, H k u * winK Ψ j (x - u))))
        = bandScaleOpJ Ψ lam (transl H y) j (x - y) := by
    intro x j
    unfold bandScaleOpJ transl
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hexp : Complex.exp (-(Complex.I * (lam k : ℂ) * ((x - y : ℝ) : ℂ)))
        = Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) *
          Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hint : (∫ u : ℝ, H k u * winK Ψ j (x - u))
        = ∫ u : ℝ, H k (u + y) * winK Ψ j ((x - y) - u) := by
      have hcongr : (fun u : ℝ => H k (u + y) * winK Ψ j ((x - y) - u))
          = fun u : ℝ => (fun v : ℝ => H k v * winK Ψ j (x - v)) (u + y) := by
        funext u
        simp only []
        rw [show (x - y) - u = x - (u + y) by ring]
      rw [hcongr]
      exact (MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun v : ℝ => H k v * winK Ψ j (x - v)) y).symm
    rw [hint, hexp]
    ring
  unfold bandMax
  rw [← lintegral_sub_right_eq_self (fun z : ℝ =>
    (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam (transl H y) j z‖ₑ) ^ (2 : ℝ)) y]
  refine lintegral_congr (fun x => ?_)
  congr 1
  refine iSup_congr (fun j => ?_)
  rw [← key x j]

end BourgainMax

end OldSWM



-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/CoverLemmas.lean ====
open MeasureTheory Finset Bornology Metric
open scoped BigOperators ENNReal Topology

theorem exists_finset_l2_cover_of_bounded {K : ℕ} (A : Set (Fin K → ℂ)) (R : ℝ)
    (hR : 0 ≤ R) (hA : ∀ a ∈ A, ∀ k : Fin K, ‖a k‖ ≤ R) {r : ℝ} (hr : 0 < r) :
    ∃ S : Finset (Fin K → ℂ), ∀ a ∈ A, ∃ s ∈ S,
      ∑ k : Fin K, ‖a k - s k‖ ^ 2 ≤ r ^ 2 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    exact ⟨{0}, fun a ha => ⟨0, Finset.mem_singleton_self _, by simp; positivity⟩⟩
  · have hKpos : (0:ℝ) < K := by exact_mod_cast hK
    set ε : ℝ := r / Real.sqrt K with hε
    have hεpos : 0 < ε := by rw [hε]; positivity
    have hsub : A ⊆ closedBall (0 : Fin K → ℂ) R := by
      intro a ha
      rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
      intro k
      simpa using hA a ha k
    have htb : TotallyBounded (closedBall (0 : Fin K → ℂ) R) :=
      (isCompact_closedBall (0 : Fin K → ℂ) R).totallyBounded
    obtain ⟨t, htfin, ht⟩ := (totallyBounded_iff.mp htb) ε hεpos
    refine ⟨htfin.toFinset, fun a ha => ?_⟩
    have ha' := ht (hsub ha)
    simp only [Set.mem_iUnion] at ha'
    obtain ⟨y, hyt, hball⟩ := ha'
    refine ⟨y, htfin.mem_toFinset.mpr hyt, ?_⟩
    have hdist : dist a y < ε := hball
    have hbound : ∀ k : Fin K, ‖a k - y k‖ ≤ ε := by
      intro k
      have h1 : dist (a k) (y k) ≤ dist a y := by
        rw [dist_eq_norm, dist_eq_norm]
        simpa using norm_le_pi_norm (a - y) k
      have h2 : dist (a k) (y k) ≤ ε := le_trans h1 hdist.le
      rwa [dist_eq_norm] at h2
    calc ∑ k : Fin K, ‖a k - y k‖ ^ 2 ≤ ∑ _k : Fin K, ε ^ 2 :=
          Finset.sum_le_sum (fun k _ => by
            exact pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2)
      _ = K * ε ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = r ^ 2 := by
          rw [hε]
          have h2 : Real.sqrt (K:ℝ) ≠ 0 := by positivity
          field_simp
          rw [Real.sq_sqrt hKpos.le]

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/ScaledRiemann.lean ====

namespace FWS

open MeasureTheory
open scoped ENNReal

/-- `(min a b) ^ p = min (a ^ p) (b ^ p)` for `ℝ≥0∞`. -/
lemma min_rpow_eq {p : ℝ} (hp : 0 ≤ p) (a b : ℝ≥0∞) : (min a b) ^ p = min (a ^ p) (b ^ p) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (ENNReal.rpow_le_rpow h hp)]
  · rw [min_eq_right h, min_eq_right (ENNReal.rpow_le_rpow h hp)]

/-- `min a (x + y) ≤ min a x + y` for `ℝ≥0∞`. -/
lemma min_add_le' (a x y : ℝ≥0∞) : min a (x + y) ≤ min a x + y := by
  rcases le_total a x with h | h
  · calc min a (x + y) ≤ a := min_le_left _ _
      _ = min a x := (min_eq_left h).symm
      _ ≤ min a x + y := le_add_right le_rfl
  · calc min a (x + y) ≤ x + y := min_le_right _ _
      _ = min a x + y := by rw [min_eq_right h]

/-- **Scaled dyadic sum versus entropy integral.**  For a non-increasing `f : ℝ → ℝ≥0∞`, a scale
`c > 0` and "entropy numbers" `M t` dominated by `f (2c · 2^{-t})`, the dyadic sum
`∑_{t ≤ S} 2^{-t} min(K, M t + 1)^{1/2}` is bounded by `c⁻¹` times the integral of
`min(√K, (f r + 1)^{1/2})` over `(0, 2c]`. -/
theorem ofReal_sum_dyadic_le_lintegral_entropy_scaled (f : ℝ → ℝ≥0∞)
    (hf : ∀ x y : ℝ, 0 < x → x ≤ y → f y ≤ f x) {c : ℝ} (hc : 0 < c)
    (K : ℕ) (M : ℕ → ℕ) (hM : ∀ t : ℕ, (M t : ℝ≥0∞) ≤ f ((2*c) * (1/2:ℝ)^t)) (S : ℕ) :
    ENNReal.ofReal (∑ t ∈ Finset.range (S + 1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ENNReal.ofReal c⁻¹ * ∫⁻ r in Set.Ioc (0:ℝ) (2*c),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) := by
  have h2c : (0:ℝ) < 2 * c := by linarith
  -- the dyadic cells in the radius variable
  let A : ℕ → Set ℝ := fun t => Set.Ioc ((2*c) * (1/2:ℝ)^(t+1)) ((2*c) * (1/2:ℝ)^t)
  have hA : ∀ t, A t = Set.Ioc ((2*c) * (1/2:ℝ)^(t+1)) ((2*c) * (1/2:ℝ)^t) := fun t => rfl
  -- `2^{-t}` in `ℝ≥0∞` is `ofReal` of the real power
  have hpow : ∀ t : ℕ, (1/2:ℝ≥0∞)^t = ENNReal.ofReal ((1/2:ℝ)^t) := by
    intro t
    have h : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2:ℝ) := by simp
    rw [h, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2)]
  -- the summand as an `ℝ≥0∞`
  have hbase : ∀ t : ℕ, ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      = (min (ENNReal.ofReal (K:ℝ)) ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2) := by
    intro t
    rw [Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg (le_min (Nat.cast_nonneg K) (by positivity))
        (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
      ENNReal.ofReal_min, ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    simp only [ENNReal.ofReal_natCast]
  -- `(ofReal K) ^ (1/2) = ofReal √K`
  have hK : (ENNReal.ofReal (K:ℝ)) ^ ((1:ℝ)/2) = ENNReal.ofReal (Real.sqrt (K:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg K)
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
  -- the termwise bound
  have hterm : ∀ t : ℕ, ENNReal.ofReal ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ENNReal.ofReal c⁻¹ * ∫⁻ r in A t,
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) := by
    intro t
    -- the constant lower bound for the integrand on the cell
    have hmono : ∫⁻ r in A t,
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ))
        ≤ ∫⁻ r in A t,
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) := by
      apply setLIntegral_mono' (s := A t)
      · rw [hA t]; exact measurableSet_Ioc
      · intro r hr
        rw [hA t] at hr
        simp only [Set.mem_Ioc] at hr
        refine min_le_min le_rfl ?_
        have hfr : f ((2*c) * (1/2:ℝ)^t) ≤ f r := by
          refine hf r ((2*c) * (1/2:ℝ)^t) ?_ hr.2
          exact lt_of_lt_of_le
            (mul_pos h2c (pow_pos (by norm_num : (0:ℝ) < 1/2) (t+1))) hr.1.le
        exact ENNReal.rpow_le_rpow (x := f ((2*c) * (1/2:ℝ)^t) + 1)
          (y := f r + 1) (z := (1:ℝ)/2) (add_le_add hfr le_rfl)
          (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
    have hconst : ∫⁻ r in A t,
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ))
        = min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ))
          * volume (A t) :=
      setLIntegral_const (A t) _
    have hvol : volume (A t) = ENNReal.ofReal (c * (1/2:ℝ)^t) := by
      rw [hA t, Real.volume_Ioc]
      congr 1
      have h1 : (2*c) * (1/2:ℝ)^t - (2*c) * (1/2:ℝ)^(t+1) = c * (1/2:ℝ)^t := by
        rw [pow_succ]; ring
      rw [h1]
    -- the summand is at most the constant integrand times the cell mass
    have hstep : ENNReal.ofReal ((1/2:ℝ)^t) *
          (min (ENNReal.ofReal (K:ℝ)) ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2)
        ≤ ENNReal.ofReal c⁻¹ * (min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ)) * ENNReal.ofReal (c * (1/2:ℝ)^t)) := by
      have hV : (min (ENNReal.ofReal (K:ℝ)) ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2)
          ≤ min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ)) := by
        rw [min_rpow_eq (by norm_num : (0:ℝ) ≤ (1:ℝ)/2), hK]
        refine min_le_min le_rfl ?_
        exact ENNReal.rpow_le_rpow (x := (M t : ℝ≥0∞) + 1)
          (y := f ((2*c) * (1/2:ℝ)^t) + 1) (z := (1:ℝ)/2) (add_le_add (hM t) le_rfl)
          (by norm_num)
      have hcf : ENNReal.ofReal ((1/2:ℝ)^t)
          = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (c * (1/2:ℝ)^t) := by
        rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc))]
        congr 1
        field_simp
      calc ENNReal.ofReal ((1/2:ℝ)^t) *
            (min (ENNReal.ofReal (K:ℝ)) ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2)
          ≤ ENNReal.ofReal ((1/2:ℝ)^t) * min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ)) :=
            mul_le_mul' le_rfl hV
        _ = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (c * (1/2:ℝ)^t)
              * min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ)) := by rw [hcf]
        _ = ENNReal.ofReal c⁻¹ * (min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ)) * ENNReal.ofReal (c * (1/2:ℝ)^t)) := by
            ring
    calc ENNReal.ofReal ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        = ENNReal.ofReal ((1/2:ℝ)^t) * (min (ENNReal.ofReal (K:ℝ))
            ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2) := by
          rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1/2:ℝ)^t),
            ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2), hbase t]
      _ ≤ ENNReal.ofReal c⁻¹ * (min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((f ((2*c) * (1/2:ℝ)^t) + 1) ^ (1/2:ℝ)) * ENNReal.ofReal (c * (1/2:ℝ)^t)) := hstep
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ r in A t,
            min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) := by
          refine mul_le_mul' le_rfl ?_
          rw [← hvol, ← hconst]
          exact hmono
  -- disjointness of the cells
  have hdisj : (Finset.range (S+1) : Set ℕ).PairwiseDisjoint A := by
    intro i _ j _ hij
    change Disjoint (A i) (A j)
    rw [Set.disjoint_left]
    intro r hri hrj
    rw [hA i] at hri
    rw [hA j] at hrj
    simp only [Set.mem_Ioc] at hri hrj
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : (2*c) * (1/2:ℝ)^j ≤ (2*c) * (1/2:ℝ)^(i+1) := by
        refine mul_le_mul_of_nonneg_left ?_ h2c.le
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hri.1, hrj.2, hle]
    · have hle : (2*c) * (1/2:ℝ)^i ≤ (2*c) * (1/2:ℝ)^(j+1) := by
        refine mul_le_mul_of_nonneg_left ?_ h2c.le
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hrj.1, hri.2, hle]
  have hmeas : ∀ b ∈ Finset.range (S+1), MeasurableSet (A b) := by
    intro b hb
    rw [hA b]; exact measurableSet_Ioc
  have hAsub : ∀ t, A t ⊆ Set.Ioc (0:ℝ) (2*c) := by
    intro t r hr
    rw [hA t] at hr
    simp only [Set.mem_Ioc] at hr ⊢
    constructor
    · have h1 : (0:ℝ) < (1/2:ℝ)^(t+1) := pow_pos (by norm_num) _
      nlinarith [h2c, h1, hr.1]
    · have h1 : (1/2:ℝ)^t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [h2c, h1, hr.2]
  have hsubset : (⋃ t ∈ Finset.range (S+1), A t) ⊆ Set.Ioc (0:ℝ) (2*c) := by
    intro r hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨t, -, hrt⟩ := hr
    exact hAsub t hrt
  -- the sum, term by term
  have hsum : ENNReal.ofReal (∑ t ∈ Finset.range (S + 1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      = ∑ t ∈ Finset.range (S + 1), ENNReal.ofReal
          ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) :=
    ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)
  rw [hsum]
  calc ∑ t ∈ Finset.range (S + 1), ENNReal.ofReal
        ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ∑ t ∈ Finset.range (S + 1), ENNReal.ofReal c⁻¹ * ∫⁻ r in A t,
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) :=
        Finset.sum_le_sum (fun t _ => hterm t)
    _ = ENNReal.ofReal c⁻¹ * ∑ t ∈ Finset.range (S + 1), ∫⁻ r in A t,
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ r in (⋃ t ∈ Finset.range (S + 1), A t),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) := by
        rw [lintegral_biUnion_finset hdisj hmeas]
    _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ r in Set.Ioc (0:ℝ) (2*c),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((f r + 1) ^ (1/2:ℝ)) :=
        mul_le_mul_right (lintegral_mono_set hsubset) _

end FWS

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/Entropy.lean ====

open MeasureTheory Finset Metric
open scoped BigOperators ENNReal
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000

namespace FWDeep

/-! ### Elementary power-mean lemmas -/

lemma sum_rpow_le_sum_rpow_of_le_one {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ t, 0 ≤ c i) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ t, c i) ^ p ≤ ∑ i ∈ t, c i ^ p := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0.ne']
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hca : 0 ≤ c a := hc a (Finset.mem_insert_self a t)
      have ht0 : 0 ≤ ∑ i ∈ t, c i :=
        Finset.sum_nonneg fun i hi => hc i (Finset.mem_insert_of_mem hi)
      have ih' := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      calc (c a + ∑ i ∈ t, c i) ^ p ≤ c a ^ p + (∑ i ∈ t, c i) ^ p :=
            Real.rpow_add_le_add_rpow hca ht0 hp0.le hp1
        _ ≤ c a ^ p + ∑ i ∈ t, c i ^ p := by linarith

lemma sum_rpow_le_of_one_le {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ t, 0 ≤ c i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ t, c i ^ p ≤ (∑ i ∈ t, c i) ^ p := by
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le one_pos hp
  have hq0 : (0:ℝ) < 1/p := by positivity
  have hq1 : 1/p ≤ 1 := by rw [div_le_one hp0]; linarith
  have hS : 0 ≤ ∑ i ∈ t, c i ^ p := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hc i hi) p
  have h1 := sum_rpow_le_sum_rpow_of_le_one t (fun i => c i ^ p)
    (fun i hi => Real.rpow_nonneg (hc i hi) p) hq0 hq1
  have h2 : (∑ i ∈ t, c i ^ p) ^ (1/p) ≤ ∑ i ∈ t, c i := by
    calc (∑ i ∈ t, c i ^ p) ^ (1/p) ≤ ∑ i ∈ t, (c i ^ p) ^ (1/p) := h1
      _ = ∑ i ∈ t, c i := by
          apply Finset.sum_congr rfl; intro i hi
          rw [← Real.rpow_mul (x := c i) (hc i hi)]
          rw [show p * (1/p) = 1 by field_simp, Real.rpow_one]
  have key : ((∑ i ∈ t, c i ^ p) ^ (1/p)) ^ p = ∑ i ∈ t, c i ^ p := by
    rw [← Real.rpow_mul (x := ∑ i ∈ t, c i ^ p) hS]
    rw [show (1:ℝ)/p * p = 1 by field_simp, Real.rpow_one]
  calc ∑ i ∈ t, c i ^ p = ((∑ i ∈ t, c i ^ p) ^ (1/p)) ^ p := key.symm
    _ ≤ (∑ i ∈ t, c i) ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hS _) h2 hp0.le

lemma sum_rpow_le_sum_sq_rpow {ι : Type*} (t : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ t, 0 ≤ b i) {s : ℝ} (hs : 2 < s) :
    (∑ i ∈ t, b i ^ s) ^ ((1:ℝ)/s) ≤ (∑ i ∈ t, b i ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  have hs0 : (0:ℝ) < s := by linarith
  have h2 : ∑ i ∈ t, b i ^ s = ∑ i ∈ t, (b i ^ (2:ℝ)) ^ (s/2) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [← Real.rpow_mul (x := b i) (hb i hi)]
    congr 1
    ring
  have h1 : ∑ i ∈ t, b i ^ s ≤ (∑ i ∈ t, b i ^ (2:ℝ)) ^ (s/2) := by
    rw [h2]
    exact sum_rpow_le_of_one_le t (fun i => b i ^ (2:ℝ))
      (fun i hi => Real.rpow_nonneg (hb i hi) 2) (by linarith : (1:ℝ) ≤ s/2)
  have key : ((∑ i ∈ t, b i ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s)
      = (∑ i ∈ t, b i ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_mul (x := ∑ i ∈ t, b i ^ (2:ℝ))
      (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hb i hi) 2)]
    rw [show s/2 * (1/s) = (1:ℝ)/2 by field_simp]
  calc (∑ i ∈ t, b i ^ s) ^ ((1:ℝ)/s)
      ≤ ((∑ i ∈ t, b i ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hb i hi) s) h1
          (one_div_nonneg.mpr hs0.le)
    _ = (∑ i ∈ t, b i ^ (2:ℝ)) ^ ((1:ℝ)/2) := key

lemma sum_sq_rpow_le_card_mul {ι : Type*} [Fintype ι] (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    {s : ℝ} (hs : 2 < s) :
    (∑ i, b i ^ (2:ℝ)) ^ (s/2) ≤ (Fintype.card ι : ℝ) ^ (s/2 - 1) * ∑ i, b i ^ s := by
  have hs0 : (0:ℝ) < s := by linarith
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    simp [Finset.univ_eq_empty, Real.zero_rpow (by linarith : s/2 ≠ 0)]
  have hK0 : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast h0
  have hq : Real.HolderConjugate (s/2) (s/(s-2)) := by
    refine ⟨?_, by linarith, div_pos hs0 (sub_pos.mpr (by linarith))⟩
    field_simp
    ring
  have h := Real.inner_le_Lp_mul_Lq (s := (Finset.univ : Finset ι))
    (f := fun i => b i ^ (2:ℝ)) (g := fun _ : ι => (1:ℝ)) hq
  have e1 : (∑ i : ι, b i ^ (2:ℝ) * 1) = ∑ i : ι, b i ^ (2:ℝ) := by simp
  rw [e1] at h
  have e2 : (∑ i : ι, |b i ^ (2:ℝ)| ^ (s/2)) = ∑ i : ι, b i ^ s := by
    apply Finset.sum_congr rfl; intro i _
    rw [abs_of_nonneg (Real.rpow_nonneg (hb i) 2), ← Real.rpow_mul (x := b i) (hb i)]
    congr 1
    ring
  have e3 : (∑ _i : ι, |(1:ℝ)| ^ (s/(s-2))) = (Fintype.card ι : ℝ) := by simp
  rw [e2, e3] at h
  rw [show (1:ℝ)/(s/2) = 2/s by field_simp,
    show (1:ℝ)/(s/(s-2)) = (s-2)/s by field_simp] at h
  have hB : 0 ≤ ∑ i, b i ^ s := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hb i) s
  have keyS : ((∑ i, b i ^ s) ^ (2/s) * (Fintype.card ι : ℝ) ^ ((s-2)/s)) ^ (s/2)
      = (∑ i, b i ^ s) * (Fintype.card ι : ℝ) ^ ((s-2)/s * (s/2)) := by
    calc ((∑ i, b i ^ s) ^ (2/s) * (Fintype.card ι : ℝ) ^ ((s-2)/s)) ^ (s/2)
        = ((∑ i, b i ^ s) ^ (2/s)) ^ (s/2) * ((Fintype.card ι : ℝ) ^ ((s-2)/s)) ^ (s/2) :=
          Real.mul_rpow (Real.rpow_nonneg hB _) (Real.rpow_nonneg (le_of_lt hK0) _)
      _ = (∑ i, b i ^ s) ^ ((2/s) * (s/2)) * (Fintype.card ι : ℝ) ^ (((s-2)/s) * (s/2)) := by
          rw [Real.rpow_mul (x := ∑ i, b i ^ s) hB,
            Real.rpow_mul (x := (Fintype.card ι : ℝ)) (le_of_lt hK0)]
      _ = (∑ i, b i ^ s) * (Fintype.card ι : ℝ) ^ ((s-2)/s * (s/2)) := by
          rw [show (2:ℝ)/s * (s/2) = 1 by field_simp, Real.rpow_one]
  have h2 : (∑ i, b i ^ (2:ℝ)) ^ (s/2)
      ≤ ((∑ i, b i ^ s) ^ (2/s) * (Fintype.card ι : ℝ) ^ ((s-2)/s)) ^ (s/2) :=
    Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hb i) 2) h
      (by positivity)
  rw [keyS] at h2
  calc (∑ i, b i ^ (2:ℝ)) ^ (s/2)
      ≤ (∑ i, b i ^ s) * (Fintype.card ι : ℝ) ^ ((s-2)/s * (s/2)) := h2
    _ = (Fintype.card ι : ℝ) ^ (s/2 - 1) * ∑ i, b i ^ s := by
        rw [show (s-2)/s * (s/2) = s/2 - 1 by field_simp]
        ring

/-! ### The `ℓ²`-valued windowed curve and its `s`-variation -/

/-- The `ℓ²`-valued windowed curve point. -/
noncomputable def curveE (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x t : ℝ) :
    EuclideanSpace ℂ (Fin K) :=
  WithLp.toLp 2 (fun k => Commons.Analysis.Fourier.winOp Ψ (f k) x t)

/-- The scalar increment of a chain of scales (log-parametrised). -/
noncomputable def chainB (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {J : ℕ} (u : Fin (J + 1) → ℝ) (j : Fin J) (k : Fin K) : ℝ :=
  dist (Commons.Analysis.Fourier.winOp Ψ (f k) x (Real.exp (u (Fin.castSucc j))))
    (Commons.Analysis.Fourier.winOp Ψ (f k) x (Real.exp (u (Fin.succ j))))

lemma chainB_nonneg (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {J : ℕ} (u : Fin (J + 1) → ℝ) (j : Fin J) (k : Fin K) : 0 ≤ chainB Ψ f x u j k :=
  dist_nonneg

/-- The `ℓ²`-metric `s`-variation of the windowed curve. -/
noncomputable def vecVarE (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    (s : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → ℝ), ⨆ (_ : StrictMono u),
    ENNReal.ofReal ((∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s))

lemma dist_sq_eq_sum (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {J : ℕ} (u : Fin (J + 1) → ℝ) (j : Fin J) :
    dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ (2:ℝ)
      = ∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ) := by
  have h : dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
      (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ 2
      = ∑ k : Fin K, chainB Ψ f x u j k ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    rfl
  simp only [Real.rpow_two]
  simpa only [pow_two] using h

/-- The `s`-th power of the `ℓ²`-distance is the `s/2`-th power of the `ℓ²`-sum. -/
lemma dist_rpow_eq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {J : ℕ} (u : Fin (J + 1) → ℝ) (j : Fin J) {s : ℝ} :
    dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s
      = (∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ)) ^ (s/2) := by
  have h2 : (0:ℝ) ≤ ∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ) :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (chainB_nonneg Ψ f x u j k) 2
  have hd : dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
      (curveE Ψ f x (Real.exp (u (Fin.succ j))))
      = (∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    have h := dist_sq_eq_sum Ψ f x u j
    have hsq : dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ (2:ℝ)
        = ∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ) := h
    calc dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
          (curveE Ψ f x (Real.exp (u (Fin.succ j))))
        = (dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
            (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
          rw [← Real.rpow_mul dist_nonneg]
          rw [show (2:ℝ) * ((1:ℝ)/2) = 1 by norm_num, Real.rpow_one]
      _ = (∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ)) ^ ((1:ℝ)/2) := by rw [hsq]
  rw [hd, ← Real.rpow_mul h2]
  congr 1
  ring

/-- **Per-chain comparison.** -/
lemma chain_le_of_chain (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s : ℝ} (hs : 2 < s) {J : ℕ} (u : Fin (J + 1) → ℝ) :
    ((∑ j : Fin J, (∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s))
      ≤ (K:ℝ) ^ ((1:ℝ)/2 - 1/s)
        * (∑ k : Fin K, (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s)) ^ ((1:ℝ)/2) := by
  have hs0 : (0:ℝ) < s := by linarith
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  set b : Fin J → Fin K → ℝ := chainB Ψ f x u with hb
  have hb0 : ∀ j k, 0 ≤ b j k := fun j k => dist_nonneg
  set c : Fin K → ℝ := fun k => ∑ j : Fin J, b j k ^ s with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hb0 j k) s
  have hstep1 : ∑ j : Fin J, (∑ k : Fin K, b j k ^ (2:ℝ)) ^ (s/2)
      ≤ (K:ℝ) ^ (s/2 - 1) * ∑ k : Fin K, c k := by
    calc ∑ j : Fin J, (∑ k : Fin K, b j k ^ (2:ℝ)) ^ (s/2)
        ≤ ∑ j : Fin J, (K:ℝ) ^ (s/2 - 1) * ∑ k : Fin K, b j k ^ s :=
          Finset.sum_le_sum fun j _ => by
            simpa [Fintype.card_fin] using sum_sq_rpow_le_card_mul (b j) (fun k => hb0 j k) hs
      _ = (K:ℝ) ^ (s/2 - 1) * ∑ k : Fin K, c k := by
          rw [hc]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
  have hsum0 : 0 ≤ ∑ k : Fin K, c k := Finset.sum_nonneg fun k _ => hc0 k
  have hstep2 : ((∑ j : Fin J, (∑ k : Fin K, b j k ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s))
      ≤ (K:ℝ) ^ ((1:ℝ)/2 - 1/s) * (∑ k : Fin K, c k) ^ ((1:ℝ)/s) := by
    calc ((∑ j : Fin J, (∑ k : Fin K, b j k ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s))
        ≤ ((K:ℝ) ^ (s/2 - 1) * ∑ k : Fin K, c k) ^ ((1:ℝ)/s) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun j _ =>
            Real.rpow_nonneg (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hb0 j k) 2) _)
            hstep1 (one_div_nonneg.mpr hs0.le)
      _ = ((K:ℝ) ^ (s/2 - 1)) ^ ((1:ℝ)/s) * (∑ k : Fin K, c k) ^ ((1:ℝ)/s) :=
          Real.mul_rpow (Real.rpow_nonneg hK0 _) hsum0
      _ = (K:ℝ) ^ ((1:ℝ)/2 - 1/s) * (∑ k : Fin K, c k) ^ ((1:ℝ)/s) := by
          rw [← Real.rpow_mul hK0,
            show (s/2 - 1) * (1/s) = (1:ℝ)/2 - 1/s by field_simp]
  have hpow : (0:ℝ) < 2/s := by positivity
  have hpow1 : 2/s ≤ 1 := by rw [div_le_one hs0]; linarith
  have hstep3 : (∑ k : Fin K, c k) ^ ((1:ℝ)/s)
      ≤ (∑ k : Fin K, c k ^ (2/s)) ^ ((1:ℝ)/2) := by
    have h1 : (∑ k : Fin K, c k) ^ (2/s) ≤ ∑ k : Fin K, c k ^ (2/s) :=
      sum_rpow_le_sum_rpow_of_le_one Finset.univ c (fun k _ => hc0 k) hpow hpow1
    have h2 : (∑ k : Fin K, c k) ^ ((1:ℝ)/s) = ((∑ k : Fin K, c k) ^ (2/s)) ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_mul hsum0,
        show (2/s) * ((1:ℝ)/2) = (1:ℝ)/s by field_simp]
    rw [h2]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hsum0 _) h1 (by norm_num)
  calc ((∑ j : Fin J, (∑ k : Fin K, b j k ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s))
      ≤ (K:ℝ) ^ ((1:ℝ)/2 - 1/s) * (∑ k : Fin K, c k) ^ ((1:ℝ)/s) := hstep2
    _ ≤ (K:ℝ) ^ ((1:ℝ)/2 - 1/s)
        * (∑ k : Fin K, c k ^ (2/s)) ^ ((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_left hstep3 (Real.rpow_nonneg hK0 _)

/-- **The `ℓ²`-variation bound.** -/
lemma vecVarE_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s : ℝ} (hs : 2 < s) :
    vecVarE Ψ f x s
      ≤ ENNReal.ofReal ((K:ℝ) ^ ((1:ℝ)/2 - 1/s))
        * (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  unfold vecVarE
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => ?_
  have hchain := chain_le_of_chain Ψ f x hs u
  have hVk : ∀ k : Fin K, ENNReal.ofReal ((∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ ((1:ℝ)/s))
      ≤ Commons.Analysis.Fourier.winVar Ψ (f k) x s := by
    intro k
    rw [show (∑ j : Fin J, chainB Ψ f x u j k ^ s) = ∑ j : Fin J,
        ‖Commons.Analysis.Fourier.winOp Ψ (f k) x (Real.exp (u (Fin.castSucc j)))
          - Commons.Analysis.Fourier.winOp Ψ (f k) x (Real.exp (u (Fin.succ j)))‖ ^ s from
      Finset.sum_congr rfl (fun j _ => by rw [chainB, dist_eq_norm])]
    refine le_iSup_of_le J ?_
    refine le_iSup_of_le (fun j => (⟨Real.exp (u j), Real.exp_pos _⟩ : {t : ℝ // 0 < t})) ?_
    refine le_iSup_of_le (fun i j hij => Real.exp_lt_exp.mpr (hu hij)) ?_
    rfl
  have hsum : ENNReal.ofReal
        ((∑ k : Fin K, (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s)) ^ ((1:ℝ)/2))
      ≤ (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    have h3 : ∀ k : Fin K,
        (ENNReal.ofReal ((∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ ((1:ℝ)/s))) ^ (2:ℝ)
        = ENNReal.ofReal ((∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s)) := by
      intro k
      rw [ENNReal.ofReal_rpow_of_nonneg
        (x := (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ ((1:ℝ)/s))
        (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg dist_nonneg s) _)
        (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      rw [← Real.rpow_mul (Finset.sum_nonneg fun j _ =>
        Real.rpow_nonneg (chainB_nonneg Ψ f x u j k) s)]
      congr 1
      field_simp
    have h4 : ENNReal.ofReal
          ((∑ k : Fin K, (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s)) ^ ((1:ℝ)/2))
        = (∑ k : Fin K,
            (ENNReal.ofReal ((∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ ((1:ℝ)/s))) ^ (2:ℝ))
          ^ ((1:ℝ)/2) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg
        (x := ∑ k : Fin K, (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s))
        (Finset.sum_nonneg fun k _ => Real.rpow_nonneg
          (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (chainB_nonneg Ψ f x u j k) s) (2/s))
        (by norm_num : (0:ℝ) ≤ 1/2)]
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun k : Fin K => (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s))
        (fun k _ => Real.rpow_nonneg
          (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (chainB_nonneg Ψ f x u j k) s) (2/s))]
      exact Finset.sum_congr rfl fun k _ => (h3 k).symm
    rw [h4]
    exact ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k _ =>
      ENNReal.rpow_le_rpow (hVk k) (by norm_num)) (by norm_num)
  have hL : ENNReal.ofReal
        ((∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
          (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s))
      = ENNReal.ofReal
        ((∑ j : Fin J, (∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s)) := by
    rw [Finset.sum_congr rfl (fun j _ => dist_rpow_eq Ψ f x u j)]
  rw [hL]
  calc ENNReal.ofReal
        ((∑ j : Fin J, (∑ k : Fin K, chainB Ψ f x u j k ^ (2:ℝ)) ^ (s/2)) ^ ((1:ℝ)/s))
      ≤ ENNReal.ofReal ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)
          * (∑ k : Fin K, (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s)) ^ ((1:ℝ)/2)) :=
        ENNReal.ofReal_le_ofReal hchain
    _ = ENNReal.ofReal ((K:ℝ) ^ ((1:ℝ)/2 - 1/s))
          * ENNReal.ofReal ((∑ k : Fin K, (∑ j : Fin J, chainB Ψ f x u j k ^ s) ^ (2/s))
              ^ ((1:ℝ)/2)) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg K) _)
    _ ≤ ENNReal.ofReal ((K:ℝ) ^ ((1:ℝ)/2 - 1/s))
          * (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2) :=
        mul_le_mul_right hsum _

/-- **The squared form.** -/
lemma vecVarE_sq_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s : ℝ} (hs : 2 < s) :
    (vecVarE Ψ f x s) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
        * ∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ) := by
  have hs0 : (0:ℝ) < s := by linarith
  have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hb := vecVarE_le Ψ f x hs
  have h2 := ENNReal.rpow_le_rpow hb (by norm_num : (0:ℝ) ≤ 2)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hK0 _) (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)) ^ (2:ℝ) = (K:ℝ) ^ ((s-2)/s) by
    rw [← Real.rpow_mul hK0]
    congr 1
    field_simp]
  congr 1
  rw [← ENNReal.rpow_mul]
  rw [show (1:ℝ)/2 * 2 = 1 by norm_num, ENNReal.rpow_one]

/-! ### Step 2 of the ℓ² deep-input route: the integrated ℓ²-variation bound -/

/-- **The integrated ℓ²-variation bound.**  There is an absolute constant `C > 0` (depending only on
the window `Ψ`) such that the `L²(ℝ)`-norm of the `ℓ²`-metric `s`-variation of the windowed curve is
bounded by `C/(s-2)²` times the `ℓ²`-norm of the data, in the sharp form needed for the entropy
input. -/
theorem lintegral_vecVarE_sq_le (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MeasureTheory.MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MeasureTheory.MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∀ {s : ℝ}, 2 < s → s ≤ 3 → (K:ℝ) ^ ((s-2)/s) ≤ 4 →
      ∫⁻ x, (vecVarE Ψ f x s) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C / (s-2)^2)
          * ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Fourier.dilation_variation_scalar_l2 Ψ
  refine ⟨4 * C₀^2, by positivity, ?_⟩
  intro K f hf2 hfinf s hs hs3 hKr
  have hs0 : (0:ℝ) < s := by linarith
  -- termwise: `∫ (winVar_k)^2 ≤ ofReal((C₀/(s-2))^2) ∫ ofReal(‖f k‖^2)`
  have hterm : ∀ k : Fin K, ∫⁻ x, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((C₀/(s-2))^2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖^2) := by
    intro k
    have h := hC₀ s hs hs3 (f k) (hf2 k) (hfinf k)
    exact h
  have hmeas : ∀ k : Fin K, AEMeasurable
      (fun x : ℝ => (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) volume := by
    intro k
    exact ((Commons.Analysis.Fourier.dilation_variation_aemeasurable Ψ s (f k)
      (hf2 k).aemeasurable (hf2 k)).pow_const 2)
  have hsum : ∫⁻ x, (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ))
      = ∑ k : Fin K, ∫⁻ x, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ) :=
    lintegral_finsetSum' _ (fun k _ => hmeas k)
  have hbsq : ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2)
      = ∑ k : Fin K, ∫⁻ x, ENNReal.ofReal (‖f k x‖^2) := by
    rw [show (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2))
        = fun x : ℝ => ∑ k : Fin K, ENNReal.ofReal (‖f k x‖^2) from
      funext fun x => ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact lintegral_finsetSum' _ (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)
  have hmain : ∫⁻ x, (vecVarE Ψ f x s) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
        * ∑ k : Fin K, ∫⁻ x, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ) := by
    refine le_trans (lintegral_mono (fun x => vecVarE_sq_le Ψ f x hs)) ?_
    have hpull : (∫⁻ x, ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
        * (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)))
        = ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
          * ∫⁻ x, (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hpull, hsum]
  calc ∫⁻ x, (vecVarE Ψ f x s) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
          * ∑ k : Fin K, ∫⁻ x, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ) := hmain
    _ ≤ ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
          * ∑ k : Fin K,
              ENNReal.ofReal ((C₀/(s-2))^2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖^2) :=
        mul_le_mul_right (Finset.sum_le_sum fun k _ => hterm k) _
    _ = ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s))
          * (ENNReal.ofReal ((C₀/(s-2))^2)
              * ∑ k : Fin K, ∫⁻ x, ENNReal.ofReal (‖f k x‖^2)) := by
        rw [← Finset.mul_sum]
    _ = ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s) * ((C₀/(s-2))^2))
          * ∑ k : Fin K, ∫⁻ x, ENNReal.ofReal (‖f k x‖^2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg K) _)]
    _ = ENNReal.ofReal ((K:ℝ) ^ ((s-2)/s) * ((C₀/(s-2))^2))
          * ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by rw [hbsq]
    _ ≤ ENNReal.ofReal (4 * C₀^2 / (s-2)^2)
          * ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : (0:ℝ) < (s-2)^2 := by positivity
        rw [div_eq_mul_inv]
        calc (K:ℝ) ^ ((s-2)/s) * ((C₀/(s-2))^2)
            ≤ 4 * ((C₀/(s-2))^2) := mul_le_mul_of_nonneg_right hKr (by positivity)
          _ = 4 * C₀^2 * (1/(s-2)^2) := by
              rw [div_pow]; ring
          _ = 4 * C₀^2 / (s-2)^2 := by rw [div_eq_mul_inv]; ring

/-! ### Step 3 of the ℓ² deep-input route: the packing bound for the entropy number -/

/-- The `ℓ²`-valued windowed curve as a set. -/
noncomputable def curveSetE (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ) :
    Set (EuclideanSpace ℂ (Fin K)) :=
  Set.range (fun t : {t : ℝ // 0 < t} => curveE Ψ f x (t : ℝ))

/-- A finite `ℓ²`-cover of the curve at radius `r`. -/
def winCoversE (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x r : ℝ)
    (S : Finset (EuclideanSpace ℂ (Fin K))) : Prop :=
  ∀ a ∈ curveSetE Ψ f x, ∃ s ∈ S, dist a s ≤ r

/-- A single `ℓ²`-ball of radius `r` covers the curve. -/
def winCoveredE (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x r : ℝ) : Prop :=
  ∃ s : EuclideanSpace ℂ (Fin K), ∀ a ∈ curveSetE Ψ f x, dist a s ≤ r

/-- The `ℓ²`-entropy number of the curve (Bourgain's convention: `0` once a single ball covers). -/
noncomputable def winEntE (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x r : ℝ) : ℝ≥0∞ := by
  classical
  exact if winCoveredE Ψ f x r then 0
    else ⨅ (S : {S : Finset (EuclideanSpace ℂ (Fin K)) // winCoversE Ψ f x r S}),
      ((S : Finset (EuclideanSpace ℂ (Fin K))).card : ℝ≥0∞)

lemma range_curveE_eq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ) :
    Set.range (fun u : ℝ => curveE Ψ f x (Real.exp u)) = curveSetE Ψ f x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact ⟨⟨Real.exp u, Real.exp_pos u⟩, rfl⟩
  · rintro _ ⟨⟨t, ht⟩, rfl⟩
    exact ⟨Real.log t, by simp [Real.exp_log ht]⟩

/-- **The packing bound.**  The `ℓ²`-entropy number of the windowed curve at radius `ρ/2` is bounded
by `(2V/ρ)^s + 1`, where `V` bounds the `ℓ²`-metric `s`-variation of the curve. -/
theorem winEntE_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s V ρ : ℝ} (hs : 1 ≤ s) (hρ : 0 < ρ) (hV : 0 ≤ V)
    (hvar : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s) ≤ V) :
    winEntE Ψ f x (ρ/2) ≤ ENNReal.ofReal ((2 * V / ρ) ^ s) + 1 := by
  classical
  have hρ2 : (0:ℝ) < ρ/2 := by linarith
  set ε : ℝ := ρ/2 with hε
  have hrange := range_curveE_eq Ψ f x
  have hA : Set.range (fun u : ℝ => curveE Ψ f x (Real.exp u)) = curveSetE Ψ f x :=
    range_curveE_eq Ψ f x
  have hpack : Metric.packingNumber ε.toNNReal
        (Set.range (fun u : ℝ => curveE Ψ f x (Real.exp u))) ≤ ((⌊(V/ε)^s⌋₊ + 1 : ℕ) : ℕ∞) :=
    Commons.Analysis.Metric.packingNumber_le (fun u : ℝ => curveE Ψ f x (Real.exp u)) hs hvar hρ2 hV
  have hne : Metric.packingNumber ε.toNNReal
      (Set.range (fun u : ℝ => curveE Ψ f x (Real.exp u))) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hpack (WithTop.coe_lt_top _))
  have hTcard : ((Metric.maximalSeparatedSet ε.toNNReal
      (Set.range (fun u : ℝ => curveE Ψ f x (Real.exp u)))).encard : ℕ∞)
      ≤ ((⌊(V/ε)^s⌋₊ + 1 : ℕ) : ℕ∞) := by
    rw [Metric.encard_maximalSeparatedSet hne]
    exact hpack
  have hTfin : (Metric.maximalSeparatedSet ε.toNNReal
      (Set.range (fun u : ℝ => curveE Ψ f x (Real.exp u)))).Finite := by
    refine Set.encard_lt_top_iff.mp (lt_of_le_of_lt hTcard ?_)
    exact WithTop.coe_lt_top _
  have hcovF : winCoversE Ψ f x ε
      (hTfin.toFinset : Finset (EuclideanSpace ℂ (Fin K))) := by
    rintro a' ha'
    rw [← hA] at ha'
    obtain ⟨c, hcC, hcd⟩ :=
      (Metric.isCover_maximalSeparatedSet hne : Metric.IsCover ε.toNNReal _ _) ha'
    refine ⟨c, by simpa using hcC, ?_⟩
    have hcd' : edist a' c ≤ (ε.toNNReal : ℝ≥0∞) := hcd
    have hcoe : ((ε.toNNReal : NNReal) : ℝ≥0∞) = ENNReal.ofReal ε := by
      rw [Real.toNNReal_of_nonneg hρ2.le]
      exact (ENNReal.ofReal_coe_nnreal (p := ⟨ε, hρ2.le⟩)).symm
    rw [edist_dist, hcoe] at hcd'
    exact (ENNReal.ofReal_le_ofReal_iff hρ2.le).mp hcd'
  have hbound : winEntE Ψ f x ε ≤ ((hTfin.toFinset.card : ℕ) : ℝ≥0∞) := by
    unfold winEntE
    by_cases hc : winCoveredE Ψ f x ε
    · rw [if_pos hc]; exact bot_le
    · rw [if_neg hc]
      exact iInf_le (fun S : {S : Finset (EuclideanSpace ℂ (Fin K)) // winCoversE Ψ f x ε S} =>
        ((S : Finset (EuclideanSpace ℂ (Fin K))).card : ℝ≥0∞)) ⟨hTfin.toFinset, hcovF⟩
  refine hbound.trans ?_
  have hcard_nat : hTfin.toFinset.card ≤ ⌊(V/ε)^s⌋₊ + 1 := by
    have h := hTcard
    rw [Set.Finite.encard_eq_coe_toFinset_card hTfin] at h
    exact_mod_cast h
  have hreal : ((hTfin.toFinset.card : ℕ) : ℝ) ≤ (2*V/ρ)^s + 1 := by
    have h1 : ((hTfin.toFinset.card : ℕ) : ℝ) ≤ ((⌊(V/ε)^s⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard_nat
    have hb : ((⌊(V/ε)^s⌋₊ : ℕ) : ℝ) ≤ (2*V/ρ)^s := by
      calc ((⌊(V/ε)^s⌋₊ : ℕ) : ℝ) ≤ (V/ε)^s :=
            Nat.floor_le (Real.rpow_nonneg (div_nonneg hV hρ2.le) s)
        _ = (2*V/ρ)^s := by rw [hε]; congr 1; ring
    calc ((hTfin.toFinset.card : ℕ) : ℝ) ≤ ((⌊(V/ε)^s⌋₊ + 1 : ℕ) : ℝ) := h1
      _ = ((⌊(V/ε)^s⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ (2*V/ρ)^s + 1 := by linarith
  calc ((hTfin.toFinset.card : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((hTfin.toFinset.card : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal ((2*V/ρ)^s + 1) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((2*V/ρ)^s) + 1 := by
        rw [ENNReal.ofReal_add (Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hV) hρ.le) s)
          zero_le_one, ENNReal.ofReal_one]


/-! ### Step 4 of the ℓ² deep-input route (the entropy-integral computation) -/

lemma lintegral_Ioc_min_le (K : ℕ) {V s r1 : ℝ} (hr1 : 0 ≤ r1) :
    ∫⁻ r in Set.Ioc (0:ℝ) r1,
        min (ENNReal.ofReal (Real.sqrt K))
          (ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s / 2)))
      ≤ ENNReal.ofReal (Real.sqrt K * r1) := by
  refine le_trans (setLIntegral_mono' measurableSet_Ioc
    (fun r _ => min_le_left _ _)) ?_
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg K)]

lemma integral_tail_eq (K : ℕ) {V s r1 : ℝ} (hV : 0 ≤ V) (hs : 2 < s) (hr1 : 0 < r1) :
    ∫⁻ r in Set.Ioi r1, ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s / 2))
      = ENNReal.ofReal (Real.sqrt 2 * V ^ (s/2) * (r1 ^ (1 - s/2) / (s/2 - 1))) := by
  have hreal : ∀ r : ℝ, 0 < r →
      Real.sqrt 2 * (V / r) ^ (s / 2) = Real.sqrt 2 * V ^ (s/2) * r ^ (-(s/2)) := by
    intro r hr0
    rw [Real.div_rpow hV (le_of_lt hr0) (s/2), div_eq_mul_inv,
      ← Real.rpow_neg (le_of_lt hr0) (s/2)]
    ring
  have hpt : ∀ r ∈ Set.Ioi r1, ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s / 2))
      = ENNReal.ofReal (Real.sqrt 2 * V ^ (s/2)) * ENNReal.ofReal (r ^ (-(s/2))) := by
    intro r hr
    rw [hreal r (lt_trans hr1 hr), ENNReal.ofReal_mul (by positivity)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Commons.MeasureTheory.Integral.lintegral_Ioi_rpow_eq (-(s/2)) r1 (by linarith) hr1]
  rw [show -(s/2) + 1 = 1 - s/2 by ring]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show -r1 ^ (1 - s/2) / (1 - s/2) = r1 ^ (1 - s/2) / (s/2 - 1) by
    rw [div_eq_div_iff (by linarith : (1:ℝ) - s/2 ≠ 0) (by linarith : s/2 - 1 ≠ 0)]
    ring]

lemma min_le_indicator_add (K : ℕ) {V s r1 : ℝ} :
    ∀ r : ℝ, Set.indicator (Set.Ioi (0:ℝ))
        (fun r => min (ENNReal.ofReal (Real.sqrt K))
          (ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s / 2)))) r
      ≤ Set.indicator (Set.Ioc (0:ℝ) r1) (fun _ => ENNReal.ofReal (Real.sqrt K)) r
        + Set.indicator (Set.Ioi r1)
            (fun r => ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s / 2))) r := by
  intro r
  by_cases h1 : r ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem h1]
    by_cases h2 : r ∈ Set.Ioc (0:ℝ) r1
    · rw [Set.indicator_of_mem h2]
      exact le_trans (min_le_left _ _) le_self_add
    · rw [Set.indicator_of_notMem h2]
      have h3 : r ∈ Set.Ioi r1 := by
        simp only [Set.mem_Ioi]
        exact lt_of_not_ge (fun hc => h2 ⟨h1, hc⟩)
      rw [Set.indicator_of_mem h3]
      exact le_trans (min_le_right _ _) le_add_self
  · rw [Set.indicator_of_notMem h1]
    exact bot_le

set_option maxHeartbeats 1600000 in
/-- **The entropy-integral computation.** -/
lemma lintegral_min_sqrt_le (K : ℕ) {V s : ℝ} (hK1 : 1 ≤ K) (hV : 0 ≤ V) (hs : 2 < s)
    (hs4 : s ≤ 4) (hKr : (K:ℝ) ^ ((1:ℝ)/2 - 1/s) ≤ 2) :
    (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
        (ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s / 2))))
      ≤ ENNReal.ofReal (16 * (2/(s-2)) * V) := by
  have hs0 : (0:ℝ) < s := by linarith
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  have hcpos : (0:ℝ) < K/2 := by
    have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK1
    linarith
  have hs2pos : (0:ℝ) < s - 2 := by linarith
  rcases eq_or_lt_of_le hV with hV0 | hVpos
  · subst hV0
    have hzero : ∀ r : ℝ, ENNReal.ofReal (Real.sqrt 2 * ((0:ℝ) / r) ^ (s / 2)) = 0 := by
      intro r
      rw [zero_div, Real.zero_rpow (by positivity : s/2 ≠ 0), mul_zero, ENNReal.ofReal_zero]
    have hz : (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
        (ENNReal.ofReal (Real.sqrt 2 * ((0:ℝ) / r) ^ (s / 2)))) = 0 := by
      rw [lintegral_congr (fun r => by rw [hzero r,
        min_eq_right (show (0:ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt K) from bot_le)]), lintegral_zero]
    rw [hz]
    exact bot_le
  · set r1 : ℝ := V / ((K/2 : ℝ) ^ (1/s)) with hr1def
    have hK2pos : 0 < ((K/2 : ℝ) ^ (1/s)) := Real.rpow_pos_of_pos hcpos _
    have hr1pos : 0 < r1 := div_pos hVpos hK2pos
    rw [← lintegral_indicator measurableSet_Ioi]
    refine le_trans (lintegral_mono (fun r =>
      min_le_indicator_add (K := K) (V := V) (s := s) (r1 := r1) r)) ?_
    rw [lintegral_add_left]
    · rw [lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioi]
      rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg K)]
      refine le_trans (add_le_add le_rfl (le_of_eq (integral_tail_eq K hV hs hr1pos))) ?_
      have hpow2 : ((2:ℝ) ^ (1/s)) ≤ 2 := by
        calc ((2:ℝ)) ^ (1/s) ≤ ((2:ℝ)) ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (by rw [div_le_one (by linarith)]; linarith)
          _ = 2 := Real.rpow_one 2
      have hKs0 : ((K:ℝ)^(1/s)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hKpos _)
      have hKt : ((K:ℝ)^((1:ℝ)/2)) * ((K:ℝ)^(1/s))⁻¹ = (K:ℝ) ^ ((1:ℝ)/2 - 1/s) := by
        rw [← div_eq_mul_inv, div_eq_iff hKs0]
        rw [← Real.rpow_add' (x := (K:ℝ)) (y := (1:ℝ)/2 - 1/s) (z := (1:ℝ)/s) hKpos.le (by
          rw [show (1:ℝ)/2 - 1/s + 1/s = (1:ℝ)/2 by ring]
          exact ne_of_gt (by norm_num : (0:ℝ) < 1/2))]
        rw [show (1:ℝ)/2 - 1/s + 1/s = (1:ℝ)/2 by ring]
      have hrecip : (1:ℝ) / ((K/2 : ℝ) ^ (1/s)) ≤ 2 / (K:ℝ) ^ (1/s) := by
        have hK2p : (0:ℝ) < ((K/2 : ℝ) ^ (1/s)) := Real.rpow_pos_of_pos hcpos _
        have hKsp : (0:ℝ) < ((K:ℝ) ^ (1/s)) := Real.rpow_pos_of_pos hKpos _
        have h2p : (0:ℝ) < ((2:ℝ) ^ (1/s)) := Real.rpow_pos_of_pos (by norm_num) _
        rw [div_le_div_iff₀ hK2p hKsp, one_mul,
          Real.div_rpow (x := (K:ℝ)) (y := (2:ℝ)) (le_of_lt hKpos) (by norm_num)]
        rw [show (2:ℝ) * ((K:ℝ)^(1/s) / (2:ℝ)^(1/s))
              = (2 / (2:ℝ)^(1/s)) * ((K:ℝ)^(1/s)) by ring]
        refine le_trans (le_mul_of_one_le_left (Real.rpow_nonneg hKpos.le _) ?_) le_rfl
        rw [le_div_iff₀ h2p]
        linarith [hpow2]
      have step2 : ((K:ℝ)^((1:ℝ)/2)) / ((K/2 : ℝ) ^ (1/s))
          ≤ 2 * ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)) := by
        have hrec : (((K/2 : ℝ) ^ (1/s)))⁻¹ ≤ 2 * ((K:ℝ)^(1/s))⁻¹ := by
          simpa only [div_eq_mul_inv, one_mul] using hrecip
        calc ((K:ℝ)^((1:ℝ)/2)) / ((K/2 : ℝ) ^ (1/s))
            = ((K:ℝ)^((1:ℝ)/2)) * (((K/2 : ℝ) ^ (1/s)))⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ ((K:ℝ)^((1:ℝ)/2)) * (2 * ((K:ℝ)^(1/s))⁻¹) :=
              mul_le_mul_of_nonneg_left hrec (Real.rpow_nonneg hKpos.le _)
          _ = 2 * ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)) := by
              rw [← mul_assoc, mul_comm ((K:ℝ)^((1:ℝ)/2)) (2:ℝ), mul_assoc, hKt]
      have h1 : Real.sqrt K * r1 ≤ 4 * V := by
        rw [hr1def, Real.sqrt_eq_rpow]
        have hstep : ((K:ℝ)^((1:ℝ)/2)) * (V / ((K/2 : ℝ) ^ (1/s)))
            = V * (((K:ℝ)^((1:ℝ)/2)) / ((K/2 : ℝ) ^ (1/s))) := by
          rw [← mul_div_assoc, mul_comm ((K:ℝ)^((1:ℝ)/2)) V, mul_div_assoc]
        refine le_trans (le_of_eq hstep) ?_
        have h2 := mul_le_mul_of_nonneg_left step2 hV
        nlinarith [h2, hKr, hV, hVpos]
      have hr1pow : r1 ^ (1 - s/2) = V ^ (1 - s/2) * ((K/2 : ℝ) ^ ((s-2)/(2*s))) := by
        rw [hr1def, Real.div_rpow hV (Real.rpow_nonneg hcpos.le _) (1 - s/2)]
        rw [div_eq_mul_inv, ← Real.rpow_neg (Real.rpow_nonneg hcpos.le _)]
        rw [← Real.rpow_mul (x := (K/2 : ℝ)) hcpos.le (1/s) (-(1 - s/2))]
        rw [show (1:ℝ)/s * (-(1 - s/2)) = (s-2)/(2*s) by field_simp; ring]
      have hc2 : ((K/2 : ℝ) ^ ((s-2)/(2*s))) ≤ 2 := by
        have h4 : (s-2)/(2*s) = (1:ℝ)/2 - 1/s := by field_simp
        rw [h4]
        refine le_trans (Real.rpow_le_rpow (by linarith) (by linarith) ?_) hKr
        rw [sub_nonneg, div_le_div_iff₀ hs0 (by norm_num)]
        linarith
      have h2 : Real.sqrt 2 * V ^ (s/2) * (r1 ^ (1 - s/2) / (s/2 - 1))
          ≤ 4 * (2/(s-2)) * V := by
        have hVprod : V ^ (s/2) * V ^ (1 - s/2) = V := by
          rw [← Real.rpow_add hVpos, show s/2 + (1 - s/2) = 1 by ring, Real.rpow_one]
        have hstep : Real.sqrt 2 * V ^ (s/2)
              * ((V ^ (1 - s/2) * ((K/2 : ℝ) ^ ((s-2)/(2*s)))) / (s/2 - 1))
            = (Real.sqrt 2 * ((K/2 : ℝ) ^ ((s-2)/(2*s)))) * (V * (1/(s/2-1))) := by
          have h1' : Real.sqrt 2 * V ^ (s/2)
                * ((V ^ (1 - s/2) * ((K/2 : ℝ) ^ ((s-2)/(2*s)))) / (s/2 - 1))
              = Real.sqrt 2 * (V ^ (s/2) * V ^ (1 - s/2))
                  * ((K/2 : ℝ) ^ ((s-2)/(2*s))) * (1/(s/2-1)) := by ring
          rw [h1', hVprod]
          ring
        rw [hr1pow, hstep]
        have h6 : 0 ≤ 1/(s/2 - 1) := div_nonneg zero_le_one (by linarith)
        have h7 : Real.sqrt 2 * ((K/2 : ℝ) ^ ((s-2)/(2*s))) ≤ 4 := by
          have h8 : Real.sqrt 2 ≤ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
          nlinarith [h8, hc2, Real.sqrt_nonneg 2, Real.rpow_nonneg hcpos.le ((s-2)/(2*s))]
        have hdiv : (2:ℝ)/(s-2) = 1/(s/2-1) := by field_simp
        rw [← hdiv]
        have hpos : 0 ≤ V * (2/(s-2)) := mul_nonneg hV (by positivity)
        calc √2 * ((K/2 : ℝ) ^ ((s-2)/(2*s))) * (V * (2/(s-2)))
            = (√2 * ((K/2 : ℝ) ^ ((s-2)/(2*s)))) * (V * (2/(s-2))) := by ring
          _ ≤ 4 * (V * (2/(s-2))) := mul_le_mul_of_nonneg_right h7 hpos
          _ = 4 * (2/(s-2)) * V := by ring
      have h3 : 0 ≤ Real.sqrt K * r1 := mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hr1pos)
      have h4 : 0 ≤ Real.sqrt 2 * V ^ (s/2) * (r1 ^ (1 - s/2) / (s/2 - 1)) := by
        apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hV _))
        exact div_nonneg (Real.rpow_nonneg (le_of_lt hr1pos) _) (by linarith)
      rw [← ENNReal.ofReal_add h3 h4]
      refine le_trans (ENNReal.ofReal_le_ofReal (add_le_add h1 h2)) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hge : (1:ℝ) ≤ 2/(s-2) := by rw [le_div_iff₀ hs2pos]; linarith
      nlinarith [hV, hge]
    · exact Measurable.indicator measurable_const measurableSet_Ioc

/-! ### The ℓ²-metric entropy input (the deep input of Bourgain's §3/§4) -/

/-- The `ℓ²`-metric entropy number of the windowed curve is zero once one ball covers it (the
convention that makes the entropy integral finite). -/
lemma winEntE_eq_zero (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x r : ℝ)
    (h : winCoveredE Ψ f x r) : winEntE Ψ f x r = 0 := by
  unfold winEntE
  rw [if_pos h]

/-- Translating the `ℓ²`-metric `s`-variation into a real bound. -/
lemma vecVarE_toReal_bound (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s : ℝ} (hV : vecVarE Ψ f x s ≠ ⊤) :
    ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s)
        ≤ (vecVarE Ψ f x s).toReal := by
  intro J u hu
  have h1 : ENNReal.ofReal ((∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s))
      ≤ vecVarE Ψ f x s := by
    unfold vecVarE
    exact le_iSup_of_le J (le_iSup_of_le u (le_iSup_of_le hu le_rfl))
  rwa [ENNReal.ofReal_le_iff_le_toReal hV] at h1

/-- The two-point chain: the `ℓ²`-diameter of the curve is at most the `s`-variation bound. -/
lemma dist_curveE_le_of_var (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s V : ℝ} (hs0 : 0 < s)
    (hvar : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
        (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s) ≤ V) :
    ∀ ta tb : ℝ, 0 < ta → 0 < tb → dist (curveE Ψ f x ta) (curveE Ψ f x tb) ≤ V := by
  have hV0 : 0 ≤ V := by
    have h := hvar 0 (fun _ : Fin 1 => (0:ℝ)) (fun i j hij => absurd hij (by omega))
    simpa [Real.zero_rpow (ne_of_gt (inv_pos.mpr hs0))] using h
  intro ta tb hta htb
  rcases lt_trichotomy ta tb with h | h | h
  · have hu : StrictMono (fun i : Fin 2 => if i = 0 then Real.log ta else Real.log tb) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
      exact Real.log_lt_log hta h
    have hv := hvar 1 (fun i : Fin 2 => if i = 0 then Real.log ta else Real.log tb) hu
    have h1 : (dist (curveE Ψ f x ta) (curveE Ψ f x tb) ^ s) ^ ((1:ℝ)/s) ≤ V := by
      simpa [Fin.sum_univ_one, Real.exp_log hta, Real.exp_log htb] using hv
    have h2 : (dist (curveE Ψ f x ta) (curveE Ψ f x tb) ^ s) ^ ((1:ℝ)/s)
        = dist (curveE Ψ f x ta) (curveE Ψ f x tb) := by
      rw [← Real.rpow_mul dist_nonneg, mul_one_div, div_self (ne_of_gt hs0), Real.rpow_one]
    rwa [h2] at h1
  · subst h
    simpa using hV0
  · have hu : StrictMono (fun i : Fin 2 => if i = 0 then Real.log tb else Real.log ta) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]
      exact Real.log_lt_log htb h
    have hv := hvar 1 (fun i : Fin 2 => if i = 0 then Real.log tb else Real.log ta) hu
    have h1 : (dist (curveE Ψ f x tb) (curveE Ψ f x ta) ^ s) ^ ((1:ℝ)/s) ≤ V := by
      simpa [Fin.sum_univ_one, Real.exp_log hta, Real.exp_log htb] using hv
    have h2 : (dist (curveE Ψ f x tb) (curveE Ψ f x ta) ^ s) ^ ((1:ℝ)/s)
        = dist (curveE Ψ f x tb) (curveE Ψ f x ta) := by
      rw [← Real.rpow_mul dist_nonneg, mul_one_div, div_self (ne_of_gt hs0), Real.rpow_one]
    rw [h2] at h1
    rwa [dist_comm] at h1

/-- **The `ℓ²`-metric entropy input (Bourgain's §3 entropy integral, dyadic form).**

For a Schwartz window `Ψ` and a `K`-tuple of `L² ∩ L^∞` functions there is an absolute constant `C`
with `∫ₓ (∫ᵣ min(√K, Mᵣ(x)^{1/2}) dr)² dx ≤ C (log(K+2))⁴ ∫ₓ ∑_k |f_k(x)|²`, where `Mᵣ = winEntE`
is the `ℓ²`-metric entropy number of the windowed curve at scale `r`.

This is the ℓ²-metric version of Bourgain's §3 entropy input: the statement whose sup-metric
counterpart (`bourgain_entropy_integral_l2_fixed`) does *not* suffice for the ℓ²-metric chain
`chain_curvePt_bound_scaled`. -/
theorem l2_entropy_input_dyadic (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MeasureTheory.MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MeasureTheory.MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K)) ((winEntE Ψ f x r) ^ ((1:ℝ)/2))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
  obtain ⟨Cv, hCvpos, hCv⟩ := lintegral_vecVarE_sq_le Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Fourier.dilation_variation_scalar_l2 Ψ
  refine ⟨10 ^ 40 * (Cv + 1), by positivity, ?_⟩
  intro K f hf2 hfinf
  -- finiteness of the `L²`-mass of the tuple
  have hAk : ∀ k : Fin K, ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖^2) < ⊤ := by
    intro k
    have hint : Integrable (fun x : ℝ => ‖f k x‖ ^ 2) volume := by
      have h := (hf2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
      simpa using h
    simpa only [Commons.Analysis.Fourier.enorm_eq_ofReal_norm'] using hint.lintegral_lt_top
  have hAfin : (∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2)) < ⊤ := by
    rw [show (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2))
        = fun x : ℝ => ∑ k : Fin K, ENNReal.ofReal (‖f k x‖^2) from
      funext fun x => ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    rw [lintegral_finsetSum' _ (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
    exact ENNReal.sum_lt_top.mpr (fun k _ => hAk k)
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have hz : ENNReal.ofReal (Real.sqrt ((0:ℕ):ℝ)) = 0 := by simp
    have hint : ∀ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt ((0:ℕ):ℝ)))
        ((winEntE Ψ f x r) ^ ((1:ℝ)/2))) = 0 := by
      intro x
      simp [hz]
    have hsq : (∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt ((0:ℕ):ℝ)))
        ((winEntE Ψ f x r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) = 0 := by
      simp only [hint, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2), lintegral_zero]
    rw [hsq]
    exact bot_le
  · have hK1 : 1 ≤ K := hKpos
    set L : ℝ := max 1 (Real.log ((K:ℝ)+2)) with hL
    have hL1 : 1 ≤ L := le_max_left _ _
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    set s : ℝ := 2 + 1/L with hs
    have hs0 : (0:ℝ) < s := by rw [hs]; positivity
    have hs2 : 2 < s := by rw [hs]; exact lt_add_of_pos_right _ (one_div_pos.mpr hLpos)
    have hs3 : s ≤ 3 := by
      rw [hs]
      have h1 : 1/L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
      linarith
    have hs4 : s ≤ 4 := by linarith
    have hs1 : 1 ≤ s := by linarith
    have hsne : s - 2 = 1/L := by rw [hs]; ring
    have hLval : 1/(s-2) = L := by rw [hsne, one_div_one_div]
    have hKexp : (K:ℝ) ^ ((1:ℝ)/2 - 1/s) ≤ 2 := by
      have h := Commons.Analysis.Fourier.rpow_half_sub_inv_le_two K
      rwa [← hL, ← hs] at h
    have hKr : (K:ℝ) ^ ((s-2)/s) ≤ 4 := by
      have h2 : (K:ℝ) ^ ((s-2)/s) = ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)) ^ (2:ℝ) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg K)]
        congr 1
        rw [hsne, hs]
        field_simp
        ring
      rw [h2]
      calc ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)) ^ (2:ℝ)
          = ((K:ℝ) ^ ((1:ℝ)/2 - 1/s)) ^ (2:ℕ) := by
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        _ ≤ 2 ^ (2:ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg K) _) hKexp 2
        _ = 4 := by norm_num
    have hstep2 := hCv K f hf2 hfinf hs2 hs3 hKr
    -- a.e. finiteness of the scalar variations
    have hmeas : ∀ k : Fin K, AEMeasurable
        (fun x : ℝ => (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) volume := by
      intro k
      exact ((Commons.Analysis.Fourier.dilation_variation_aemeasurable Ψ s (f k)
        (hf2 k).aemeasurable (hf2 k)).pow_const 2)
    have hfinv : ∀ k : Fin K,
        ∫⁻ x : ℝ, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ) < ⊤ := by
      intro k
      refine lt_of_le_of_lt (hC₀ s hs2 hs3 (f k) (hf2 k) (hfinf k))
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hAk k))
    have hae_k : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : Fin K,
        (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ) < ⊤ := by
      rw [Filter.eventually_all]
      intro k
      exact ae_lt_top' (hmeas k) (ne_of_lt (hfinv k))
    have haefin : ∀ᵐ x ∂(volume : Measure ℝ), vecVarE Ψ f x s ≠ ⊤ := by
      filter_upwards [hae_k] with x hx
      have hsx : (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) < ⊤ :=
        ENNReal.sum_lt_top.mpr (fun k _ => hx k)
      intro htop
      have hle := vecVarE_le Ψ f x hs2
      rw [htop] at hle
      have hmax : (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2)
          ≤ max 1 (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) := by
        rcases le_total (1 : ℝ≥0∞)
          (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) with h' | h'
        · calc (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2)
              ≤ (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ (1:ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le h' (by norm_num)
            _ = (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) :=
                ENNReal.rpow_one _
            _ ≤ max 1 (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) :=
                le_max_right _ _
        · calc (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2)
              ≤ (1 : ℝ≥0∞) ^ ((1:ℝ)/2) := ENNReal.rpow_le_rpow h' (by norm_num)
            _ = 1 := ENNReal.one_rpow _
            _ ≤ max 1 (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) :=
                le_max_left _ _
      have hrhs : ENNReal.ofReal ((K:ℝ) ^ ((1:ℝ)/2 - 1/s))
          * (∑ k : Fin K, (Commons.Analysis.Fourier.winVar Ψ (f k) x s) ^ (2:ℝ)) ^ ((1:ℝ)/2) ≠ ⊤ := by
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
        refine ne_of_lt (lt_of_le_of_lt hmax ?_)
        rw [max_lt_iff]
        exact ⟨ENNReal.one_lt_top, hsx⟩
      exact absurd hle (not_le.mpr (lt_top_iff_ne_top.mpr hrhs))
    -- the per-`x` bound on the entropy integral
    have hper : ∀ᵐ x ∂(volume : Measure ℝ),
        (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K)) ((winEntE Ψ f x r) ^ ((1:ℝ)/2)))
          ≤ ENNReal.ofReal (16 * (2/(s-2)) * (vecVarE Ψ f x s).toReal) := by
      filter_upwards [haefin] with x hV
      set V : ℝ := (vecVarE Ψ f x s).toReal with hVdef
      have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
      have hvar : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
          (∑ j : Fin J, dist (curveE Ψ f x (Real.exp (u (Fin.castSucc j))))
            (curveE Ψ f x (Real.exp (u (Fin.succ j)))) ^ s) ^ ((1:ℝ)/s) ≤ V := by
        rw [hVdef]; exact vecVarE_toReal_bound Ψ f x hV
      have hcov : ∀ r : ℝ, V ≤ r → winCoveredE Ψ f x r := by
        intro r hr
        refine ⟨curveE Ψ f x 1, fun a ha => ?_⟩
        rcases ha with ⟨⟨t, ht⟩, rfl⟩
        exact le_trans (dist_curveE_le_of_var Ψ f x hs0 hvar t 1 ht one_pos) hr
      have hpoint : ∀ r ∈ Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K)) ((winEntE Ψ f x r) ^ ((1:ℝ)/2))
            ≤ min (ENNReal.ofReal (Real.sqrt K))
                (ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s/2))) := by
        intro r hr
        rcases le_total V r with hcase | hcase
        · rw [winEntE_eq_zero Ψ f x r (hcov r hcase),
              ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)]
          simp
        · have hrpos : 0 < r := hr
          have hbb := winEntE_le Ψ f x hs1 (by linarith : (0:ℝ) < 2*r) hVnn
            (fun J u hu => hvar J u hu)
          rw [show 2 * r / 2 = r by ring, show 2 * V / (2 * r) = V / r by field_simp] at hbb
          have hVr : (1:ℝ) ≤ V / r := by rw [le_div_iff₀ hrpos]; linarith
          have h1 : (1:ℝ) ≤ (V / r) ^ s := Real.one_le_rpow hVr hs0.le
          have h2 : ENNReal.ofReal ((V/r) ^ s) + 1 ≤ 2 * ENNReal.ofReal ((V/r) ^ s) := by
            rw [two_mul]
            exact add_le_add le_rfl (ENNReal.one_le_ofReal.mpr h1)
          have hsplit : ((2:ℝ≥0∞) * ENNReal.ofReal ((V / r) ^ s)) ^ ((1:ℝ)/2)
              = ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s/2)) := by
            rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
              ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
                (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
              ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (div_nonneg hVnn hrpos.le) s)
                (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
              show (2:ℝ) ^ ((1:ℝ)/2) = Real.sqrt 2 from by rw [Real.sqrt_eq_rpow],
              ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
            congr 1
            rw [← Real.rpow_mul (div_nonneg hVnn hrpos.le)]
            congr 1
            ring_nf
          have h3 : (winEntE Ψ f x r) ^ ((1:ℝ)/2)
              ≤ ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s/2)) := by
            rw [← hsplit]
            exact ENNReal.rpow_le_rpow (hbb.trans h2) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
          exact min_le_min le_rfl h3
      calc (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
            ((winEntE Ψ f x r) ^ ((1:ℝ)/2)))
          ≤ ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
              (ENNReal.ofReal (Real.sqrt 2 * (V / r) ^ (s/2))) :=
            setLIntegral_mono' measurableSet_Ioi hpoint
        _ ≤ ENNReal.ofReal (16 * (2/(s-2)) * V) := lintegral_min_sqrt_le K hK1 hVnn hs2 hs4 hKexp
    -- integrate the square in `x`
    have hαpos : (0:ℝ) < 16 * (2/(s-2)) := by positivity
    have hcoef : (ENNReal.ofReal (16 * (2/(s-2)))) ^ (2:ℝ)
        = ENNReal.ofReal ((16 * (2/(s-2)))^2) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      exact (ENNReal.ofReal_pow hαpos.le 2).symm
    have heq : ∀ᵐ x ∂(volume : Measure ℝ),
        ENNReal.ofReal (16 * (2/(s-2)) * (vecVarE Ψ f x s).toReal) ^ (2:ℝ)
          = ENNReal.ofReal ((16 * (2/(s-2)))^2) * (vecVarE Ψ f x s) ^ (2:ℝ) := by
      filter_upwards [haefin] with x hV
      rw [ENNReal.ofReal_mul hαpos.le, ENNReal.ofReal_toReal hV,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), hcoef]
    calc (∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
            ((winEntE Ψ f x r) ^ ((1:ℝ)/2))) ^ (2:ℝ))
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal (16 * (2/(s-2)) * (vecVarE Ψ f x s).toReal) ^ (2:ℝ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hper] with x hx
          exact ENNReal.rpow_le_rpow hx (by norm_num : (0:ℝ) ≤ 2)
      _ = ENNReal.ofReal ((16 * (2/(s-2)))^2)
            * (∫⁻ x : ℝ, (vecVarE Ψ f x s) ^ (2:ℝ)) := by
          rw [lintegral_congr_ae heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((16 * (2/(s-2)))^2)
            * (ENNReal.ofReal (Cv / (s-2)^2)
                * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2)) :=
          mul_le_mul_right hstep2 _
      _ ≤ ENNReal.ofReal ((10 ^ 40 * (Cv + 1) * (Real.log ((K:ℝ)+2))^2)^2)
            * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg (16 * (2/(s-2))))]
          refine mul_le_mul_left ?_ _
          refine ENNReal.ofReal_le_ofReal ?_
          have hlogpos : 0 < Real.log ((K:ℝ)+2) := by
            refine Real.log_pos ?_
            have hh : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK1
            linarith
          have hLle : L ≤ 200 * Real.log ((K:ℝ)+2) := by
            rw [hL]; exact Commons.Analysis.Fourier.max_one_log_le K
          have hL4 : L^4 ≤ (200 * Real.log ((K:ℝ)+2))^4 :=
            pow_le_pow_left₀ hLpos.le hLle 4
          have hrew : (16 * (2/(s-2)))^2 * (Cv/(s-2)^2) = 1024 * Cv * (1/(s-2))^4 := by
            field_simp
            ring
          rw [hrew, hLval]
          calc 1024 * Cv * L^4
              ≤ 1024 * Cv * (200 * Real.log ((K:ℝ)+2))^4 :=
                mul_le_mul_of_nonneg_left hL4 (by positivity)
            _ = 1024 * Cv * 200^4 * (Real.log ((K:ℝ)+2))^4 := by ring
            _ ≤ 10^80 * (Cv+1)^2 * (Real.log ((K:ℝ)+2))^4 := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                nlinarith [hCvpos, sq_nonneg (Cv + 1), sq_nonneg Cv]
            _ = (10 ^ 40 * (Cv + 1) * (Real.log ((K:ℝ)+2))^2)^2 := by ring

end FWDeep
#print axioms FWDeep.l2_entropy_input_dyadic

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/EntropyFin.lean ====

set_option maxHeartbeats 2000000

namespace FWS

open OldSWM.BourgainMax
open OldSWM Commons.Analysis.Fourier
open _root_.MeasureTheory _root_.Finset
open scoped BigOperators ENNReal Topology

noncomputable section

/-- **The windowed curve is bounded.**  With `‖H k‖ ≤ M` a.e. and `Ψ` finitely integrable, every
point of the curve `t ↦ (∫ y, H k y * (t⁻¹ • Ψ((z-y)/t)))_k` has `ℓ^∞`-norm at most
`M * ∫‖Ψ‖`. -/
lemma winCurve_enorm_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hH : ∀ k : Fin K, ∀ᵐ y ∂(volume : Measure ℝ), ‖H k y‖ ≤ M) (z : ℝ) :
    ∀ a ∈ winCurve K (⇑Ψ) H z, ∀ k : Fin K,
      ‖a k‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u : ℝ, ‖(Ψ : ℝ → ℂ) u‖ₑ := by
  rintro a ⟨⟨t, ht⟩, rfl⟩ k
  have hpos : 0 < t := ht
  have hnorm : ‖((t:ℝ)⁻¹ : ℝ)‖ₑ = ENNReal.ofReal t⁻¹ := by
    rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg (inv_nonneg.mpr hpos.le), ENNReal.ofReal,
      Real.toNNReal_of_nonneg (inv_nonneg.mpr hpos.le)]
  have hmeas : Measurable (fun y : ℝ => ‖((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ) :=
    (by fun_prop : Continuous fun y : ℝ => ((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))).enorm.measurable
  have hae : ∀ᵐ y ∂(volume : Measure ℝ),
      ‖H k y * ((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ
        ≤ ENNReal.ofReal M * ‖((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ := by
    filter_upwards [hH k] with y hy
    rw [enorm_mul, enorm_eq_ofReal_norm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hy) le_rfl
  have hsmul : ∀ y : ℝ, ‖((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ
      = ENNReal.ofReal t⁻¹ * ‖(Ψ : ℝ → ℂ) ((z - y)/t)‖ₑ := by
    intro y
    rw [enorm_smul, hnorm]
  calc ‖∫ y, H k y * ((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ
      ≤ ∫⁻ y, ‖H k y * ((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal M * ‖((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ :=
        lintegral_mono_ae hae
    _ = ENNReal.ofReal M * ∫⁻ y, ‖((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ :=
        lintegral_const_mul (f := fun y : ℝ => ‖((t:ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - y)/t))‖ₑ) _ hmeas
    _ = ENNReal.ofReal M * ∫⁻ y, ENNReal.ofReal t⁻¹ * ‖(Ψ : ℝ → ℂ) ((z - y)/t)‖ₑ := by
        simp only [hsmul]
    _ = ENNReal.ofReal M * (ENNReal.ofReal t⁻¹ * ∫⁻ y, ‖(Ψ : ℝ → ℂ) ((z - y)/t)‖ₑ) := by
        rw [lintegral_const_mul (f := fun y : ℝ => ‖(Ψ : ℝ → ℂ) ((z - y)/t)‖ₑ) _
          ((continuous_enorm.comp (by fun_prop)).measurable)]
    _ = ENNReal.ofReal M * (ENNReal.ofReal t⁻¹
          * (ENNReal.ofReal t * ∫⁻ u, ‖(Ψ : ℝ → ℂ) u‖ₑ)) := by
        rw [BourgainWindow.lintegral_comp_div_sub (fun u : ℝ => ‖(Ψ : ℝ → ℂ) u‖ₑ)
          ((continuous_enorm.comp (by fun_prop)).measurable) z hpos]
    _ = ENNReal.ofReal M * ∫⁻ u, ‖(Ψ : ℝ → ℂ) u‖ₑ := by
        have hcancel : ENNReal.ofReal t⁻¹ * (ENNReal.ofReal t * ∫⁻ u, ‖(Ψ : ℝ → ℂ) u‖ₑ)
            = ∫⁻ u, ‖(Ψ : ℝ → ℂ) u‖ₑ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hpos)),
            inv_mul_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one, one_mul]
        rw [hcancel]

end
end FWS

namespace FWS

open OldSWM.BourgainMax
open OldSWM Commons.Analysis.Fourier
open _root_.MeasureTheory _root_.Finset
open scoped BigOperators ENNReal Topology

noncomputable section

/-- **The covering numbers of the windowed curve are finite.**  If `‖H k‖ ≤ M` a.e. then the
curve is contained in a ball of radius `M ∫‖Ψ‖`, hence totally bounded, so it has finite covering
numbers at every positive radius. -/
lemma winEntropy_ne_top (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hH : ∀ k : Fin K, ∀ᵐ y ∂(volume : Measure ℝ), ‖H k y‖ ≤ M) (z : ℝ) {r : ℝ}
    (hr : 0 < r) : winEntropy K (⇑Ψ) H z r ≠ ⊤ := by
  classical
  have hint : Integrable (fun u : ℝ => ‖(Ψ : ℝ → ℂ) u‖) (volume : Measure ℝ) :=
    (SchwartzMap.integrable (μ := (volume : Measure ℝ)) Ψ).norm
  have hI : ∫⁻ u : ℝ, ‖(Ψ : ℝ → ℂ) u‖ₑ
      = ENNReal.ofReal (∫ u : ℝ, ‖(Ψ : ℝ → ℂ) u‖) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => norm_nonneg _)]
    exact lintegral_congr fun u => enorm_eq_ofReal_norm _
  set R : ℝ := M * ∫ u : ℝ, ‖(Ψ : ℝ → ℂ) u‖ with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    exact mul_nonneg hM (integral_nonneg fun u => norm_nonneg _)
  obtain ⟨S, hS⟩ := exists_finset_l2_cover_of_bounded (winCurve K (⇑Ψ) H z) R hRnn
    (fun a ha k => by
      have h1 := winCurve_enorm_le Ψ H hM hH z a ha k
      rw [hI, ← ENNReal.ofReal_mul hM, ← hR, enorm_eq_ofReal_norm] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hRnn).mp h1) hr
  have hcov : winCovers K (⇑Ψ) H z r S := fun a ha => hS a ha
  unfold winEntropy
  by_cases hc : winCovered K (⇑Ψ) H z r
  · rw [if_pos hc]
    exact ENNReal.zero_ne_top
  · rw [if_neg hc]
    refine ne_of_lt (lt_of_le_of_lt (iInf_le _ ⟨S, hcov⟩) ?_)
    exact lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top S.card)

end
end FWS

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/Step.lean ====
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The entropy step of Bourgain's Lemma 4.13 (smooth-window maximal estimate)

Scratch assembly file for the fixed-bump crux of
`Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2`.

* `chain_exp_sum_le_entropy_scaled` — the `D`-scaled form of the published chain bound.
-/

set_option maxHeartbeats 2000000

namespace FWS

open OldSWM.BourgainMax
open OldSWM Commons.Analysis.Fourier
open _root_.MeasureTheory _root_.Finset
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The exponential-sum integrand of the chain bound, for the family `a`. -/
def expSup {N K : ℕ} (lam : Fin K → ℝ) (a : Fin (N+1) → Fin K → ℂ) (y : ℝ) : ℝ :=
  ⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖

/-- **The `D`-scaled chain bound.**  The published
`Commons.Analysis.Fourier.chain_exp_sum_le_entropy` bounds the mean square over `y ∈ (0,1]` of
the maximal exponential sum `⨆ i, ‖∑ k, a i k · e^{iλ_k y}‖` for a family `a` of `ℓ²`-radius at
most `1`.  Here the family has `ℓ²`-diameter `D`: the estimate is rescaled by `D`. -/
theorem chain_exp_sum_le_entropy_scaled (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ C ≤ ESU.cChain ∧ ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ) {D : ℝ}, 0 < D →
      1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      (N+1) ≤ M S →
      (∀ i : Fin (N+1), ∑ k : Fin K, ‖a i k - a (σ 0 0) k‖ ^ 2 ≤ D ^ 2) →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * D * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (expSup lam a y) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + D * ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  set C₀ : ℝ := ESU.cChain with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; exact ESU.cChain_pos
  have hC₀ : ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
      (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ), 1 ≤ S →
    (∀ i : Fin (N+1), σ 0 i = σ 0 0) → (N+1) ≤ M S →
    (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
    (∀ t, t ≤ S → ∀ i : Fin (N+1),
      ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
    ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (expSup lam a y) ^ 2
      ≤ ENNReal.ofReal ((C₀ * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
          + ∑ t ∈ Finset.range (S+1),
              (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
    intro N S a σ M hS hconst hNM hcard hnet2
    have h := ESU.chain_exp_sum_le_entropy_const K lam hsep N S a σ M hS hconst hNM hcard hnet2
    simpa only [hC₀def, expSup, ESU.cChain] using h
  refine ⟨C₀, hC₀pos, ?_, ?_⟩
  · rw [hC₀def]
  intro N S a σ M D hD hS hconst hNM hball hcard hnet
  have hDc : ((D:ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]; exact ne_of_gt hD
  set a' : Fin (N+1) → Fin K → ℂ := fun i k => ((D:ℂ))⁻¹ * a i k with ha'
  have ha'_apply : ∀ i k, a' i k = ((D:ℂ))⁻¹ * a i k := fun i k => rfl
  -- the normalized family satisfies the required net property
  have hnet' : ∀ t, t ≤ S → ∀ i : Fin (N+1),
      ∑ k : Fin K, ‖a' i k - a' (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2 := by
    intro t ht i
    have hterm : ∀ k : Fin K, ‖a' i k - a' (σ t i) k‖ = D⁻¹ * ‖a i k - a (σ t i) k‖ := by
      intro k
      have he : a' i k - a' (σ t i) k = ((D:ℂ))⁻¹ * (a i k - a (σ t i) k) := by
        rw [ha'_apply, ha'_apply]; ring
      rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    calc ∑ k : Fin K, ‖a' i k - a' (σ t i) k‖ ^ 2
        = ∑ k : Fin K, (D⁻¹)^2 * ‖a i k - a (σ t i) k‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hterm k]; ring
      _ = (D⁻¹)^2 * ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (D⁻¹)^2 * (2 * D * (1/2:ℝ)^t)^2 := mul_le_mul_of_nonneg_left (hnet t ht i) (by positivity)
      _ = (2 * (1/2:ℝ)^t)^2 := by
          rw [← mul_pow]
          congr 1
          rw [show D⁻¹ * (2 * D * (1/2:ℝ)^t) = (D⁻¹ * D) * (2 * (1/2:ℝ)^t) by ring,
            inv_mul_cancel₀ (ne_of_gt hD), one_mul]
  have hmain := hC₀ N S a' σ M hS hconst hNM (fun t ht => hcard t ht) hnet'
  -- scaling back: `‖∑ a e‖ = D · ‖∑ a' e‖`
  have hXle : ∀ y : ℝ, expSup lam a y ≤ D * expSup lam a' y := by
    intro y
    refine ciSup_le (fun i => ?_)
    have h1 : (∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ)))
        = (D:ℂ) * ∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [ha'_apply]
      field_simp
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    exact mul_le_mul_of_nonneg_left
      (le_ciSup (f := fun i : Fin (N+1) =>
          ‖∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖)
        ⟨∑ i : Fin (N+1), ‖∑ k : Fin K,
            a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖,
          by
            rintro _ ⟨j, rfl⟩
            show ‖∑ k : Fin K, a' j k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖
              ≤ ∑ i : Fin (N+1), ‖∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖
            exact Finset.single_le_sum
              (f := fun i : Fin (N+1) => ‖∑ k : Fin K,
                a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖)
              (fun l _ => norm_nonneg _) (Finset.mem_univ j)⟩ i) hD.le
  -- the mean-square comparison
  have hpt : ∀ y : ℝ,
      ENNReal.ofReal (expSup lam a y) ^ 2
        ≤ (ENNReal.ofReal D) ^ 2 * ENNReal.ofReal (expSup lam a' y) ^ 2 := by
    intro y
    have h1 : ENNReal.ofReal (expSup lam a y)
        ≤ ENNReal.ofReal D * ENNReal.ofReal (expSup lam a' y) := by
      rw [← ENNReal.ofReal_mul hD.le]
      exact ENNReal.ofReal_le_ofReal (hXle y)
    calc ENNReal.ofReal (expSup lam a y) ^ 2
        ≤ (ENNReal.ofReal D * ENNReal.ofReal (expSup lam a' y)) ^ 2 :=
          pow_le_pow_left₀ bot_le h1 2
      _ = (ENNReal.ofReal D) ^ 2 * ENNReal.ofReal (expSup lam a' y) ^ 2 := by ring
  have hstep : (∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (expSup lam a y) ^ 2)
      ≤ (ENNReal.ofReal D) ^ 2 * (∫⁻ y in Set.Ioc (0:ℝ) 1,
          ENNReal.ofReal (expSup lam a' y) ^ 2) := by
    set Fa : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (expSup lam a y) ^ 2 with hFa
    set Ga : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (expSup lam a' y) ^ 2 with hGa
    calc ∫⁻ y in Set.Ioc (0:ℝ) 1, Fa y
        = ∫⁻ y : ℝ, (Set.Ioc (0:ℝ) 1).indicator Fa y :=
          (lintegral_indicator measurableSet_Ioc Fa).symm
      _ ≤ ∫⁻ y : ℝ, (Set.Ioc (0:ℝ) 1).indicator
            (fun y : ℝ => (ENNReal.ofReal D) ^ 2 * Ga y) y := by
          refine lintegral_mono (fun y => ?_)
          by_cases hy : y ∈ Set.Ioc (0:ℝ) 1
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hpt y
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      _ = ∫⁻ y : ℝ, (ENNReal.ofReal D) ^ 2 *
            (Set.Ioc (0:ℝ) 1).indicator Ga y := by
          apply lintegral_congr; intro y
          by_cases hy : y ∈ Set.Ioc (0:ℝ) 1
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp
      _ = (ENNReal.ofReal D) ^ 2 * (∫⁻ y : ℝ, (Set.Ioc (0:ℝ) 1).indicator Ga y) :=
          lintegral_const_mul' _ _ (by simp)
      _ = (ENNReal.ofReal D) ^ 2 * (∫⁻ y in Set.Ioc (0:ℝ) 1, Ga y) := by
          rw [lintegral_indicator measurableSet_Ioc]
  refine hstep.trans ?_
  have hA : D * Real.sqrt (∑ k : Fin K, ‖a' (σ 0 0) k‖ ^ 2)
      = Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2) := by
    have hterm : ∀ k : Fin K, ‖a' (σ 0 0) k‖ = D⁻¹ * ‖a (σ 0 0) k‖ := by
      intro k
      have he : a' (σ 0 0) k = ((D:ℂ))⁻¹ * a (σ 0 0) k := ha'_apply _ _
      rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    have hsum : (∑ k : Fin K, ‖a' (σ 0 0) k‖ ^ 2)
        = (D⁻¹)^2 * ∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2 := by
      calc ∑ k : Fin K, ‖a' (σ 0 0) k‖ ^ 2
          = ∑ k : Fin K, (D⁻¹)^2 * ‖a (σ 0 0) k‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hterm k]; ring
        _ = (D⁻¹)^2 * ∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2 := by rw [Finset.mul_sum]
    rw [hsum, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (D⁻¹)^2),
      show Real.sqrt ((D⁻¹)^2) = D⁻¹ from Real.sqrt_sq (by positivity),
      ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hD), one_mul]
  rw [← ENNReal.ofReal_pow hD.le 2]
  have h1 : ENNReal.ofReal (D^2) * (∫⁻ y in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (expSup lam a' y) ^ 2)
      ≤ ENNReal.ofReal (D^2) * ENNReal.ofReal ((C₀ * (Real.sqrt (∑ k : Fin K, ‖a' (σ 0 0) k‖ ^ 2)
          + ∑ t ∈ Finset.range (S+1),
              (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) :=
    mul_le_mul_right hmain _
  refine h1.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (sq_nonneg D)]
  congr 1
  have hrw : D^2 * (C₀ * (Real.sqrt (∑ k : Fin K, ‖a' (σ 0 0) k‖^2)
        + ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ)+1))))^2
      = (C₀ * (D * Real.sqrt (∑ k : Fin K, ‖a' (σ 0 0) k‖^2)
        + D * ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ)+1))))^2 := by
    ring
  rw [hrw, hA]

/-- **Bourgain's bootstrap with an *adaptive* shift.**  The chain bound controls the `y`-average of
`bandMax (transl H y)`, hence only *existence* of a good shift `y ∈ [-δ,δ]` with
`bandMax (transl H y) ≤ A · bandSq H`; the good shift may be chosen afresh at each step of the
iteration.  Given the one-step inequality (subadditivity of `bandMax`), the energy contraction for
`H ↦ H - transl H y` (`|y| ≤ δ`), and the a priori bound, we get
`bandMax H ≤ (2A/(1-2θ²) + δ') · bandSq H` for every `δ' > 0`. -/
theorem bandMax_le_of_good_shift (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    {A θ CK δ δ' : ℝ} (hA : 0 < A) (hθ0 : 0 ≤ θ) (hθ : 2 * θ ^ 2 < 1) (hCK : 0 ≤ CK)
    (hδ' : 0 < δ')
    (Adm : (Fin K → ℝ → ℂ) → Prop)
    (hpres : ∀ H, Adm H → ∀ y, |y| ≤ δ → Adm (fun k u => H k u - H k (u + y)))
    (hgood : ∀ H, Adm H → ∃ y : ℝ, |y| ≤ δ ∧
        bandMax Ψ lam (transl H y) ≤ ENNReal.ofReal A * bandSq H)
    (hcon : ∀ H, Adm H → ∀ y, |y| ≤ δ →
        bandSq (fun k u => H k u - H k (u + y)) ≤ ENNReal.ofReal (θ ^ 2) * bandSq H)
    (hsub : ∀ H, Adm H → ∀ y, |y| ≤ δ → bandMax Ψ lam H
        ≤ 2 * bandMax Ψ lam (transl H y) + 2 * bandMax Ψ lam (fun k u => H k u - H k (u + y)))
    (hap : ∀ H, Adm H → bandMax Ψ lam H ≤ ENNReal.ofReal CK * bandSq H)
    (H : Fin K → ℝ → ℂ) (hH : Adm H) :
    bandMax Ψ lam H ≤ ENNReal.ofReal (2 * A / (1 - 2 * θ ^ 2) + δ') * bandSq H := by
  classical
  have hden : (0:ℝ) < 1 - 2 * θ ^ 2 := by nlinarith [hθ, sq_nonneg θ]
  set r : ℝ := 2 * θ ^ 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact hθ
  set yof : (Fin K → ℝ → ℂ) → ℝ := fun G =>
    if h : ∃ y : ℝ, |y| ≤ δ ∧ bandMax Ψ lam (transl G y) ≤ ENNReal.ofReal A * bandSq G
      then h.choose else 0 with hyof
  have hyof_spec : ∀ G, Adm G → |yof G| ≤ δ ∧
      bandMax Ψ lam (transl G (yof G)) ≤ ENNReal.ofReal A * bandSq G := by
    intro G hG
    obtain ⟨y, hy, hb⟩ := hgood G hG
    have hex : ∃ y : ℝ, |y| ≤ δ ∧ bandMax Ψ lam (transl G y) ≤ ENNReal.ofReal A * bandSq G :=
      ⟨y, hy, hb⟩
    have hval : yof G = hex.choose := by
      rw [hyof]
      exact dif_pos hex
    rw [hval]
    exact hex.choose_spec
  set F : ℕ → (Fin K → ℝ → ℂ) := fun n =>
    Nat.rec H (fun _ G => fun k u => G k u - G k (u + yof G)) n with hF
  have hF_zero : F 0 = H := rfl
  have hF_succ : ∀ n, F (n+1) = (fun k u => F n k u - F n k (u + yof (F n))) := fun n => rfl
  have hAdm : ∀ n, Adm (F n) := by
    intro n
    induction n with
    | zero => rw [hF_zero]; exact hH
    | succ n ih =>
        rw [hF_succ n]
        exact hpres (F n) ih (yof (F n)) (hyof_spec (F n) ih).1
  have hsq : ∀ n, bandSq (F n) ≤ (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H := by
    intro n
    induction n with
    | zero => rw [hF_zero]; simp
    | succ n ih =>
        rw [hF_succ n]
        calc bandSq (fun k u => F n k u - F n k (u + yof (F n)))
            ≤ ENNReal.ofReal (θ ^ 2) * bandSq (F n) :=
              hcon (F n) (hAdm n) (yof (F n)) (hyof_spec (F n) (hAdm n)).1
          _ ≤ ENNReal.ofReal (θ ^ 2) * ((ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H) :=
              mul_le_mul_right ih _
          _ = (ENNReal.ofReal (θ ^ 2)) ^ (n+1) * bandSq H := by rw [pow_succ']; ring
  have hone : ∀ n, bandMax Ψ lam (F n)
      ≤ 2 * (ENNReal.ofReal A * bandSq (F n)) + 2 * bandMax Ψ lam (F (n+1)) := by
    intro n
    have h1 := hsub (F n) (hAdm n) (yof (F n)) (hyof_spec (F n) (hAdm n)).1
    have h2 := (hyof_spec (F n) (hAdm n)).2
    calc bandMax Ψ lam (F n)
        ≤ 2 * bandMax Ψ lam (transl (F n) (yof (F n)))
            + 2 * bandMax Ψ lam (fun k u => F n k u - F n k (u + yof (F n))) := h1
      _ ≤ 2 * (ENNReal.ofReal A * bandSq (F n)) + 2 * bandMax Ψ lam (F (n+1)) := by
          rw [hF_succ n]
          exact add_le_add (mul_le_mul_right h2 _) le_rfl
  have hiter : ∀ n, bandMax Ψ lam (F 0) ≤
      (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1) * (ENNReal.ofReal A * bandSq (F i)))
        + (2:ENNReal) ^ n * bandMax Ψ lam (F n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc bandMax Ψ lam (F 0)
            ≤ (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1) * (ENNReal.ofReal A * bandSq (F i)))
              + (2:ENNReal) ^ n * bandMax Ψ lam (F n) := ih
          _ ≤ (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1) * (ENNReal.ofReal A * bandSq (F i)))
              + (2:ENNReal) ^ n * (2 * (ENNReal.ofReal A * bandSq (F n))
                + 2 * bandMax Ψ lam (F (n+1))) := by
              refine add_le_add le_rfl (mul_le_mul_right (hone n) _)
          _ = (∑ i ∈ Finset.range (n+1), (2:ENNReal) ^ (i+1) * (ENNReal.ofReal A * bandSq (F i)))
              + (2:ENNReal) ^ (n+1) * bandMax Ψ lam (F (n+1)) := by
              rw [Finset.sum_range_succ, pow_succ']
              ring
  have htail : ∀ n, bandMax Ψ lam (F n)
      ≤ ENNReal.ofReal CK * (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H := by
    intro n
    calc bandMax Ψ lam (F n) ≤ ENNReal.ofReal CK * bandSq (F n) := hap (F n) (hAdm n)
      _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H) := mul_le_mul_right (hsq n) _
      _ = ENNReal.ofReal CK * (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H := by ring
  -- the closed form of the unrolled bound, in `ℝ`
  have hcast : ∀ i : ℕ,
      (2:ENNReal) ^ (i+1) * ENNReal.ofReal A * (ENNReal.ofReal (θ ^ 2)) ^ i
        = ENNReal.ofReal (2 * A * r ^ i) := by
    intro i
    rw [show (2:ENNReal) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ← ENNReal.ofReal_pow (sq_nonneg θ)]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hr, mul_pow, pow_succ]
    ring
  have hcastCK : ∀ n : ℕ,
      (2:ENNReal) ^ n * (ENNReal.ofReal CK * (ENNReal.ofReal (θ ^ 2)) ^ n)
        = ENNReal.ofReal (CK * r ^ n) := by
    intro n
    rw [show (2:ENNReal) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ← ENNReal.ofReal_pow (sq_nonneg θ)]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hr, mul_pow]
    ring
  have hbound : ∀ n, bandMax Ψ lam H ≤ ENNReal.ofReal
      (2 * A * (∑ i ∈ Finset.range n, r ^ i) + CK * r ^ n) * bandSq H := by
    intro n
    have h1 := hiter n
    rw [hF_zero] at h1
    have h2 : (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1)
          * (ENNReal.ofReal A * bandSq (F i)))
        ≤ (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1)
          * (ENNReal.ofReal A * ((ENNReal.ofReal (θ ^ 2)) ^ i * bandSq H))) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_right (mul_le_mul_right (hsq i) _) _
    have h3 : (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1)
          * (ENNReal.ofReal A * ((ENNReal.ofReal (θ ^ 2)) ^ i * bandSq H)))
        = ENNReal.ofReal (2 * A * (∑ i ∈ Finset.range n, r ^ i)) * bandSq H := by
      have hterm : ∀ i ∈ Finset.range n, (2:ENNReal) ^ (i+1)
            * (ENNReal.ofReal A * ((ENNReal.ofReal (θ ^ 2)) ^ i * bandSq H))
          = ENNReal.ofReal (2 * A * r ^ i) * bandSq H := by
        intro i _
        rw [← hcast i]
        ring
      calc (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1)
            * (ENNReal.ofReal A * ((ENNReal.ofReal (θ ^ 2)) ^ i * bandSq H)))
          = ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * A * r ^ i) * bandSq H :=
            Finset.sum_congr rfl hterm
        _ = (∑ i ∈ Finset.range n, ENNReal.ofReal (2 * A * r ^ i)) * bandSq H := by
            rw [Finset.sum_mul]
        _ = ENNReal.ofReal (∑ i ∈ Finset.range n, 2 * A * r ^ i) * bandSq H := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        _ = ENNReal.ofReal (2 * A * (∑ i ∈ Finset.range n, r ^ i)) * bandSq H := by
            have hone : (∑ i ∈ Finset.range n, 2 * A * r ^ i)
                = 2 * A * ∑ i ∈ Finset.range n, r ^ i := by
              rw [Finset.mul_sum]
            rw [hone]
    calc bandMax Ψ lam H
        ≤ (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1) * (ENNReal.ofReal A * bandSq (F i)))
            + (2:ENNReal) ^ n * bandMax Ψ lam (F n) := h1
      _ ≤ (∑ i ∈ Finset.range n, (2:ENNReal) ^ (i+1)
            * (ENNReal.ofReal A * ((ENNReal.ofReal (θ ^ 2)) ^ i * bandSq H)))
            + (2:ENNReal) ^ n * (ENNReal.ofReal CK * (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H) := by
          refine add_le_add h2 (mul_le_mul_right (htail n) _)
      _ = ENNReal.ofReal (2 * A * (∑ i ∈ Finset.range n, r ^ i)) * bandSq H
            + ENNReal.ofReal (CK * r ^ n) * bandSq H := by
          rw [h3]
          have hassoc : (2:ENNReal) ^ n
              * (ENNReal.ofReal CK * (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H)
              = ((2:ENNReal) ^ n * (ENNReal.ofReal CK * (ENNReal.ofReal (θ ^ 2)) ^ n))
                * bandSq H := by ring
          rw [hassoc, hcastCK n]
      _ = ENNReal.ofReal (2 * A * (∑ i ∈ Finset.range n, r ^ i) + CK * r ^ n) * bandSq H := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- choose `n` with the coefficient at most `2A/(1-r) + δ'`
  have hgeom : ∀ n : ℕ, (∑ i ∈ Finset.range n, r ^ i) ≤ (1 - r)⁻¹ := by
    intro n
    have hlt1 : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
    have hsummable : Summable (fun i : ℕ => r ^ i) := summable_geometric_of_norm_lt_one hlt1
    have hsum : (∑' i : ℕ, r ^ i) = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one hlt1
    rw [← hsum]
    exact hsummable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg hr0 i)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * r ^ n ≤ δ' := by
    have htend : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hpos : (0:ℝ) < δ' / (CK + 1) := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend _ hpos)
    have hdist := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at hdist
    have hlt : r ^ N < δ' / (CK + 1) := by
      rwa [abs_of_nonneg (pow_nonneg hr0 N)] at hdist
    refine ⟨N, ?_⟩
    calc CK * r ^ N ≤ (CK + 1) * (δ' / (CK + 1)) := by
          refine mul_le_mul (by linarith) hlt.le (pow_nonneg hr0 N) (by linarith)
      _ = δ' := by field_simp
  calc bandMax Ψ lam H
      ≤ ENNReal.ofReal (2 * A * (∑ i ∈ Finset.range n, r ^ i) + CK * r ^ n) * bandSq H := hbound n
    _ ≤ ENNReal.ofReal (2 * A / (1 - 2 * θ ^ 2) + δ') * bandSq H := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        have hg := hgeom n
        rw [hr] at hg
        have h2 : 2 * A * (∑ i ∈ Finset.range n, r ^ i) ≤ 2 * A * (1 - r)⁻¹ :=
          mul_le_mul_of_nonneg_left hg (by linarith)
        calc 2 * A * (∑ i ∈ Finset.range n, r ^ i) + CK * r ^ n
            ≤ 2 * A * (1 - r)⁻¹ + δ' := add_le_add h2 hn
          _ = 2 * A / (1 - 2 * θ ^ 2) + δ' := by rw [hr]; ring

/-! ### §6 item 1: the two entropy numbers agree

`FWDeep.winEntE Ψ f x r` (curve in the ℓ²-space `EuclideanSpace ℂ (Fin K)`, covers with
`dist a s ≤ r`) and `OldSWM.BourgainMax.winEntropy K (⇑Ψ) f x r` (curve in `Fin K → ℂ`, covers with
`∑ k, ‖a k - s k‖² ≤ r²`) are the *same* number.  This is the interface gap of §1 of the STATUS. -/

section EntropyBridge

variable {K : ℕ}

/-- The `ℓ²`-metric of `EuclideanSpace ℂ (Fin K)` on `WithLp.toLp`-points is the `ℓ²`-sum. -/
lemma dist_toLp_sq (a s : Fin K → ℂ) :
    dist (WithLp.toLp 2 a) (WithLp.toLp 2 s : EuclideanSpace ℂ (Fin K)) ^ 2
      = ∑ k : Fin K, ‖a k - s k‖ ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, dist_eq_norm]

/-- Transport of the ball comparison. -/
lemma dist_toLp_le_iff {r : ℝ} (hr : 0 ≤ r) (a s : Fin K → ℂ) :
    dist (WithLp.toLp 2 a) (WithLp.toLp 2 s : EuclideanSpace ℂ (Fin K)) ≤ r
      ↔ ∑ k : Fin K, ‖a k - s k‖ ^ 2 ≤ r ^ 2 := by
  rw [← dist_toLp_sq a s]
  exact (pow_le_pow_iff_left₀ dist_nonneg hr (by norm_num : (2:ℕ) ≠ 0)).symm

/-- The two curves: `FWDeep.curveSetE` is the `WithLp.toLp`-image of `winCurve`. -/
lemma curveSetE_eq_image (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    FWDeep.curveSetE Ψ f x
      = (fun z : Fin K → ℂ => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin K)))
          '' winCurve K (⇑Ψ) f x := by
  have h1 : FWDeep.curveSetE Ψ f x = Set.range
      ((fun z : Fin K → ℂ => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin K)))
        ∘ (fun t : {t : ℝ // 0 < t} => fun k : Fin K => winOp Ψ (f k) x (t : ℝ))) := rfl
  have h2 : winCurve K (⇑Ψ) f x = Set.range
      (fun t : {t : ℝ // 0 < t} => fun k : Fin K => winOp Ψ (f k) x (t : ℝ)) := rfl
  rw [h1, h2, Set.range_comp]

/-- The `ℓ²`-covering predicate. -/
lemma winCoveredE_iff (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    FWDeep.winCoveredE Ψ f x r ↔ winCovered K (⇑Ψ) f x r := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.ofLp, fun a ha => ?_⟩
    have h1 : (WithLp.toLp 2 a : EuclideanSpace ℂ (Fin K)) ∈ FWDeep.curveSetE Ψ f x := by
      rw [curveSetE_eq_image]; exact ⟨a, ha, rfl⟩
    have h2 := hs _ h1
    rw [← WithLp.toLp_ofLp (p := 2) s] at h2
    exact (dist_toLp_le_iff hr.le a s.ofLp).mp h2
  · rintro ⟨s, hs⟩
    refine ⟨WithLp.toLp 2 s, fun a ha => ?_⟩
    rw [curveSetE_eq_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact (dist_toLp_le_iff hr.le b s).mpr (hs b hb)

/-- The `ℓ²`-covering-set predicate, transported to `Fin K → ℂ`. -/
lemma winCoversE_iff_image (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {r : ℝ}
    (hr : 0 < r) (S : Finset (EuclideanSpace ℂ (Fin K))) :
    FWDeep.winCoversE Ψ f x r S ↔ winCovers K (⇑Ψ) f x r (S.image WithLp.ofLp) := by
  constructor
  · intro hS a ha
    obtain ⟨s, hsS, hs⟩ := hS _ (by rw [curveSetE_eq_image]; exact ⟨a, ha, rfl⟩)
    refine ⟨s.ofLp, Finset.mem_image.mpr ⟨s, hsS, rfl⟩, ?_⟩
    rw [← WithLp.toLp_ofLp (p := 2) s] at hs
    exact (dist_toLp_le_iff hr.le a s.ofLp).mp hs
  · intro hS a ha
    rw [curveSetE_eq_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨s, hsS, hs⟩ := hS b hb
    rw [Finset.mem_image] at hsS
    obtain ⟨s', hs'S, rfl⟩ := hsS
    exact ⟨s', hs'S, (dist_toLp_le_iff hr.le b s').mpr hs⟩

/-- The `ℓ²`-covering-set predicate, transported from `Fin K → ℂ`. -/
lemma winCovers_iff_image_toLp (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {r : ℝ}
    (hr : 0 < r) (T : Finset (Fin K → ℂ)) :
    winCovers K (⇑Ψ) f x r T
      ↔ FWDeep.winCoversE Ψ f x r
          (T.image (fun z => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin K)))) := by
  constructor
  · intro hT a ha
    rw [curveSetE_eq_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨s, hsT, hs⟩ := hT b hb
    exact ⟨WithLp.toLp 2 s, Finset.mem_image.mpr ⟨s, hsT, rfl⟩, (dist_toLp_le_iff hr.le b s).mpr hs⟩
  · intro hT a ha
    obtain ⟨s, hsS, hs⟩ := hT _ (by rw [curveSetE_eq_image]; exact ⟨a, ha, rfl⟩)
    rw [Finset.mem_image] at hsS
    obtain ⟨s', hs'T, rfl⟩ := hsS
    exact ⟨s', hs'T, (dist_toLp_le_iff hr.le a s').mp hs⟩

/-- **§6 item 1: the two entropy numbers agree.** -/
theorem winEntE_eq_winEntropy (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {r : ℝ}
    (hr : 0 < r) :
    FWDeep.winEntE Ψ f x r = winEntropy K (⇑Ψ) f x r := by
  classical
  have hcov : FWDeep.winCoveredE Ψ f x r ↔ winCovered K (⇑Ψ) f x r := winCoveredE_iff Ψ f x hr
  rw [show FWDeep.winEntE Ψ f x r = (if FWDeep.winCoveredE Ψ f x r then 0
      else ⨅ (S : {S : Finset (EuclideanSpace ℂ (Fin K)) // FWDeep.winCoversE Ψ f x r S}),
        ((S : Finset (EuclideanSpace ℂ (Fin K))).card : ℝ≥0∞)) from rfl,
    show winEntropy K (⇑Ψ) f x r = (if winCovered K (⇑Ψ) f x r then 0
      else ⨅ (T : {T : Finset (Fin K → ℂ) // winCovers K (⇑Ψ) f x r T}),
        ((T : Finset (Fin K → ℂ)).card : ℝ≥0∞)) from rfl]
  by_cases hc : FWDeep.winCoveredE Ψ f x r
  · rw [if_pos hc, if_pos (hcov.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hcov.mpr h))]
    refine le_antisymm ?_ ?_
    · refine le_iInf (fun T => ?_)
      have hS : FWDeep.winCoversE Ψ f x r
          (T.1.image (fun z => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin K)))) :=
        (winCovers_iff_image_toLp Ψ f x hr T.1).mp T.2
      calc (⨅ (S : {S : Finset (EuclideanSpace ℂ (Fin K)) // FWDeep.winCoversE Ψ f x r S}),
              ((S : Finset (EuclideanSpace ℂ (Fin K))).card : ℝ≥0∞))
          ≤ (((T.1.image (fun z => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin K)))) :
                Finset (EuclideanSpace ℂ (Fin K))).card : ℝ≥0∞) :=
            iInf_le _ (⟨T.1.image (fun z => (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin K))), hS⟩ :
              {S : Finset (EuclideanSpace ℂ (Fin K)) // FWDeep.winCoversE Ψ f x r S})
        _ ≤ (T.1.card : ℝ≥0∞) := by exact_mod_cast Finset.card_image_le
    · refine le_iInf (fun S => ?_)
      have hT : winCovers K (⇑Ψ) f x r (S.1.image WithLp.ofLp) :=
        (winCoversE_iff_image Ψ f x hr S.1).mp S.2
      calc (⨅ (T : {T : Finset (Fin K → ℂ) // winCovers K (⇑Ψ) f x r T}),
              ((T : Finset (Fin K → ℂ)).card : ℝ≥0∞))
          ≤ ((S.1.image WithLp.ofLp : Finset (Fin K → ℂ)).card : ℝ≥0∞) :=
            iInf_le _ (⟨S.1.image WithLp.ofLp, hT⟩ :
              {T : Finset (Fin K → ℂ) // winCovers K (⇑Ψ) f x r T})
        _ ≤ (S.1.card : ℝ≥0∞) := by exact_mod_cast Finset.card_image_le

/-- **The `ℓ²`-metric entropy input in the `OldSWM` covering-number form** (`winEntropy`): the
immediate corollary of §6 item 1 and `FWDeep.l2_entropy_input_dyadic`. -/
theorem l2_entropy_input_winEntropy (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K)) ((winEntropy K (⇑Ψ) f x r) ^ ((1:ℝ)/2))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
  obtain ⟨C, hC, h⟩ := FWDeep.l2_entropy_input_dyadic Ψ
  refine ⟨C, hC, fun K f hf2 hfinf => ?_⟩
  refine le_trans (le_of_eq ?_) (h K f hf2 hfinf)
  refine lintegral_congr (fun x => ?_)
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  rw [winEntE_eq_winEntropy Ψ f x hr]

/-! ### §6 item 2: the chain bound at a fixed point `z`

`D = 2c`; the covers at the dyadic radii `2c·2^{-t}` come from `exists_phased_covers` (the caller),
the nets from `BourgainEntropy.exists_netmap_of_cover`; the chain bound applied is
`FWS.chain_exp_sum_le_entropy_scaled`.  The output is the per-`z` (truncated) chain statement
consumed by the `(y,z)` Tonnelli step (item 3). -/

/-- **§6 item 2 (the chain bound at a fixed `z`).** -/
theorem chain_bound_at_z (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 3 * ESU.cChain ∧ ∀ (H : Fin K → ℝ → ℂ) (S : ℕ) (z c : ℝ) (M : ℕ → ℕ),
      0 < c → 1 ≤ S → 1 ≤ M 0 → (S+1) ≤ M S →
      (∀ i : Fin (S+1), ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k‖ ^ 2 ≤ c ^ 2) →
      (∀ t, 1 ≤ t → t ≤ S → ∃ Sc : Finset (Fin K → ℂ),
          (∀ i : Fin (S+1), ∃ s ∈ Sc,
            ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - s k‖ ^ 2 ≤ (2 * c * (1/2:ℝ)^t)^2) ∧
          Sc.card ≤ M t) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H i z k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((C * c * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  obtain ⟨C₀, hC₀pos, hC₀le, hC₀⟩ := chain_exp_sum_le_entropy_scaled K lam hsep
  have hC₀le' : 3 * C₀ ≤ 3 * ESU.cChain := by
    have := ESU.cChain_pos
    linarith
  refine ⟨3 * C₀, by positivity, hC₀le', ?_⟩
  intro H S z c M hc hS hM0 hMS hball hcov
  have h0 : 0 < S + 1 := Nat.succ_pos S
  -- the difference of any curve point from the base point `0`
  have hdiff : ∀ i : Fin (S+1),
      ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2 ≤ (2 * c) ^ 2 := by
    intro i
    have hsplit : ∀ k : Fin K, ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2
        ≤ 2 * ‖curvePtJ Ψ lam H i z k‖ ^ 2 + 2 * ‖curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2 := by
      intro k
      have hb : ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (0:ℕ) z k‖
          ≤ ‖curvePtJ Ψ lam H i z k‖ + ‖curvePtJ Ψ lam H (0:ℕ) z k‖ := norm_sub_le _ _
      have h1 : (0:ℝ) ≤ ‖curvePtJ Ψ lam H i z k‖ := norm_nonneg _
      have h2 : (0:ℝ) ≤ ‖curvePtJ Ψ lam H (0:ℕ) z k‖ := norm_nonneg _
      have h3 : (‖curvePtJ Ψ lam H i z k‖ + ‖curvePtJ Ψ lam H (0:ℕ) z k‖) ^ 2
          ≤ 2 * ‖curvePtJ Ψ lam H i z k‖ ^ 2 + 2 * ‖curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2 := by
        nlinarith [sq_nonneg (‖curvePtJ Ψ lam H i z k‖ - ‖curvePtJ Ψ lam H (0:ℕ) z k‖),
          sq_nonneg (‖curvePtJ Ψ lam H i z k‖ + ‖curvePtJ Ψ lam H (0:ℕ) z k‖)]
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hb 2) h3
    calc ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2
        ≤ ∑ k : Fin K, (2 * ‖curvePtJ Ψ lam H i z k‖ ^ 2
            + 2 * ‖curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2) := Finset.sum_le_sum (fun k _ => hsplit k)
      _ = 2 * ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k‖ ^ 2
            + 2 * ∑ k : Fin K, ‖curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ (2 * c) ^ 2 := by
          have h1 := hball i
          have h2 := hball (⟨0, h0⟩ : Fin (S+1))
          have h3 : (2:ℝ) * (∑ k : Fin K, ‖curvePtJ Ψ lam H i z k‖ ^ 2)
              ≤ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (by norm_num)
          have h4 : (2:ℝ) * (∑ k : Fin K, ‖curvePtJ Ψ lam H (0:ℕ) z k‖ ^ 2)
              ≤ 2 * c ^ 2 := by
            have h5 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 2)
            simpa using h5
          nlinarith [h3, h4]
  -- a net map at each level `1 ≤ t ≤ S` from the given covers
  have hnet_exists : ∀ t : ℕ, 1 ≤ t → t ≤ S → ∃ τ : Fin (S+1) → Fin (S+1),
      (Finset.univ.image τ).card ≤ M t ∧ ∀ i : Fin (S+1),
        ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (τ i) z k‖ ^ 2
          ≤ (4 * c * (1/2:ℝ)^t)^2 := by
    intro t ht1 htS
    obtain ⟨Sc, hcover, hcard⟩ := hcov t ht1 htS
    have hr : (0:ℝ) < 4 * c * (1/2:ℝ)^t := by positivity
    obtain ⟨τ, hτcard, hτnet⟩ := BourgainEntropy.exists_netmap_of_cover
      (fun i : Fin (S+1) => curvePtJ Ψ lam H i z) Sc (r := 4 * c * (1/2:ℝ)^t) hr
      (fun i => by
        obtain ⟨s, hs, hb⟩ := hcover i
        exact ⟨s, hs, by
          rw [show 4 * c * (1/2:ℝ)^t / 2 = 2 * c * (1/2:ℝ)^t by ring]
          exact hb⟩)
    exact ⟨τ, le_trans hτcard hcard, hτnet⟩
  -- the nets, chosen once and for all at each level
  choose σt hσtcard hσtnet using hnet_exists
  set σ : ℕ → Fin (S+1) → Fin (S+1) := fun t =>
    if h : 1 ≤ t ∧ t ≤ S then σt t h.1 h.2 else fun _ => (⟨0, h0⟩ : Fin (S+1)) with hσ
  have hσ0 : ∀ i : Fin (S+1), σ 0 i = σ 0 0 := by
    intro i
    have hval : σ 0 = fun _ => (⟨0, h0⟩ : Fin (S+1)) := by
      rw [hσ]; exact dif_neg (by omega : ¬ (1 ≤ (0:ℕ) ∧ (0:ℕ) ≤ S))
    rw [hval]
  have hσcard : ∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t := by
    intro t htS
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      have hcard1 : (Finset.univ.image (fun _ : Fin (S+1) => (⟨0, h0⟩ : Fin (S+1)))).card ≤ 1 := by
        refine Finset.card_le_one.mpr (fun x hx y hy => ?_)
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
        rfl
      have hval : σ 0 = fun _ => (⟨0, h0⟩ : Fin (S+1)) := by
        rw [hσ]; exact dif_neg (by omega : ¬ (1 ≤ (0:ℕ) ∧ (0:ℕ) ≤ S))
      rw [hval]
      omega
    · have h1 : 1 ≤ t ∧ t ≤ S := ⟨htpos, htS⟩
      have hval : σ t = σt t h1.1 h1.2 := by rw [hσ]; exact dif_pos h1
      rw [hval]
      exact hσtcard t h1.1 h1.2
  have hσnet : ∀ t, t ≤ S → ∀ i : Fin (S+1),
      ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (σ t i) z k‖ ^ 2
        ≤ (2 * (2 * c) * (1/2:ℝ)^t)^2 := by
    intro t htS i
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      have hval : σ 0 = fun _ => (⟨0, h0⟩ : Fin (S+1)) := by
        rw [hσ]; exact dif_neg (by omega : ¬ (1 ≤ (0:ℕ) ∧ (0:ℕ) ≤ S))
      rw [hval]
      refine le_trans (hdiff i) ?_
      have : (2 * c) ^ 2 ≤ (2 * (2 * c) * (1/2:ℝ)^(0:ℕ)) ^ 2 := by
        rw [pow_zero, mul_one]; nlinarith
      exact this
    · have h1 : 1 ≤ t ∧ t ≤ S := ⟨htpos, htS⟩
      have hval : σ t = σt t h1.1 h1.2 := by rw [hσ]; exact dif_pos h1
      rw [hval]
      have hτ := hσtnet t h1.1 h1.2 i
      rwa [show 4 * c * (1/2:ℝ)^t = 2 * (2 * c) * (1/2:ℝ)^t by ring] at hτ
  have hbase : ((σ 0 0 : Fin (S+1)) : ℕ) = 0 := by
    have hval : σ 0 = fun _ => (⟨0, h0⟩ : Fin (S+1)) := by
      rw [hσ]; exact dif_neg (by omega : ¬ (1 ≤ (0:ℕ) ∧ (0:ℕ) ≤ S))
    rw [hval]
  have hball' : ∀ i : Fin (S+1),
      ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - curvePtJ Ψ lam H (σ 0 0) z k‖ ^ 2
        ≤ (2 * c) ^ 2 := by
    intro i
    rw [hbase]
    exact hdiff i
  have hmain := hC₀ S S (fun i : Fin (S+1) => curvePtJ Ψ lam H i z) σ M (D := 2 * c)
    (by positivity) hS hσ0 hMS hball' hσcard hσnet
  have hroot : Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H (σ 0 0) z k‖ ^ 2) ≤ c := by
    rw [hbase, Real.sqrt_le_iff]
    exact ⟨hc.le, hball (⟨0, h0⟩ : Fin (S+1))⟩
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hBnn : 0 ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)) :=
    Finset.sum_nonneg (fun t _ => by positivity)
  have hle : Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H (σ 0 0) z k‖ ^ 2)
      + 2 * c * (∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ 3 * c * (1 + ∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) := by
    nlinarith [hroot, hBnn, hc]
  calc (C₀ * (Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H (σ 0 0) z k‖ ^ 2)
        + 2 * c * ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2
      = C₀ ^ 2 * (Real.sqrt (∑ k : Fin K, ‖curvePtJ Ψ lam H (σ 0 0) z k‖ ^ 2)
        + 2 * c * ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) ^ 2 := by ring
    _ ≤ C₀ ^ 2 * (3 * c * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C₀)
        exact pow_le_pow_left₀ (by positivity) hle 2
    _ = ((3 * C₀) * c * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2 := by ring

/-! ### §6 item 4: `curveRad` and the `L²` bound on the curve's size

`curveRadSq Ψ lam H S z` is the squared `ℓ²`-norm of the curve point `curvePtJ Ψ lam H i z`,
maximized over the truncated scale family `i ≤ S`; `curveRad` is its square root.  Item 4 is the
estimate `∫_z ofReal (curveRadSq z) ≤ C · bandSq H`, which bounds `∫ c²` (the only place where the
normalization constant `c` grows). -/

/-- The squared `ℓ²`-norm of the largest curve point at scale `≤ S`. -/
noncomputable def curveRadSq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (S+1))).sup' Finset.univ_nonempty
    (fun i => ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2)

/-- The `ℓ²`-size of the curve at scale `≤ S` (the normalizing constant of §6 item 2). -/
noncomputable def curveRad (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) : ℝ :=
  Real.sqrt (curveRadSq Ψ lam H S z)

lemma curveRadSq_nonneg (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) : 0 ≤ curveRadSq Ψ lam H S z :=
  le_trans (Finset.sum_nonneg (fun k _ => sq_nonneg _))
    (Finset.le_sup' (fun i : Fin (S+1) => ∑ k : Fin K,
        ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2) (Finset.mem_univ (⟨0, Nat.succ_pos S⟩)))

lemma curveRad_nonneg (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) : 0 ≤ curveRad Ψ lam H S z :=
  Real.sqrt_nonneg _

/-- Every curve point at scale `≤ S` lies in the `curveRad`-ball. -/
lemma curvePtJ_sum_sq_le_curveRadSq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) (i : Fin (S+1)) :
    ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2 ≤ curveRadSq Ψ lam H S z :=
  Finset.le_sup' (fun i : Fin (S+1) => ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2)
    (Finset.mem_univ i)

lemma curvePtJ_sum_sq_le_curveRad_sq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) (i : Fin (S+1)) :
    ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2 ≤ curveRad Ψ lam H S z ^ 2 := by
  rw [curveRad, Real.sq_sqrt (curveRadSq_nonneg Ψ lam H S z)]
  exact curvePtJ_sum_sq_le_curveRadSq Ψ lam H S z i

/-! ### Fine points A and B of §6 item 4 -/

/-- **Fine point A.**  A bounded-above supremum of reals commutes with `ENNReal.ofReal`.  (No
Mathlib lemma exists for this: `ofReal` is a complete-lattice embedding, but the real `⨆` is a
conditionally complete supremum, so boundedness above must be assumed and the `≤` direction goes
through `exists_lt_of_lt_ciSup`.) -/
lemma ofReal_iSup_eq_iSup_ofReal {ι : Type*} [Nonempty ι] {f : ι → ℝ}
    (hb : BddAbove (Set.range f)) :
    ENNReal.ofReal (⨆ i, f i) = ⨆ i, ENNReal.ofReal (f i) := by
  refine le_antisymm ?_ ?_
  · refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    have hεpos : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup (f := f) (b := (⨆ i, f i) - (ε:ℝ))
      (by linarith : (⨆ i, f i) - (ε:ℝ) < ⨆ i, f i)
    calc ENNReal.ofReal (⨆ i, f i) ≤ ENNReal.ofReal (f i + (ε:ℝ)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (f i) + ENNReal.ofReal ((ε:ℝ)) := ENNReal.ofReal_add_le
      _ ≤ (⨆ i, ENNReal.ofReal (f i)) + (ε : ℝ≥0∞) := by
          refine add_le_add (le_iSup (fun i => ENNReal.ofReal (f i)) i) ?_
          exact le_of_eq (ENNReal.ofReal_coe_nnreal (p := ε))
  · exact iSup_le (fun i => ENNReal.ofReal_le_ofReal (le_ciSup hb i))

/-- **Fine point B.**  The `ofReal`/`rpow` bookkeeping converting a squared norm into the
`ℝ≥0∞`-valued `enorm` to the power `2`. -/
lemma ofReal_norm_sq_eq_enorm_rpow_two (z : ℂ) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2:ℝ) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, enorm_eq_ofReal_norm',
    ← ENNReal.ofReal_pow (norm_nonneg z) 2]

/-- A **finite** supremum commutes with `ENNReal.ofReal` (here the supremum is attained, so no
boundedness hypothesis is needed, unlike fine point A). -/
lemma ofReal_sup'_eq_sup'_ofReal {ι : Type*} {s : Finset ι} (h : s.Nonempty) (f : ι → ℝ) :
    ENNReal.ofReal (s.sup' h f) = s.sup' h (fun i => ENNReal.ofReal (f i)) := by
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' h f
  refine le_antisymm ?_ ?_
  · rw [hsup]
    exact Finset.le_sup' (fun i => ENNReal.ofReal (f i)) hi
  · refine Finset.sup'_le h _ (fun j hj => ?_)
    exact ENNReal.ofReal_le_ofReal (Finset.le_sup' f hj)

/-- **§6 item 4, step 1.**  The squared curve size is dominated by the sum over the coordinates of
the dyadic maximal functions of the windowed dilations (the phases of `curvePtJ` drop out). -/
lemma ofReal_curveRadSq_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    ENNReal.ofReal (curveRadSq Ψ lam H S z)
      ≤ ∑ k : Fin K, ⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ) := by
  rw [curveRadSq, ofReal_sup'_eq_sup'_ofReal (Finset.univ_nonempty (α := Fin (S+1)))]
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  calc ENNReal.ofReal (∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2)
      = ∑ k : Fin K, ENNReal.ofReal (‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2) :=
        ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
    _ ≤ ∑ k : Fin K, ⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hph : ‖curvePtJ Ψ lam H (i : ℕ) z k‖
            = ‖∫ v : ℝ, H k v * winK Ψ (i : ℕ) (z - v)‖ := by
          show ‖Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ)))
              * (∫ v : ℝ, H k v * winK Ψ (i : ℕ) (z - v))‖ = _
          have hexp : ‖Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ)))‖ = 1 := by
            rw [show -(Complex.I * (lam k : ℂ) * (z : ℂ))
                = (((-(lam k * z)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          rw [norm_mul, hexp, one_mul]
        rw [ofReal_norm_sq_eq_enorm_rpow_two,
          show ‖curvePtJ Ψ lam H (i : ℕ) z k‖ₑ
            = ‖∫ v : ℝ, H k v * winK Ψ (i : ℕ) (z - v)‖ₑ from
            (Commons.Analysis.Fourier.enorm_eq_ofReal_norm' _).trans
              ((congrArg ENNReal.ofReal hph).trans
                (Commons.Analysis.Fourier.enorm_eq_ofReal_norm' _).symm)]
        exact le_iSup (fun j : ℕ => ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)) (i : ℕ)

/-- **§6 item 4 (the integral bound).**  `∫_z ofReal (curveRadSq z) ≤ C · bandSq H`, i.e. the
normalizing constant `c = √(curveRadSq)` of §6 item 2 has `L²` square-integral controlled by the
energy — the only place where `c` grows. -/
theorem lintegral_curveRadSq_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hH2 : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (hHm : ∀ k : Fin K, Measurable (H k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℕ,
      ∫⁻ z : ℝ, ENNReal.ofReal (curveRadSq Ψ lam H S z) ≤ ENNReal.ofReal C * bandSq H := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := maximal_dilation_convolution_l2 Ψ
  refine ⟨C₀ + 1, by positivity, fun S => ?_⟩
  -- per-coordinate dyadic maximal bound (the dyadic family is a sub-family of all dilations)
  have hper : ∀ k : Fin K, (∫⁻ z : ℝ,
        (⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)))
      ≤ ENNReal.ofReal C₀ * ∫⁻ z : ℝ, ‖H k z‖ₑ ^ (2:ℝ) := by
    intro k
    refine le_trans (lintegral_mono (fun z => ?_)) (hC₀ (H k) (hH2 k))
    refine iSup_le (fun j => ?_)
    have heq : (∫ v : ℝ, H k v * winK Ψ j (z - v))
        = ∫ v : ℝ, H k v * ((((winScale j)⁻¹)⁻¹) • Ψ ((z - v) / (winScale j)⁻¹)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
      show H k v * winK Ψ j (z - v)
        = H k v * ((((winScale j)⁻¹)⁻¹) • Ψ ((z - v) / (winScale j)⁻¹))
      have hwk : winK Ψ j (z - v) = ((((winScale j)⁻¹)⁻¹) • Ψ ((z - v) / (winScale j)⁻¹)) := by
        rw [← winK_eq_curve Ψ j (z - v)]
      rw [hwk]
    rw [heq]
    exact ENNReal.rpow_le_rpow (le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖∫ v : ℝ, H k v * ((t : ℝ)⁻¹ • Ψ ((z - v) / (t : ℝ)))‖ₑ)
      ⟨(winScale j)⁻¹, inv_winScale_pos j⟩) (by norm_num)
  -- measurability of each coordinate's maximal function
  have hmeas : ∀ k : Fin K, AEMeasurable (fun z : ℝ =>
      ⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)) volume := by
    intro k
    refine AEMeasurable.iSup (fun j => ?_)
    have hcont : Continuous (fun u : ℝ => winK Ψ j u) := by
      unfold winK
      exact continuous_const.mul (Ψ.continuous.comp (continuous_const.mul continuous_id))
    have hconv : Measurable (fun z : ℝ => ∫ v : ℝ, H k v * winK Ψ j (z - v)) :=
      BourgainFatou.measurable_parametric_integral
        (K := fun p : ℝ × ℝ => winK Ψ j (p.1 - p.2))
        (hcont.measurable.comp (measurable_fst.sub measurable_snd))
        (hHm k) (fun z => integrable_mul_winK Ψ (hH1 k) j z)
    exact (hconv.enorm.pow_const 2).aemeasurable
  have hbandSq : (∫⁻ z : ℝ, ∑ k : Fin K, ‖H k z‖ₑ ^ (2:ℝ)) = bandSq H := by
    unfold bandSq
    refine lintegral_congr (fun z => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl
      (fun k _ => (ofReal_norm_sq_eq_enorm_rpow_two (H k z)).symm)
  calc ∫⁻ z : ℝ, ENNReal.ofReal (curveRadSq Ψ lam H S z)
      ≤ ∫⁻ z : ℝ, ∑ k : Fin K, ⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ) :=
        lintegral_mono (fun z => ofReal_curveRadSq_le Ψ lam H S z)
    _ = ∑ k : Fin K, ∫⁻ z : ℝ, (⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)) :=
        lintegral_finsetSum' _ (fun k _ => hmeas k)
    _ ≤ ∑ k : Fin K, ENNReal.ofReal C₀ * ∫⁻ z : ℝ, ‖H k z‖ₑ ^ (2:ℝ) :=
        Finset.sum_le_sum (fun k _ => hper k)
    _ = ENNReal.ofReal C₀ * ∑ k : Fin K, ∫⁻ z : ℝ, ‖H k z‖ₑ ^ (2:ℝ) := by rw [Finset.mul_sum]
    _ = ENNReal.ofReal C₀ * ∫⁻ z : ℝ, ∑ k : Fin K, ‖H k z‖ₑ ^ (2:ℝ) := by
        rw [lintegral_finsetSum' _ (fun k _ =>
          ((hH2 k).aemeasurable.enorm.pow_const 2))]
    _ = ENNReal.ofReal C₀ * bandSq H := by rw [hbandSq]
    _ ≤ ENNReal.ofReal (C₀ + 1) * bandSq H := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

/-- **§6 item 3, step.**  `chain_bound_at_z` with the normalizing constant `c := curveRad Ψ lam H S z`
(the sup of the curve's `ℓ²`-norms, §10).  The hypothesis `0 < c` of `chain_bound_at_z` is
discharged: in the degenerate case `curveRad = 0` every curve point vanishes (each summand of the
`ℓ²`-sum is a square bounded by `0`), so both sides are `0`. -/
theorem chain_bound_at_z_curveRad (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 3 * ESU.cChain ∧ ∀ (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) (M : ℕ → ℕ),
      1 ≤ S → 1 ≤ M 0 → (S+1) ≤ M S →
      (∀ t, 1 ≤ t → t ≤ S → ∃ Sc : Finset (Fin K → ℂ),
          (∀ i : Fin (S+1), ∃ s ∈ Sc,
            ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - s k‖ ^ 2
              ≤ (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)^2) ∧ Sc.card ≤ M t) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H i z k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((C * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  obtain ⟨C, hCpos, hCle, hC⟩ := chain_bound_at_z Ψ lam hsep
  refine ⟨C, hCpos, hCle, fun H S z M hS hM0 hMS hcov => ?_⟩
  rcases eq_or_lt_of_le (curveRad_nonneg Ψ lam H S z) with h0 | hpos
  · -- degenerate: every curve point vanishes, both sides are `0`
    have hz : ∀ i : Fin (S+1), curvePtJ Ψ lam H (i : ℕ) z = 0 := by
      intro i
      funext k
      have h := curvePtJ_sum_sq_le_curveRad_sq Ψ lam H S z i
      rw [h0.symm, pow_two, mul_zero] at h
      have hk : ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2 ≤ 0 :=
        le_trans (Finset.single_le_sum
          (fun l _ => sq_nonneg ‖curvePtJ Ψ lam H (i : ℕ) z l‖) (Finset.mem_univ k)) h
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hk (sq_nonneg _)))
    have hL : (∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2)
        = 0 := by
      have hfun : (fun y : ℝ => ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
            curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2)
          = fun _ => (0 : ℝ≥0∞) := by
        funext y
        have hsum : ∀ i : Fin (S+1), (∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))) = 0 := by
          intro i
          rw [hz i]
          simp
        simp [hsum]
      rw [hfun]
      simp
    rw [hL]
    have hR : ENNReal.ofReal ((C * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) = 0 := by
      rw [h0.symm]
      simp
    rw [hR]
  · exact hC H S z (curveRad Ψ lam H S z) M hpos hS hM0 hMS
      (fun i => curvePtJ_sum_sq_le_curveRad_sq Ψ lam H S z i) hcov

/-! ### §6 item 3, step 1: the `curvePtJ` form of the `u`-averaging identity -/

/-- **Step 1 of the Tonnelli unit.**  The `u`-averaging identity `bandMax_transl_eq`, rewritten with
the phased curve point `curvePtJ` (which is *definitionally* the inner factor
`e^{-Iλ_k x}(H_k ⋆ winK_j)(x)`).  This is the shape in which the chain bound at `z` (item 2) is
applied: the summand is `e^{Iλ_k y} · curvePtJ Ψ lam H j z k`, with the shift `y` only in the
character factor. -/
theorem bandMax_transl_eq_curvePtJ (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (y : ℝ) :
    bandMax Ψ lam (transl H y)
      = ∫⁻ z : ℝ, (⨆ j : ℕ, ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtJ Ψ lam H j z k‖ₑ) ^ (2:ℝ) := by
  rw [bandMax_transl_eq]
  refine lintegral_congr (fun z => ?_)
  refine congrArg (fun t : ℝ≥0∞ => t ^ (2:ℝ)) ?_
  refine iSup_congr (fun j => ?_)
  refine congrArg (fun w : ℂ => ‖w‖ₑ) ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rfl

/-! ### §6 item 3, step 2: measurability side-lemmas and the truncation identity -/

/-- **Measurability of a curve point.**  `(y,z) ↦ curvePtJ Ψ lam H j z k` is measurable on the product
`ℝ × ℝ` (the `y`-dependence is only through the phase, which is continuous in `z`).  Requires both
`Measurable (H k)` (for the parametric integral) and `Integrable (H k)` (its side condition). -/
lemma measurable_curvePtJ (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (j : ℕ) (k : Fin K) :
    Measurable (fun p : ℝ × ℝ => curvePtJ Ψ lam H j p.2 k) := by
  have hcont : Continuous (fun u : ℝ => winK Ψ j u) := by
    unfold winK
    exact continuous_const.mul (Ψ.continuous.comp (continuous_const.mul continuous_id))
  have hconv : Measurable (fun z : ℝ => ∫ v : ℝ, H k v * winK Ψ j (z - v)) :=
    BourgainFatou.measurable_parametric_integral
      (K := fun p : ℝ × ℝ => winK Ψ j (p.1 - p.2))
      (hcont.measurable.comp (measurable_fst.sub measurable_snd))
      (hHm k) (fun z => integrable_mul_winK Ψ (hH1 k) j z)
  have hphase : Measurable (fun p : ℝ × ℝ =>
      Complex.exp (-(Complex.I * (lam k : ℂ) * (p.2 : ℂ)))) := by fun_prop
  have hconv' : Measurable (fun p : ℝ × ℝ => ∫ v : ℝ, H k v * winK Ψ j (p.2 - v)) :=
    hconv.comp measurable_snd
  exact Measurable.mul (f := fun p : ℝ × ℝ => Complex.exp (-(Complex.I * (lam k : ℂ) * (p.2 : ℂ))))
    (g := fun p : ℝ × ℝ => ∫ v : ℝ, H k v * winK Ψ j (p.2 - v)) hphase hconv'

/-- **Measurability of the truncated maximal exponential sum** (the `z`-integrand of the chain
bound, as a function of `(y,z)`). -/
lemma measurable_trunc_sup (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (S : ℕ) :
    Measurable (fun p : ℝ × ℝ => ⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) p.2 k * Complex.exp (Complex.I * (lam k : ℂ) * (p.1 : ℂ))‖) := by
  refine Measurable.iSup (fun i => ?_)
  refine (Finset.measurable_sum Finset.univ (fun k _ => ?_)).norm
  have hphase : Measurable (fun p : ℝ × ℝ =>
      Complex.exp (Complex.I * (lam k : ℂ) * (p.1 : ℂ))) := by fun_prop
  have hcurve : Measurable (fun p : ℝ × ℝ => curvePtJ Ψ lam H (i : ℕ) p.2 k) :=
    measurable_curvePtJ Ψ lam H hHm hH1 (i : ℕ) k
  exact Measurable.mul (f := fun p : ℝ × ℝ => curvePtJ Ψ lam H (i : ℕ) p.2 k)
    (g := fun p : ℝ × ℝ => Complex.exp (Complex.I * (lam k : ℂ) * (p.1 : ℂ))) hcurve hphase

/-- **The truncation identity**: `⨆ j : ℕ` is the increasing union of the finite level sets
`Fin (S+1)`. -/
lemma iSup_nat_eq_iSup_fin {f : ℕ → ℝ≥0∞} :
    (⨆ j : ℕ, f j) = ⨆ S : ℕ, ⨆ i : Fin (S+1), f (i : ℕ) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun j => ?_)
    exact le_trans (le_iSup (fun i : Fin (j+1) => f (i : ℕ)) ⟨j, Nat.lt_succ_self j⟩)
      (le_iSup (fun S : ℕ => ⨆ i : Fin (S+1), f (i : ℕ)) j)
  · refine iSup_le (fun S => ?_)
    exact iSup_le (fun i => le_iSup (fun j : ℕ => f j) (i : ℕ))

/-- **The `ofReal`/square form of the truncated integrand is a.e.-measurable on the product** — the
form consumed by `lintegral_iSup` (step 2) and by `lintegral_lintegral_swap` (step 3), and the form
in which `chain_bound_at_z` is stated. -/
lemma aemeasurable_trunc_enn (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (S : ℕ) :
    AEMeasurable (fun p : ℝ × ℝ => (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) p.2 k * Complex.exp (Complex.I * (lam k : ℂ) * (p.1 : ℂ))‖)) ^ 2)
      ((volume : Measure ℝ).prod volume) :=
  (((measurable_trunc_sup Ψ lam H hHm hH1 S).ennreal_ofReal).pow_const 2).aemeasurable

/-- **The truncated integrand in item 2's shape.**  For a *finite* index the real supremum is
bounded above, so fine point A applies and the `ℝ≥0∞`-rpow form of the truncated maximal
exponential sum coincides with the `ofReal`/square form in which `chain_bound_at_z` is stated. -/
lemma trunc_rpow_eq_ofReal_sq {S : ℕ} (X : Fin (S+1) → ℂ) :
    (⨆ i : Fin (S+1), ‖X i‖ₑ) ^ (2:ℝ)
      = ENNReal.ofReal (⨆ i : Fin (S+1), ‖X i‖) ^ 2 := by
  have hbdd : BddAbove (Set.range (fun i : Fin (S+1) => ‖X i‖)) :=
    ⟨∑ i : Fin (S+1), ‖X i‖, by
      rintro y ⟨i, rfl⟩
      exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)⟩
  have h1 : (⨆ i : Fin (S+1), ‖X i‖ₑ) = ENNReal.ofReal (⨆ i : Fin (S+1), ‖X i‖) := by
    rw [ofReal_iSup_eq_iSup_ofReal hbdd]
    exact iSup_congr (fun i => enorm_eq_ofReal_norm' _)
  rw [h1, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]

/-- The Nat-power form of `trunc_rpow_eq_ofReal_sq` (the exponent form produced by
`ENNReal.iSup_pow`). -/
lemma trunc_pow_eq_ofReal_sq {S : ℕ} (X : Fin (S+1) → ℂ) :
    (⨆ i : Fin (S+1), ‖X i‖ₑ) ^ (2:ℕ) = ENNReal.ofReal (⨆ i : Fin (S+1), ‖X i‖) ^ 2 := by
  simpa only [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast] using
    trunc_rpow_eq_ofReal_sq X

/-- **The pointwise `S → ∞` identity**: the untruncated maximal exponential sum is the supremum of
its finite-scale truncations, in the `ofReal`/square shape of item 2. -/
lemma iSup_eq_iSup_trunc (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (y z : ℝ) :
    (⨆ j : ℕ, ‖∑ k : Fin K, curvePtJ Ψ lam H j z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ (2:ℝ)
      = ⨆ S : ℕ, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, iSup_nat_eq_iSup_fin,
    ENNReal.iSup_pow]
  exact iSup_congr (fun S => trunc_pow_eq_ofReal_sq
    (fun i : Fin (S+1) => ∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
      * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))))

/-- **Monotonicity of the truncation in `S`** (real-supremum form): a larger level set gives a
larger maximal exponential sum. -/
lemma trunc_sup_mono (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (y z : ℝ) {S S' : ℕ} (h : S ≤ S') :
    (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)
      ≤ ⨆ i : Fin (S'+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ := by
  have hbdd : BddAbove (Set.range (fun i : Fin (S'+1) => ‖∑ k : Fin K,
      curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) :=
    ⟨∑ j : Fin (S'+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (j : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖, by
      rintro v ⟨j, rfl⟩
      exact Finset.single_le_sum (f := fun j : Fin (S'+1) => ‖∑ k : Fin K, curvePtJ Ψ lam H (j : ℕ) z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)
        (fun l _ => norm_nonneg _) (Finset.mem_univ j)⟩
  refine Real.iSup_le (fun i => ?_) (le_trans (norm_nonneg _) (le_ciSup hbdd ⟨0, Nat.succ_pos S'⟩))
  refine le_ciSup hbdd ⟨(i : ℕ), Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ h)⟩

/-- The same monotonicity after `ofReal` and squaring — the shape in which the `z`-push needs it. -/
lemma trunc_ofReal_sq_mono (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (y z : ℝ) {S S' : ℕ} (h : S ≤ S') :
    (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2
      ≤ (ENNReal.ofReal (⨆ i : Fin (S'+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 :=
  pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal (trunc_sup_mono Ψ lam H y z h)) 2

/-- **Monotonicity of the truncation in `S`, `ℝ≥0∞`-sup form.**  Cheaper than
`trunc_ofReal_sq_mono`: the `ℝ≥0∞`-supremum needs no `BddAbove` and no unfolding, so it is the
`Monotone` hypothesis to use when pushing `lintegral_iSup` in the `ℝ≥0∞` form. -/
lemma trunc_enn_mono (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (y z : ℝ) {S S' : ℕ} (h : S ≤ S') :
    (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ (2:ℕ)
      ≤ (⨆ i : Fin (S'+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ 2 := by
  refine pow_le_pow_left₀ bot_le (iSup_le (fun i => ?_)) 2
  exact le_iSup (fun i : Fin (S'+1) => ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
      * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ)
    ⟨(i : ℕ), Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ h)⟩

/-- **The `AEMeasurable` side condition of the `ℝ≥0∞`-form `z`-push.**  Measurability in `z` of a
level of the truncation, stated with the `ℝ≥0∞`-supremum (no `ofReal`, no real sup, no unfolding):
each term is `Measurable.enorm` of a `Finset.measurable_sum` of products, the finite `iSup` is
`Measurable.iSup`. -/
lemma measurable_trunc_enn_sup (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (S : ℕ) (y : ℝ) :
    Measurable (fun z : ℝ => (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ 2) := by
  refine Measurable.pow_const ?_ 2
  refine Measurable.iSup (fun i => ?_)
  refine Measurable.enorm ?_
  refine Finset.measurable_sum _ (fun k _ => ?_)
  have hslice : Measurable (fun z : ℝ => (y, z)) := by fun_prop
  have hcurve : Measurable (fun z : ℝ => curvePtJ Ψ lam H (i : ℕ) z k) :=
    (measurable_curvePtJ Ψ lam H hHm hH1 (i : ℕ) k).comp hslice
  exact Measurable.mul (f := fun z : ℝ => curvePtJ Ψ lam H (i : ℕ) z k)
    (g := fun _ : ℝ => Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) hcurve measurable_const

lemma aemeasurable_trunc_enn_sup (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (S : ℕ) (y : ℝ) :
    AEMeasurable (fun z : ℝ => (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ 2) volume :=
  (measurable_trunc_enn_sup Ψ lam H hHm hH1 S y).aemeasurable

/-- **The `z`-push in the `ℝ≥0∞`-sup form.**  For fixed `y`, the `z`-integral of the supremum over
the truncations is the supremum of the level-wise `z`-integrals — `lintegral_iSup` with both
hypotheses in matching shape (`aemeasurable_trunc_enn_sup`, `trunc_enn_mono`). -/
lemma lintegral_iSup_trunc_enn (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (y : ℝ) :
    (∫⁻ z : ℝ, ⨆ S : ℕ, (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ (2:ℕ))
      = ⨆ S : ℕ, ∫⁻ z : ℝ, (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ 2 := by
  refine lintegral_iSup (fun S => measurable_trunc_enn_sup Ψ lam H hHm hH1 S y)
    (fun S S' h => fun z => trunc_enn_mono Ψ lam H y z h)

/-- **The `z`-push in item 2's `ofReal`/square shape.**  Obtained from the `ℝ≥0∞`-form
`lintegral_iSup_trunc_enn` by rewriting each level with the *proved equality*
`trunc_pow_eq_ofReal_sq` — no unfolding, so this is cheap. -/
lemma lintegral_iSup_trunc_z (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (y : ℝ) :
    (∫⁻ z : ℝ, ⨆ S : ℕ, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      = ⨆ S : ℕ, ∫⁻ z : ℝ, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
  have hcongr : (fun z : ℝ => ⨆ S : ℕ, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      = fun z : ℝ => ⨆ S : ℕ, (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ 2 := by
    funext z
    exact iSup_congr (fun S => (trunc_pow_eq_ofReal_sq (fun i : Fin (S+1) => ∑ k : Fin K,
      curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)))).symm)
  rw [hcongr, lintegral_iSup_trunc_enn Ψ lam H hHm hH1 y]
  refine iSup_congr (fun S => ?_)
  refine lintegral_congr (fun z => ?_)
  exact trunc_pow_eq_ofReal_sq (fun i : Fin (S+1) => ∑ k : Fin K,
    curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)))

/-- **The `y`-push**, in item 2's `ofReal`/square shape.  Uses `lintegral_iSup'` (the
`AEMeasurable` + a.e.-monotone variant, which is the right one here: the inner `z`-integral is only
a.e.-measurable in `y`) with
* measurability from `AEMeasurable.lintegral_prod_right` applied to `aemeasurable_trunc_enn` — whose
  statement is *already* the `ofReal`/square form on the product `ℝ × ℝ`, i.e. this integrand
  verbatim, so no conversion is needed;
* a.e.-monotonicity from `trunc_ofReal_sq_mono` (pointwise in `z`, then `lintegral_mono`). -/
lemma lintegral_iSup_trunc_y (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) :
    (∫⁻ y in Set.Ioc (0:ℝ) 1, ⨆ S : ℕ, ∫⁻ z : ℝ, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      = ⨆ S : ℕ, ∫⁻ y in Set.Ioc (0:ℝ) 1, ∫⁻ z : ℝ, (ENNReal.ofReal (⨆ i : Fin (S+1),
          ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
  refine lintegral_iSup' (fun S =>
    (AEMeasurable.lintegral_prod_right (aemeasurable_trunc_enn Ψ lam H hHm hH1 S)).mono_measure
      Measure.restrict_le_self) ?_
  filter_upwards with y
  intro S S' h
  refine lintegral_mono (fun z => ?_)
  exact trunc_ofReal_sq_mono Ψ lam H y z h

/-- **The `(y,z)` Tonnelli swap** for a level-`S` truncation integrand, in item 2's shape.  The
hypothesis is `aemeasurable_trunc_enn` (joint measurability on `volume.prod volume`) moved to the
product of the restricted measures by `monotonicity of `Measure.prod`. -/
lemma lintegral_lintegral_trunc_swap (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (S : ℕ) :
    (∫⁻ y in Set.Ioc (0:ℝ) 1, ∫⁻ z : ℝ, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      = ∫⁻ z : ℝ, ∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
  refine lintegral_lintegral_swap ?_
  exact (aemeasurable_trunc_enn Ψ lam H hHm hH1 S).mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl)

/-- **The combination lemma** (the assembled right-hand side of item 3): the `y`-average of the
maximal function of the translate is the supremum over the truncation level of the doubly-swapped
level integrals — step 1, the pointwise `S → ∞` identity, the two pushes and the swap, fused. -/
theorem lintegral_bandMax_transl_eq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) :
    (∫⁻ y in Set.Ioc (0:ℝ) 1, bandMax Ψ lam (transl H y))
      = ⨆ S : ℕ, ∫⁻ z : ℝ, ∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1),
          ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
  calc ∫⁻ y in Set.Ioc (0:ℝ) 1, bandMax Ψ lam (transl H y)
      = ∫⁻ y in Set.Ioc (0:ℝ) 1, ∫⁻ z : ℝ, (⨆ j : ℕ, ‖∑ k : Fin K, curvePtJ Ψ lam H j z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ₑ) ^ (2:ℝ) := by
          refine lintegral_congr (fun y => ?_)
          rw [bandMax_transl_eq_curvePtJ]
          refine lintegral_congr (fun z => ?_)
          congr 1
          refine iSup_congr (fun j => ?_)
          congr 1
          refine Finset.sum_congr rfl (fun k _ => ?_)
          exact mul_comm _ _
    _ = ∫⁻ y in Set.Ioc (0:ℝ) 1, ∫⁻ z : ℝ, ⨆ S : ℕ, (ENNReal.ofReal (⨆ i : Fin (S+1),
          ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
          refine lintegral_congr (fun y => ?_)
          refine lintegral_congr (fun z => ?_)
          rw [iSup_eq_iSup_trunc]
    _ = ∫⁻ y in Set.Ioc (0:ℝ) 1, ⨆ S : ℕ, ∫⁻ z : ℝ, (ENNReal.ofReal (⨆ i : Fin (S+1),
          ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
          refine lintegral_congr (fun y => ?_)
          rw [lintegral_iSup_trunc_z Ψ lam H hHm hH1 y]
    _ = ⨆ S : ℕ, ∫⁻ y in Set.Ioc (0:ℝ) 1, ∫⁻ z : ℝ, (ENNReal.ofReal (⨆ i : Fin (S+1),
          ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 :=
          lintegral_iSup_trunc_y Ψ lam H hHm hH1
    _ = ⨆ S : ℕ, ∫⁻ z : ℝ, ∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1),
          ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2 := by
          refine iSup_congr (fun S => ?_)
          rw [lintegral_lintegral_trunc_swap Ψ lam H hHm hH1 S]

/-! ### Auxiliary arithmetic for the entropy comparison -/

private lemma ent_min_add_le (K x y : ℝ) (hy : 0 ≤ y) : min K (x+y) ≤ min K x + y := by
  rcases le_total x K with h | h
  · rcases le_total (x+y) K with h2 | h2
    · rw [min_eq_right h, min_eq_right h2]
    · rw [min_eq_right h, min_eq_left h2]; linarith
  · rw [min_eq_left h]
    rcases le_total (x+y) K with h2 | h2
    · rw [min_eq_right h2]; linarith
    · rw [min_eq_left h2]; linarith

private lemma ent_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x+y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 : x + y ≤ (Real.sqrt x + Real.sqrt y)^2 := by
    rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x+y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y)^2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

private lemma ent_sqrt_min_add_le (K x y : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (min K (x+y)) ≤ Real.sqrt (min K x) + Real.sqrt y :=
  (Real.sqrt_le_sqrt (ent_min_add_le K x y hy)).trans
    (ent_sqrt_add_le _ _ (le_min hK hx) hy)

private lemma ent_four_pow_ge (S : ℕ) : ((S:ℝ) + 1) ≤ (4:ℝ)^S := by
  induction S with
  | zero => norm_num
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hstep : ((n:ℝ) + 2) ≤ 4 * ((n:ℝ) + 1) := by linarith
      have hcast : ((n+1 : ℕ) : ℝ) + 1 = (n:ℝ) + 2 := by push_cast; ring
      rw [hcast]
      calc (n:ℝ) + 2 ≤ 4 * ((n:ℝ) + 1) := hstep
        _ ≤ 4 * (4:ℝ)^n := by linarith
        _ = (4:ℝ)^(n+1) := by rw [pow_succ]; ring

private lemma ent_tail_le_one (K : ℝ) (S : ℕ) :
    ((1:ℝ)/2)^S * Real.sqrt (min K ((S:ℝ) + 1)) ≤ 1 := by
  have hs : Real.sqrt ((S:ℝ) + 1) ≤ (2:ℝ)^S := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (2:ℝ)^S)]
    refine Real.sqrt_le_sqrt ?_
    have h2 : (2:ℝ)^S * 2^S = (4:ℝ)^S := by rw [← mul_pow]; norm_num
    rw [pow_two, h2]; exact ent_four_pow_ge S
  calc ((1:ℝ)/2)^S * Real.sqrt (min K ((S:ℝ) + 1))
      ≤ ((1:ℝ)/2)^S * Real.sqrt ((S:ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (min_le_right _ _)) (by positivity)
    _ ≤ ((1:ℝ)/2)^S * (2:ℝ)^S := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The dyadic entropy level `cov + 2` at radius `r`. -/
private noncomputable def entA (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) (z : ℝ)
    (r : ℝ) : ℝ :=
  (winEntropy K (⇑Ψ) H z r).toReal + 2

private lemma entA_nonneg (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) (z r : ℝ) :
    0 ≤ entA Ψ H z r := by
  have := ENNReal.toReal_nonneg (a := winEntropy K (⇑Ψ) H z r)
  simp only [entA]; linarith

private lemma entA_apply (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) (z r : ℝ) :
    entA Ψ H z r = (winEntropy K (⇑Ψ) H z r).toReal + 2 := rfl

/-- **The per-`z` chain bound, applied** (`chain_bound_at_z_curveRad` + `exists_phased_covers`,
with the `M`-sum rewritten in terms of the covering numbers `winEntropy`). -/
theorem chain_bound_at_z_winEnt (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 9 * ESU.cChain ∧ ∀ (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ), 1 ≤ S →
      (∀ t : ℕ, winEntropy K (⇑Ψ) H z ((2 * curveRad Ψ lam H S z) * (1/2:ℝ)^t) ≠ ⊤) →
      (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
        ≤ ENNReal.ofReal ((C * curveRad Ψ lam H S z
            * (1 + ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
                (entA Ψ H z ((2 * curveRad Ψ lam H S z) * (1/2:ℝ)^t))))) ^ 2) := by
  obtain ⟨C₀, hC₀pos, hC₀le, hC₀⟩ := chain_bound_at_z_curveRad Ψ lam hsep
  have hC₀le' : 3 * C₀ ≤ 9 * ESU.cChain := by
    have := ESU.cChain_pos
    linarith
  refine ⟨3 * C₀, by positivity, hC₀le', fun H S z hS hfin => ?_⟩
  obtain ⟨Sc, hcard, hcover⟩ := exists_phased_covers Ψ lam H S S z
    (2 * curveRad Ψ lam H S z) hfin
  have hc0 : 0 ≤ curveRad Ψ lam H S z := curveRad_nonneg Ψ lam H S z
  have hcardR : ∀ t, 1 ≤ t → t ≤ S → ((Sc t).card : ℝ)
      ≤ (winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)).toReal + 1 := by
    intro t ht1 htS
    have h1 := hcard t ht1 htS
    have hnt := hfin t
    have hnt' : winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t) + 1 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hnt, ENNReal.one_ne_top⟩
    have h2 : ((Sc t).card : ℝ)
        ≤ (winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t) + 1).toReal := by
      rw [← ENNReal.toReal_natCast (Sc t).card]
      exact ENNReal.toReal_mono hnt' h1
    rw [ENNReal.toReal_add hnt ENNReal.one_ne_top, ENNReal.toReal_one] at h2
    exact h2
  set M : ℕ → ℕ := fun t => if t = 0 then 1 else
    (if t = S then max ((Sc t).card) (S+1) else max ((Sc t).card) 1) with hM
  have hMval : ∀ t : ℕ, M t = (if t = 0 then 1 else
      (if t = S then max ((Sc t).card) (S+1) else max ((Sc t).card) 1)) := fun t => by rw [hM]
  have hM0 : 1 ≤ M 0 := by
    rw [hMval 0]; simp
  have hMS : S + 1 ≤ M S := by
    rw [hMval S]
    by_cases h : S = 0
    · rw [if_pos h]; omega
    · rw [if_neg h, if_pos rfl]; exact le_max_right _ _
  have hcov : ∀ t, 1 ≤ t → t ≤ S → ∃ Sc' : Finset (Fin K → ℂ),
      (∀ i : Fin (S+1), ∃ s ∈ Sc', ∑ k : Fin K, ‖curvePtJ Ψ lam H i z k - s k‖ ^ 2
          ≤ (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)^2) ∧ Sc'.card ≤ M t := by
    intro t ht1 htS
    refine ⟨Sc t, hcover t ht1 htS, ?_⟩
    rw [hMval t, if_neg (by omega : ¬ t = 0)]
    by_cases h : t = S
    · rw [if_pos h]; exact le_max_left _ _
    · rw [if_neg h]; exact le_max_left _ _
  have hmain := hC₀ H S z M hS hM0 hMS hcov
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcmp : (1 + ∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ 3 * (1 + ∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
            (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)))) := by
    have hsplitM : (∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        = (∑ t ∈ Finset.range S, (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
          + (1/2:ℝ)^S * Real.sqrt (min (K:ℝ) ((M S : ℝ) + 1)) :=
      Finset.sum_range_succ _ _
    have hsplitA : (∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
            (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t))))
        = (∑ t ∈ Finset.range S, (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
            (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t))))
          + (1/2:ℝ)^S * Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S))) :=
      Finset.sum_range_succ _ _
    have hsm : (∑ t ∈ Finset.range S,
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ (∑ t ∈ Finset.range S, (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
            (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)))) := by
      refine Finset.sum_le_sum (fun t ht => ?_)
      have htS : t < S := Finset.mem_range.mp ht
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0
        rw [hMval 0, if_pos rfl]
        refine min_le_min le_rfl ?_
        rw [entA_apply]
        norm_num
      · have hMv : M t = max ((Sc t).card) 1 := by
          rw [hMval t, if_neg (by omega : ¬ t = 0), if_neg (by omega : ¬ t = S)]
        rw [hMv]
        have hcardt := hcardR t htpos htS.le
        have hmax : ((max ((Sc t).card) 1 : ℕ) : ℝ)
            ≤ (winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)).toReal + 1 := by
          rw [Nat.cast_max, Nat.cast_one]
          refine max_le ?_ ?_
          · linarith [hcardt]
          · have hnn := ENNReal.toReal_nonneg
              (a := winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t))
            linarith
        rw [entA_apply]
        exact min_le_min le_rfl (by linarith)
    have hlast : (1/2:ℝ)^S * Real.sqrt (min (K:ℝ) ((M S : ℝ) + 1))
        ≤ (1/2:ℝ)^S * Real.sqrt (min (K:ℝ)
            (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S))) + 1 := by
      have hMSle : ((M S : ℝ) + 1)
          ≤ ((winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S)).toReal + 2)
            + ((S:ℝ) + 1) := by
        by_cases h : S = 0
        · subst h
          rw [hMval 0, if_pos rfl]
          have hnn : (0:ℝ) ≤ ((winEntropy K (⇑Ψ) H z
                (2 * curveRad Ψ lam H 0 z * (1/2:ℝ)^0)).toReal) := ENNReal.toReal_nonneg
          push_cast
          linarith
        · have hMv : M S = max ((Sc S).card) (S+1) := by
            rw [hMval S, if_neg h, if_pos rfl]
          rw [hMv, Nat.cast_max, Nat.cast_add, Nat.cast_one]
          have hcardS := hcardR S (by omega) le_rfl
          have hnn : (0:ℝ) ≤ (winEntropy K (⇑Ψ) H z
              (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S)).toReal := ENNReal.toReal_nonneg
          have hmax : max ((Sc S).card : ℝ) ((S:ℝ) + 1) + 1
              = max (((Sc S).card : ℝ) + 1) (((S:ℝ) + 1) + 1) := by
            rcases le_total ((Sc S).card : ℝ) ((S:ℝ) + 1) with hle | hle
            · rw [max_eq_right hle,
                max_eq_right (by linarith : ((Sc S).card : ℝ) + 1 ≤ (S:ℝ) + 1 + 1)]
            · rw [max_eq_left hle,
                max_eq_left (by linarith : ((S:ℝ) + 1) + 1 ≤ ((Sc S).card : ℝ) + 1)]
          rw [hmax]
          refine max_le ?_ ?_
          · linarith [hcardS]
          · linarith
      have hstep : Real.sqrt (min (K:ℝ) ((M S : ℝ) + 1))
          ≤ Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S)))
            + Real.sqrt ((S:ℝ) + 1) := by
        rw [entA_apply]
        exact (Real.sqrt_le_sqrt (min_le_min le_rfl hMSle)).trans
          (ent_sqrt_min_add_le _ _ _ (by positivity)
            (by have hnn := ENNReal.toReal_nonneg
                  (a := winEntropy K (⇑Ψ) H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S))
                linarith)
            (by positivity))
      have htl : (1/2:ℝ)^S * Real.sqrt ((S:ℝ) + 1) ≤ 1 := by
        have h1 := ent_tail_le_one ((S:ℝ) + 1) S
        rwa [min_self] at h1
      calc (1/2:ℝ)^S * Real.sqrt (min (K:ℝ) ((M S : ℝ) + 1))
          ≤ (1/2:ℝ)^S * (Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S)))
              + Real.sqrt ((S:ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (1/2:ℝ)^S * Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S)))
            + (1/2:ℝ)^S * Real.sqrt ((S:ℝ) + 1) := by ring
        _ ≤ (1/2:ℝ)^S * Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S))) + 1 := by linarith
    have hnn : (0:ℝ) ≤ (∑ t ∈ Finset.range S, (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
          (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)))) :=
      Finset.sum_nonneg (fun t _ => by positivity)
    have hnnA : (0:ℝ) ≤ (1/2:ℝ)^S * Real.sqrt (min (K:ℝ)
          (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^S))) := by positivity
    linarith [hsplitM, hsplitA, hsm, hlast, hnn, hnnA]
  have hnn2 : (0:ℝ) ≤ (1 + ∑ t ∈ Finset.range (S+1),
      (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) := by
    have h := Finset.sum_nonneg (fun t (_ : t ∈ Finset.range (S+1)) =>
      show (0:ℝ) ≤ (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)) by positivity)
    linarith
  have hle : C₀ * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ 3 * C₀ * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
            (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)))) := by
    have h1 : C₀ * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ C₀ * curveRad Ψ lam H S z * (3 * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t))))) :=
      mul_le_mul_of_nonneg_left hcmp (mul_nonneg hC₀pos.le hc0)
    calc C₀ * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ C₀ * curveRad Ψ lam H S z * (3 * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t))))) := h1
      _ = 3 * C₀ * curveRad Ψ lam H S z * (1 + ∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
              (entA Ψ H z (2 * curveRad Ψ lam H S z * (1/2:ℝ)^t)))) := by ring
  exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC₀pos.le hc0) (by linarith [hnn2])) hle 2
/-- The `t`-th entropy level `⌊cov⌋₊ + 3` dominates `entA`. -/
private lemma entA_le_floor_add (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (H : Fin K → ℝ → ℂ) (z : ℝ)
    (r : ℝ) (hx : winEntropy K (⇑Ψ) H z r ≠ ⊤) :
    entA Ψ H z r ≤ ((⌊(winEntropy K (⇑Ψ) H z r).toReal⌋₊ : ℕ) : ℝ) + 3 := by
  have h1 : (winEntropy K (⇑Ψ) H z r).toReal
      < (⌊(winEntropy K (⇑Ψ) H z r).toReal⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  simp only [entA]
  linarith

private lemma ent_geom_le_two (S : ℕ) : (∑ t ∈ Finset.range S, ((1:ℝ)/2)^t) ≤ 2 := by
  have hsum : Summable (fun t : ℕ => ((1:ℝ)/2)^t) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have h2 : (∑' t : ℕ, ((1:ℝ)/2)^t) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num)]; norm_num
  have h3 := hsum.sum_le_tsum (Finset.range S)
    (fun i _ => by positivity : ∀ i ∉ Finset.range S, (0:ℝ) ≤ ((1:ℝ)/2)^i)
  rw [h2] at h3
  exact h3

/-- Degenerate case of the per-`z` chain bound: if the curve has radius `0`, every curve point
vanishes and the left-hand side is `0`. -/
lemma chain_bound_degenerate (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) (h0 : curveRad Ψ lam H S z = 0) :
    (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      = 0 := by
  have hz : ∀ i : Fin (S+1), curvePtJ Ψ lam H (i : ℕ) z = 0 := by
    intro i
    funext k
    have h := curvePtJ_sum_sq_le_curveRad_sq Ψ lam H S z i
    have h2 : curveRad Ψ lam H S z ^ 2 = 0 := by rw [h0]; ring
    rw [h2] at h
    have hk : ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2 ≤ 0 :=
      le_trans (Finset.single_le_sum
        (fun l _ => sq_nonneg ‖curvePtJ Ψ lam H (i : ℕ) z l‖) (Finset.mem_univ k)) h
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hk (sq_nonneg _)))
  have hfun : (fun y : ℝ => (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      = fun _ => (0 : ℝ≥0∞) := by
    funext y
    have hsum : ∀ i : Fin (S+1), (∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) = 0 := by
      intro i
      rw [hz i]
      simp
    simp [hsum]
  rw [hfun]
  simp

/-- **The per-`z` chain bound in entropy-integral form.** -/
theorem chain_bound_at_z_ent (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 90 * ESU.cChain ∧ ∀ (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ), 1 ≤ S →
      (∀ t : ℕ, winEntropy K (⇑Ψ) H z ((2 * curveRad Ψ lam H S z) * (1/2:ℝ)^t) ≠ ⊤) →
      (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
        ≤ (ENNReal.ofReal C * (ENNReal.ofReal (curveRad Ψ lam H S z)
            + ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)))) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀le, hC₀⟩ := chain_bound_at_z_winEnt Ψ lam hsep
  have hC₀le' : 10 * C₀ ≤ 90 * ESU.cChain := by
    have := ESU.cChain_pos
    linarith
  refine ⟨10 * C₀, by positivity, hC₀le', fun H S z hS hfin => ?_⟩
  have hmain := hC₀ H S z hS hfin
  set c : ℝ := curveRad Ψ lam H S z with hcdef
  set J : ℝ≥0∞ := ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
      ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)) with hJ
  by_cases hJtop : J = ⊤
  · have hne : ENNReal.ofReal (10 * C₀) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith [hC₀pos]
    have h1 : ENNReal.ofReal c + J = (⊤ : ℝ≥0∞) := by rw [hJtop]; simp
    have htop : (ENNReal.ofReal (10 * C₀) * (ENNReal.ofReal c + J)) ^ 2 = ⊤ := by
      rw [h1, ENNReal.mul_top hne, ENNReal.top_pow (by norm_num)]
    rw [htop]
    exact le_top
  -- from now on `J` is finite
  have hMle : ∀ t : ℕ,
      ((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ≥0∞)
        ≤ winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t) := by
    intro t
    have hne := hfin t
    have h1 : ((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ)
        ≤ (winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal := Nat.floor_le (by positivity)
    calc ((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal ((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal ((winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal) :=
          ENNReal.ofReal_le_ofReal h1
      _ = winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t) := ENNReal.ofReal_toReal hne
  -- the sum of the chain bound versus the `⌊·⌋₊`-sum
  have hsum_le : (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t))))
      ≤ (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
          (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)))
        + 2 * Real.sqrt 2 := by
    have hterm : ∀ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t)))
        ≤ (1/2:ℝ)^t * (Real.sqrt (min (K:ℝ)
            (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1))
          + Real.sqrt 2) := by
      intro t ht
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hfl := entA_le_floor_add Ψ H z ((2*c) * (1/2:ℝ)^t) (hfin t)
      have h2 : entA Ψ H z ((2*c) * (1/2:ℝ)^t)
          ≤ (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1) + 2 := by
        linarith [hfl]
      exact le_trans (Real.sqrt_le_sqrt (min_le_min le_rfl h2))
        (ent_sqrt_min_add_le _ _ _ (by positivity) (by positivity) (by positivity))
    calc (∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t))))
        ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t
            * (Real.sqrt (min (K:ℝ)
                (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1))
              + Real.sqrt 2) := Finset.sum_le_sum hterm
      _ = ∑ t ∈ Finset.range (S+1), ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
              (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1))
            + (1/2:ℝ)^t * Real.sqrt 2) := Finset.sum_congr rfl (fun t _ => by ring)
      _ = (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
              (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)))
            + Real.sqrt 2 * (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul,
            mul_comm (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t) (Real.sqrt 2)]
      _ ≤ (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
              (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)))
            + Real.sqrt 2 * 2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (ent_geom_le_two (S+1)) (by positivity))
      _ = _ + 2 * Real.sqrt 2 := by ring
  -- the item-5 comparison
  have hanti : ∀ x y : ℝ, 0 < x → x ≤ y →
      winEntropy K (⇑Ψ) H z y ≤ winEntropy K (⇑Ψ) H z x :=
    fun x y hx hxy => winEntropy_antitone K (⇑Ψ) H z hx hxy
  have hc0 : 0 ≤ c := curveRad_nonneg Ψ lam H S z
  rcases eq_or_lt_of_le hc0 with hceq | hcpos
  · have hdeg := chain_bound_degenerate Ψ lam H S z (hcdef.symm.trans hceq.symm)
    rw [hdeg]
    exact bot_le
  have hitem5 := ofReal_sum_dyadic_le_lintegral_entropy_scaled
    (winEntropy K (⇑Ψ) H z) hanti (c := c) hcpos K
      (fun t => ⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊) hMle S
  -- the `+1` slack of the entropy integral
  have hint_le : ∫⁻ r in Set.Ioc (0:ℝ) (2*c),
        min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winEntropy K (⇑Ψ) H z r + 1) ^ ((1:ℝ)/2))
      ≤ J + ENNReal.ofReal (2*c) := by
    have hpt : ∀ r : ℝ, min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
        ((winEntropy K (⇑Ψ) H z r + 1) ^ ((1:ℝ)/2))
        ≤ min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)) + 1 := by
      intro r
      have h1 : (winEntropy K (⇑Ψ) H z r + 1) ^ ((1:ℝ)/2)
          ≤ (winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2) + 1 := by
        have h := ENNReal.rpow_add_le_add_rpow (p := (1:ℝ)/2)
          (winEntropy K (⇑Ψ) H z r) 1
          (by norm_num : (0:ℝ) ≤ 1/(2:ℝ)) (by norm_num : (1:ℝ)/(2:ℝ) ≤ 1)
        have hone : (1:ℝ≥0∞) ^ ((1:ℝ)/2) = 1 := by simp
        rw [hone] at h
        exact h
      exact (min_le_min le_rfl h1).trans (min_add_le' _ _ _)
    calc ∫⁻ r in Set.Ioc (0:ℝ) (2*c), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winEntropy K (⇑Ψ) H z r + 1) ^ ((1:ℝ)/2))
        ≤ ∫⁻ r in Set.Ioc (0:ℝ) (2*c), (min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)) + 1) := lintegral_mono hpt
      _ = (∫⁻ r in Set.Ioc (0:ℝ) (2*c), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) + ENNReal.ofReal (2*c) := by
          rw [lintegral_add_right (f := fun r : ℝ => min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) measurable_const,
            setLIntegral_const, Real.volume_Ioc, sub_zero, one_mul]
      _ ≤ J + ENNReal.ofReal (2*c) := by
          refine add_le_add ?_ le_rfl
          rw [hJ]
          exact lintegral_mono_set (fun r hr => hr.1)
  -- the `ℝ`-level bound for the `⌊·⌋₊`-sum
  have hSM : (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
        (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)))
      ≤ c⁻¹ * (J.toReal + 2*c) := by
    have h1 : (ENNReal.ofReal (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
          (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)))).toReal
        ≤ (ENNReal.ofReal c⁻¹ * (J + ENNReal.ofReal (2*c))).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hJtop, ENNReal.ofReal_ne_top⟩))
        (hitem5.trans (mul_le_mul' le_rfl hint_le))
    have h2 : (ENNReal.ofReal c⁻¹ * (J + ENNReal.ofReal (2*c))).toReal
        = c⁻¹ * (J.toReal + 2*c) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hcpos)),
        ENNReal.toReal_add hJtop ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)]
      try ring
    have h3 : (ENNReal.ofReal (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
          (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)))).toReal
        = ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ)
            (((⌊(winEntropy K (⇑Ψ) H z ((2*c) * (1/2:ℝ)^t)).toReal⌋₊ : ℕ) : ℝ) + 1)) :=
      ENNReal.toReal_ofReal (Finset.sum_nonneg (fun t _ => by positivity))
    simpa only [h3, h2] using h1
  -- the final `ℝ`-arithmetic
  have hreal : C₀ * c * (1 + (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t)))))
      ≤ 10 * C₀ * (c + J.toReal) := by
    have h1 : (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t))))
        ≤ c⁻¹ * (J.toReal + 2*c) + 2 * Real.sqrt 2 := by linarith [hsum_le, hSM]
    have hs2 : Real.sqrt 2 ≤ 3/2 := by
      rw [Real.sqrt_le_iff]; constructor <;> norm_num
    have h2 : c * (∑ t ∈ Finset.range (S+1),
          (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t))))
        ≤ J.toReal + 2*c + 3*c := by
      calc c * (∑ t ∈ Finset.range (S+1),
            (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) (entA Ψ H z ((2*c) * (1/2:ℝ)^t))))
          ≤ c * (c⁻¹ * (J.toReal + 2*c) + 2 * Real.sqrt 2) :=
            mul_le_mul_of_nonneg_left h1 hcpos.le
        _ = J.toReal + 2*c + 2 * Real.sqrt 2 * c := by
            rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul,
              mul_comm c (2 * Real.sqrt 2)]
        _ ≤ J.toReal + 2*c + 3*c := by nlinarith [hs2, hcpos.le]
    have hcJ : (0:ℝ) ≤ J.toReal := ENNReal.toReal_nonneg (a := J)
    nlinarith [h2, hcpos, hcJ, hC₀pos.le]
  -- assemble
  refine hmain.trans ?_
  have hstep : ENNReal.ofReal ((10 * C₀ * (c + J.toReal))^2)
      = (ENNReal.ofReal (10 * C₀) * (ENNReal.ofReal c + J))^2 := by
    rw [ENNReal.ofReal_pow (by positivity),
      show (10:ℝ) * C₀ * (c + J.toReal) = (10 * C₀) * (c + J.toReal) by ring,
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add hc0 (ENNReal.toReal_nonneg (a := J)), ENNReal.ofReal_toReal hJtop]
  rw [← hstep]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hreal 2)

end EntropyBridge



end

end FWS
























-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/UniformConsts.lean ====

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ESU

open OldSWM.BourgainMax
open _root_.MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- A `K`-free constant dominating the constant of the entropy input (the only `K`-dependence of
that input is the explicit factor `(log (K+2))²`). -/
noncomputable def cEnt (Ψ : SchwartzMap ℝ ℂ) : ℝ :=
  Classical.choose (FWS.l2_entropy_input_winEntropy Ψ)

lemma cEnt_pos (Ψ : SchwartzMap ℝ ℂ) : 0 < cEnt Ψ :=
  (Classical.choose_spec (FWS.l2_entropy_input_winEntropy Ψ)).1

lemma cEnt_spec (Ψ : SchwartzMap ℝ ℂ) :
    ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K)) ((OldSWM.winEntropy K (⇑Ψ) f x r) ^ ((1:ℝ)/2))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) :=
  (Classical.choose_spec (FWS.l2_entropy_input_winEntropy Ψ)).2

/-- A `K`-free constant dominating the constant of the (single-function) dilation maximal bound. -/
noncomputable def cCurve (Ψ : SchwartzMap ℝ ℂ) : ℝ :=
  Classical.choose (Commons.Analysis.Fourier.maximal_dilation_convolution_l2 Ψ)

lemma cCurve_pos (Ψ : SchwartzMap ℝ ℂ) : 0 < cCurve Ψ :=
  (Classical.choose_spec (Commons.Analysis.Fourier.maximal_dilation_convolution_l2 Ψ)).1

lemma cCurve_spec (Ψ : SchwartzMap ℝ ℂ) :
    ∀ (g : ℝ → ℂ), MemLp g 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
          ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (cCurve Ψ) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) :=
  (Classical.choose_spec (Commons.Analysis.Fourier.maximal_dilation_convolution_l2 Ψ)).2

end

end ESU

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/EntropyStep3.lean ====

set_option maxHeartbeats 2000000

namespace FWS

open OldSWM.BourgainMax
open OldSWM Commons.Analysis.Fourier
open _root_.MeasureTheory _root_.Finset
open scoped BigOperators ENNReal Topology

noncomputable section

/-- `(a + b)^2 ≤ 2 a^2 + 2 b^2` in `ℝ≥0∞`. -/
private lemma enn_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  have ha2 : a ^ 2 ≠ ⊤ := by rw [pow_two]; exact ENNReal.mul_ne_top ha ha
  have hb2 : b ^ 2 ≠ ⊤ := by rw [pow_two]; exact ENNReal.mul_ne_top hb hb
  have hab : a + b ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha, hb⟩
  rw [← ENNReal.toReal_le_toReal (by rw [pow_two]; exact ENNReal.mul_ne_top hab hab)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) ha2,
      ENNReal.mul_ne_top (by norm_num) hb2⟩)]
  rw [ENNReal.toReal_pow, ENNReal.toReal_add ha hb, ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) ha2) (ENNReal.mul_ne_top (by norm_num) hb2),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_pow, ENNReal.toReal_pow]
  nlinarith [sq_nonneg (a.toReal - b.toReal)]

/-- **A uniform a.e. bound from `MemLp ⊤`.** -/
private lemma exists_ae_bound {K : ℕ} (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : Fin K, ∀ᵐ y ∂(volume : Measure ℝ), ‖H k y‖ ≤ M := by
  have h1 : ∀ k : Fin K, ∀ᵐ y ∂(volume : Measure ℝ),
      ‖H k y‖ ≤ (eLpNormEssSup (H k) (volume : Measure ℝ)).toReal := by
    intro k
    filter_upwards [ae_le_eLpNormEssSup (f := H k) (μ := (volume : Measure ℝ))] with y hy
    have hne : eLpNormEssSup (H k) (volume : Measure ℝ) ≠ ⊤ :=
      (eLpNormEssSup_le_eLpNorm_top.trans_lt (hH k)).ne
    have h2 : (‖H k y‖ₑ).toReal ≤ (eLpNormEssSup (H k) (volume : Measure ℝ)).toReal :=
      ENNReal.toReal_mono hne hy
    rwa [enorm_eq_ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at h2
  refine ⟨∑ k : Fin K, (eLpNormEssSup (H k) (volume : Measure ℝ)).toReal,
    Finset.sum_nonneg (fun k _ => ENNReal.toReal_nonneg), fun k => ?_⟩
  filter_upwards [h1 k] with y hy
  exact hy.trans (Finset.single_le_sum
    (f := fun k : Fin K => (eLpNormEssSup (H k) (volume : Measure ℝ)).toReal)
    (fun l _ => ENNReal.toReal_nonneg) (Finset.mem_univ k))

/-- Measurability in `z` of `(ofReal (curveRad … S z))²`. -/
private lemma aemeasurable_curveRad_sq (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) (S : ℕ) :
    AEMeasurable (fun z : ℝ => (ENNReal.ofReal (curveRad Ψ lam H S z)) ^ 2) volume := by
  have hterm : ∀ i : Fin (S+1), Measurable (fun z : ℝ =>
      ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2) := by
    intro i
    refine Finset.measurable_sum _ (fun k _ => ?_)
    have hcurve : Measurable (fun z : ℝ => curvePtJ Ψ lam H (i : ℕ) z k) :=
      (measurable_curvePtJ Ψ lam H hHm hH1 (i : ℕ) k).comp
        (by fun_prop : Measurable fun z : ℝ => ((0:ℝ), z))
    exact (hcurve.norm).pow_const 2
  have hF : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (S+1) => fun z : ℝ => ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2)) := by
    refine Finset.measurable_sup' Finset.univ_nonempty (fun i _ => ?_)
    exact hterm i
  have hEq : (Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (S+1) => fun z : ℝ => ∑ k : Fin K, ‖curvePtJ Ψ lam H (i : ℕ) z k‖ ^ 2))
      = fun z : ℝ => curveRadSq Ψ lam H S z := by
    funext z
    simp only [curveRadSq]
    exact Finset.sup'_apply ..
  have hrad : AEMeasurable (fun z : ℝ => curveRad Ψ lam H S z) volume := by
    rw [hEq] at hF
    have h2 : Measurable (fun z : ℝ => Real.sqrt (curveRadSq Ψ lam H S z)) :=
      Real.continuous_sqrt.measurable.comp hF
    simpa only [curveRad] using h2.aemeasurable
  exact ((ENNReal.measurable_ofReal.comp_aemeasurable hrad).pow_const 2)

/-- **Uniform form of item 4** (the constant does not depend on `H`). -/
private theorem lintegral_curveRadSq_le_uniform (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ) :
    ∃ C : ℝ, 0 < C ∧ C ≤ ESU.cCurve Ψ + 1 ∧ ∀ (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, Integrable (H k)) → (∀ k : Fin K, Measurable (H k)) →
      ∀ S : ℕ, ∫⁻ z : ℝ, ENNReal.ofReal (curveRadSq Ψ lam H S z) ≤ ENNReal.ofReal C * bandSq H := by
  set C₀ : ℝ := ESU.cCurve Ψ with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; exact ESU.cCurve_pos Ψ
  have hC₀ : ∀ (g : ℝ → ℂ), MemLp g 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
          ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ) ^ (2 : ℝ)
        ≤ ENNReal.ofReal C₀ * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
    intro g hg
    have h := ESU.cCurve_spec Ψ g hg
    simpa only [hC₀def] using h
  refine ⟨C₀ + 1, by positivity, ?_, fun H hH2 hH1 hHm S => ?_⟩
  · rw [hC₀def]
  have hper : ∀ k : Fin K, (∫⁻ z : ℝ,
        (⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)))
      ≤ ENNReal.ofReal C₀ * ∫⁻ z : ℝ, ‖H k z‖ₑ ^ (2:ℝ) := by
    intro k
    refine le_trans (lintegral_mono (fun z => ?_)) (hC₀ (H k) (hH2 k))
    refine iSup_le (fun j => ?_)
    have heq : (∫ v : ℝ, H k v * winK Ψ j (z - v))
        = ∫ v : ℝ, H k v * ((((winScale j)⁻¹)⁻¹) • Ψ ((z - v) / (winScale j)⁻¹)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
      show H k v * winK Ψ j (z - v)
        = H k v * ((((winScale j)⁻¹)⁻¹) • Ψ ((z - v) / (winScale j)⁻¹))
      have hwk : winK Ψ j (z - v) = ((((winScale j)⁻¹)⁻¹) • Ψ ((z - v) / (winScale j)⁻¹)) := by
        rw [← winK_eq_curve Ψ j (z - v)]
      rw [hwk]
    rw [heq]
    exact ENNReal.rpow_le_rpow (le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖∫ v : ℝ, H k v * ((t : ℝ)⁻¹ • Ψ ((z - v) / (t : ℝ)))‖ₑ)
      ⟨(winScale j)⁻¹, inv_winScale_pos j⟩) (by norm_num)
  have hmeas : ∀ k : Fin K, AEMeasurable (fun z : ℝ =>
      ⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)) volume := by
    intro k
    refine AEMeasurable.iSup (fun j => ?_)
    have hcont : Continuous (fun u : ℝ => winK Ψ j u) := by
      unfold winK
      exact continuous_const.mul (Ψ.continuous.comp (continuous_const.mul continuous_id))
    have hconv : Measurable (fun z : ℝ => ∫ v : ℝ, H k v * winK Ψ j (z - v)) :=
      BourgainFatou.measurable_parametric_integral
        (K := fun p : ℝ × ℝ => winK Ψ j (p.1 - p.2))
        (hcont.measurable.comp (measurable_fst.sub measurable_snd))
        (hHm k) (fun z => integrable_mul_winK Ψ (hH1 k) j z)
    exact (hconv.enorm.pow_const 2).aemeasurable
  have hbandSq : (∫⁻ z : ℝ, ∑ k : Fin K, ‖H k z‖ₑ ^ (2:ℝ)) = bandSq H := by
    unfold bandSq
    refine lintegral_congr (fun z => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl
      (fun k _ => (ofReal_norm_sq_eq_enorm_rpow_two (H k z)).symm)
  calc ∫⁻ z : ℝ, ENNReal.ofReal (curveRadSq Ψ lam H S z)
      ≤ ∫⁻ z : ℝ, ∑ k : Fin K, ⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ) :=
        lintegral_mono (fun z => ofReal_curveRadSq_le Ψ lam H S z)
    _ = ∑ k : Fin K, ∫⁻ z : ℝ, (⨆ j : ℕ, ‖∫ v : ℝ, H k v * winK Ψ j (z - v)‖ₑ ^ (2:ℝ)) :=
        lintegral_finsetSum' _ (fun k _ => hmeas k)
    _ ≤ ∑ k : Fin K, ENNReal.ofReal C₀ * ∫⁻ z : ℝ, ‖H k z‖ₑ ^ (2:ℝ) :=
        Finset.sum_le_sum (fun k _ => hper k)
    _ = ENNReal.ofReal C₀ * ∑ k : Fin K, ∫⁻ z : ℝ, ‖H k z‖ₑ ^ (2:ℝ) := by rw [Finset.mul_sum]
    _ = ENNReal.ofReal C₀ * ∫⁻ z : ℝ, ∑ k : Fin K, ‖H k z‖ₑ ^ (2:ℝ) := by
        rw [lintegral_finsetSum' _ (fun k _ =>
          ((hH2 k).aemeasurable.enorm.pow_const 2))]
    _ = ENNReal.ofReal C₀ * bandSq H := by rw [hbandSq]
    _ ≤ ENNReal.ofReal (C₀ + 1) * bandSq H := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (le_add_of_nonneg_right zero_le_one : C₀ ≤ C₀ + 1)) (bandSq H)

/-- **The averaged one-step bound.** -/
theorem lintegral_bandMax_transl_le (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ A : ℝ, 0 < A ∧ A ≤ (90 * ESU.cChain)^2 * (2 * (ESU.cCurve Ψ + 1)
        + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2) ∧ ∀ (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) →
      (∀ k : Fin K, Measurable (H k)) →
      (∀ k : Fin K, Integrable (H k)) →
      (∫⁻ y in Set.Ioc (0:ℝ) 1, bandMax Ψ lam (transl H y)) ≤ ENNReal.ofReal A * bandSq H := by
  obtain ⟨C, hCpos, hCle, hC⟩ := chain_bound_at_z_ent Ψ lam hsep
  obtain ⟨CA, hCApos, hCAle, hCA⟩ := lintegral_curveRadSq_le_uniform Ψ lam
  set CB : ℝ := ESU.cEnt Ψ with hCBdef
  have hCBpos : 0 < CB := by rw [hCBdef]; exact ESU.cEnt_pos Ψ
  have hCB : ∀ (K' : ℕ) (f : Fin K' → ℝ → ℂ),
      (∀ k : Fin K', MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K', MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K')) ((OldSWM.winEntropy K' (⇑Ψ) f x r) ^ ((1:ℝ)/2))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((CB * (Real.log ((K':ℝ)+2))^2)^2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K', ‖f k x‖^2) := by
    intro K' f hf2 hftop
    have h := ESU.cEnt_spec Ψ K' f hf2 hftop
    simpa only [hCBdef] using h
  have hlog : (0:ℝ) < (Real.log ((K:ℝ)+2))^2 := by
    refine pow_pos ?_ 2
    exact Real.log_pos (by linarith [(Nat.cast_nonneg K : (0:ℝ) ≤ (K:ℝ))] :
      (1:ℝ) < (K:ℝ) + 2)
  set CB' : ℝ := (CB * (Real.log ((K:ℝ)+2))^2)^2 with hCB'def
  have hCB'pos : 0 < CB' := by
    rw [hCB'def]; exact pow_pos (mul_pos hCBpos hlog) 2
  have hApos : 0 < C^2 * (2*CA + 2*CB') :=
    mul_pos (pow_pos hCpos 2) (by linarith [hCApos, hCB'pos])
  refine ⟨C^2 * (2*CA + 2*CB'), hApos, ?_, fun H hH2 hHtop hHm hH1 => ?_⟩
  · have hC2 : C^2 ≤ (90 * ESU.cChain)^2 := by
      have h2 : 0 < ESU.cChain := ESU.cChain_pos
      nlinarith [hCle, hCpos, h2]
    have hsum_le : 2*CA + 2*CB'
        ≤ 2 * (ESU.cCurve Ψ + 1) + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2 := by
      rw [hCB'def, hCBdef]
      linarith
    have hsum_nn : 0 ≤ 2*CA + 2*CB' := by linarith [hCApos, hCB'pos]
    calc C^2 * (2*CA + 2*CB')
        ≤ (90 * ESU.cChain)^2 * (2*CA + 2*CB') := mul_le_mul_of_nonneg_right hC2 hsum_nn
      _ ≤ (90 * ESU.cChain)^2 * (2 * (ESU.cCurve Ψ + 1)
            + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2) :=
          mul_le_mul_of_nonneg_left hsum_le (sq_nonneg _)
  obtain ⟨M, hM0, hMbd⟩ := exists_ae_bound H hHtop
  -- monotonicity of the inner term in `S`
  have hmono : ∀ S S' : ℕ, S ≤ S' → ∀ z,
      (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      ≤ (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S'+1), ‖∑ k : Fin K,
          curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2) := by
    intro S S' hSS' z
    refine lintegral_mono (fun y => ?_)
    refine pow_le_pow_left₀ (bot_le : (⊥ : ℝ≥0∞) ≤ _) (ENNReal.ofReal_le_ofReal ?_) 2
    refine ciSup_le (fun i => ?_)
    exact le_ciSup (Set.finite_range (fun i : Fin (S'+1) =>
      ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)).bddAbove
      ⟨(i : ℕ), Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hSS')⟩
  -- the per-`z` bound for `1 ≤ S`
  have hptpos : ∀ S : ℕ, 1 ≤ S → ∀ z,
      (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1), ‖∑ k : Fin K,
        curvePtJ Ψ lam H (i : ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal (curveRad Ψ lam H S z)
          + ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)))) ^ 2 := by
    intro S hS z
    by_cases hc0 : curveRad Ψ lam H S z = 0
    · rw [chain_bound_degenerate Ψ lam H S z hc0]
      exact bot_le
    · have hpos : 0 < curveRad Ψ lam H S z :=
        lt_of_le_of_ne (curveRad_nonneg Ψ lam H S z) (Ne.symm hc0)
      exact hC H S z hS (fun t => winEntropy_ne_top Ψ H hM0 hMbd z
        (by positivity))
  -- measurability and the square identity
  have hmeascore : ∀ S : ℕ, AEMeasurable (fun z : ℝ =>
      (ENNReal.ofReal (curveRad Ψ lam H S z)) ^ 2) volume :=
    fun S => aemeasurable_curveRad_sq Ψ lam H hHm hH1 S
  have hsq : ∀ (S : ℕ) (z : ℝ), (ENNReal.ofReal (curveRad Ψ lam H S z)) ^ 2
      = ENNReal.ofReal (curveRadSq Ψ lam H S z) := by
    intro S z
    rw [← ENNReal.ofReal_pow (curveRad_nonneg Ψ lam H S z), curveRad,
      Real.sq_sqrt (curveRadSq_nonneg Ψ lam H S z)]
  -- the `z`-integral, for `1 ≤ S`
  have hzpos : ∀ S : ℕ, 1 ≤ S →
      (∫⁻ z, (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1),
        ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2))
      ≤ ENNReal.ofReal (C^2 * (2*CA + 2*CB')) * bandSq H := by
    intro S hS
    refine le_trans (lintegral_mono (fun z => hptpos S hS z)) ?_
    -- rewrite the integrand
    have hpt2 : ∀ z : ℝ, (ENNReal.ofReal C * (ENNReal.ofReal (curveRad Ψ lam H S z)
          + ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)))) ^ 2
        ≤ ENNReal.ofReal (C^2) * (2 * ENNReal.ofReal (curveRadSq Ψ lam H S z)
            + 2 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2) := by
      intro z
      have h1 : (ENNReal.ofReal C * (ENNReal.ofReal (curveRad Ψ lam H S z)
            + ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)))) ^ 2
          = ENNReal.ofReal (C^2) * (ENNReal.ofReal (curveRad Ψ lam H S z)
            + ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2 := by
        rw [mul_pow, ← ENNReal.ofReal_pow (le_of_lt hCpos)]
      rw [h1]
      refine mul_le_mul' le_rfl ?_
      refine (enn_add_sq_le (ENNReal.ofReal (curveRad Ψ lam H S z))
        (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2)))).trans (le_of_eq ?_)
      rw [hsq S z]
    refine le_trans (lintegral_mono hpt2) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsplit : (∫⁻ z : ℝ, (2 * ENNReal.ofReal (curveRadSq Ψ lam H S z)
          + 2 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2))
        = (∫⁻ z : ℝ, 2 * ENNReal.ofReal (curveRadSq Ψ lam H S z))
          + ∫⁻ z : ℝ, 2 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2 := by
      have hmeascore' : AEMeasurable (fun z : ℝ => ENNReal.ofReal (curveRadSq Ψ lam H S z)) volume := by
        rw [show (fun z : ℝ => ENNReal.ofReal (curveRadSq Ψ lam H S z))
            = fun z => (ENNReal.ofReal (curveRad Ψ lam H S z)) ^ 2 from
          funext (fun z => (hsq S z).symm)]
        exact hmeascore S
      rw [lintegral_add_left']
      exact AEMeasurable.const_mul hmeascore' 2
    rw [hsplit, lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤),
      lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
    have hA : (∫⁻ z : ℝ, ENNReal.ofReal (curveRadSq Ψ lam H S z))
        ≤ ENNReal.ofReal CA * bandSq H := hCA H hH2 hH1 hHm S
    have hB : (∫⁻ z : ℝ, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2)
        ≤ ENNReal.ofReal CB' * bandSq H := by
      have h := hCB K H hH2 hHtop
      have hEq : (∫⁻ z : ℝ, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2)
          = ∫⁻ z : ℝ, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ) := by
        refine lintegral_congr fun z => ?_
        rw [show (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)
            = (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
              ((winEntropy K (⇑Ψ) H z r) ^ ((1:ℝ)/2))) ^ 2 from
          ENNReal.rpow_natCast _ 2]
      rw [hEq, hCB'def]
      exact h
    refine le_trans (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hA)
      (mul_le_mul' le_rfl hB))) (le_of_eq ?_)
    have hCa : ENNReal.ofReal (C^2 * (2*CA + 2*CB'))
        = ENNReal.ofReal (C^2) * (2 * ENNReal.ofReal CA + 2 * ENNReal.ofReal CB') := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      norm_num
    rw [hCa]
    ring
  -- the general `S`
  have hz : ∀ S : ℕ, (∫⁻ z, (∫⁻ y in Set.Ioc (0:ℝ) 1, (ENNReal.ofReal (⨆ i : Fin (S+1),
        ‖∑ k : Fin K, curvePtJ Ψ lam H (i : ℕ) z k
          * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ 2))
      ≤ ENNReal.ofReal (C^2 * (2*CA + 2*CB')) * bandSq H := by
    intro S
    rcases Nat.eq_zero_or_pos S with hS0 | hSpos
    · subst hS0
      refine le_trans (lintegral_mono (fun z => hmono 0 1 (by norm_num) z)) ?_
      exact hzpos 1 (by norm_num)
    · exact hzpos S hSpos
  rw [lintegral_bandMax_transl_eq Ψ lam H hHm hH1]
  exact iSup_le (fun S => hz S)

end
end FWS

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/EntropyStep4.lean ====

set_option maxHeartbeats 2000000

namespace FWS

open OldSWM.BourgainMax
open OldSWM Commons.Analysis.Fourier
open _root_.MeasureTheory _root_.Finset
open scoped BigOperators ENNReal Topology FourierTransform

noncomputable section

/-- The class of admissible tuples: `L² ∩ L^∞ ∩ L¹`, measurable, band-limited to `[-a,a]`. -/
def Adm {K : ℕ} (a : ℝ) (H : Fin K → ℝ → ℂ) : Prop :=
  (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) ∧
  (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) ∧
  (∀ k : Fin K, Measurable (H k)) ∧
  (∀ k : Fin K, Integrable (H k)) ∧
  (∀ k : Fin K, ∀ ξ : ℝ, a < |ξ| → 𝓕 (H k) ξ = 0)

/-- `bandSq` is translation invariant. -/
lemma bandSq_transl {K : ℕ} (H : Fin K → ℝ → ℂ) (y : ℝ) :
    bandSq (transl H y) = bandSq H := by
  unfold bandSq transl
  exact lintegral_add_right_eq_self
    (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2)) y

/-- `bandSq` as the sum of the per-slice `L²`-energies (from `MemLp` only). -/
lemma bandSq_eq_sum_L2 {K : ℕ} (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) :
    bandSq H = ∑ k : Fin K, ∫⁻ x : ℝ, ‖H k x‖ₑ ^ (2:ℝ) := by
  unfold bandSq
  rw [← lintegral_finsetSum']
  · refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ← enorm_eq_ofReal_norm]
      exact (ENNReal.rpow_natCast _ 2).symm)
  · exact fun k _ => (hH k).aemeasurable.enorm.pow_const 2

/-- The Fourier transform of a translate-difference, in raw-function form. -/
lemma fourier_sub_translate (G : ℝ → ℂ) (hG : Integrable G) (y : ℝ) :
    𝓕 (fun u : ℝ => G u - G (u + y))
      = fun ξ : ℝ => (1 - (Real.fourierChar (y * ξ) : ℂ)) * 𝓕 G ξ := by
  funext ξ
  have hB : Integrable (fun u : ℝ => G (u + y)) := hG.comp_add_right y
  have hsub : Integrable (fun u : ℝ => G u - G (u + y)) := hG.sub hB
  have hadd : 𝓕 (fun u : ℝ => (G u - G (u + y)) + G (u + y))
      = 𝓕 (fun u : ℝ => G u - G (u + y)) + 𝓕 (fun u : ℝ => G (u + y)) := by
    change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) _
      = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) _
        + VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) _
    exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar (by fun_prop) hsub hB
  have hkey : (fun u : ℝ => (G u - G (u + y)) + G (u + y)) = G := by
    funext u; ring
  have h1 := congrFun hadd ξ
  rw [hkey] at h1
  simp only [Pi.add_apply] at h1
  rw [fourier_comp_add_right_real G y ξ, smul_eq_mul] at h1
  have hA : 𝓕 (fun u : ℝ => G u - G (u + y)) ξ
      = 𝓕 G ξ - (Real.fourierChar (y * ξ) : ℂ) * 𝓕 G ξ :=
    eq_sub_iff_add_eq.mpr h1.symm
  rw [hA]; ring

/-- `bandSq` is finite for `L²` tuples. -/
lemma bandSq_ne_top {K : ℕ} (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) : bandSq H ≠ ⊤ := by
  have hterm : ∀ k : Fin K, (∫⁻ x : ℝ, ‖H k x‖ₑ ^ (2:ℝ)) ≠ ⊤ := by
    intro k
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := (volume : Measure ℝ))
      (f := H k) (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) (hH k).aestronglyMeasurable).mp (hH k).eLpNorm_lt_top
    simpa using h.ne
  rw [bandSq_eq_sum_L2 H hH]
  exact ENNReal.sum_ne_top.mpr (fun k _ => hterm k)

/-- The `j`-integrand of `bandMax` is a.e.-measurable in `x`. -/
lemma aemeasurable_bandScaleOpJ {K : ℕ} (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hHm : ∀ k : Fin K, Measurable (H k))
    (hH1 : ∀ k : Fin K, Integrable (H k)) :
    AEMeasurable (fun x : ℝ => (⨆ j : ℕ, ‖bandScaleOpJ Ψ lam H j x‖ₑ) ^ (2:ℝ))
      (volume : Measure ℝ) := by
  have hinner : ∀ j : ℕ, AEMeasurable (fun x : ℝ => ‖bandScaleOpJ Ψ lam H j x‖ₑ)
      (volume : Measure ℝ) := by
    intro j
    refine AEMeasurable.enorm ?_
    refine Finset.aemeasurable_fun_sum Finset.univ (fun k _ => ?_)
    have hconv : AEMeasurable (fun x : ℝ => ∫ v : ℝ, H k v * winK Ψ j (x - v)) volume := by
      refine (BourgainFatou.measurable_parametric_integral
        (K := fun p : ℝ × ℝ => winK Ψ j (p.1 - p.2))
        (((continuous_const.mul (Ψ.continuous.comp
          (by fun_prop : Continuous fun u : ℝ => winScale j * u))).measurable).comp
            (measurable_fst.sub measurable_snd))
        (hHm k) (fun z => integrable_mul_winK Ψ (hH1 k) j z)).aemeasurable
    have hph : Measurable (fun x : ℝ => Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ)))) :=
      (Complex.continuous_exp.comp (by fun_prop)).measurable
    exact hph.aemeasurable.mul hconv
  exact (AEMeasurable.iSup hinner).pow_const 2

/-- **The crux on the admissible class.**  For `1`-separated `lam` and `H` band-limited to
`[-a,a]` (with `0 < a` and `2(2πa·9/10)² < 1`), `bandMax` is bounded by
`log⁴(K+2) · bandSq`. -/
theorem bandMax_le_log (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {a : ℝ} (ha : 0 < a)
    (hth : 2 * (2 * Real.pi * a * (9/10))^2 < 1) :
    ∃ C : ℝ, 0 < C ∧
      C ≤ 2 * (2 * ((90 * ESU.cChain)^2 * (2 * (ESU.cCurve Ψ + 1)
              + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2)) / (9/10))
          / (1 - 2 * (2 * Real.pi * a * (9/10))^2) + 1 ∧
      ∀ (H : Fin K → ℝ → ℂ), Adm a H → bandMax Ψ lam H ≤ ENNReal.ofReal C * bandSq H := by
  obtain ⟨A₀, hA₀pos, hA₀le, hA₀⟩ := lintegral_bandMax_transl_le Ψ lam hsep
  obtain ⟨CK, hCKpos, hCK⟩ := bandMax_apriori Ψ lam
  set δ : ℝ := 9/10 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; norm_num
  set A₁ : ℝ := 2 * A₀ / δ with hA₁def
  have hA₁pos : 0 < A₁ := by rw [hA₁def]; positivity
  -- the selection of the good shift
  have hgood : ∀ (H : Fin K → ℝ → ℂ), Adm a H → ∃ y : ℝ, |y| ≤ δ ∧
      bandMax Ψ lam (transl H y) ≤ ENNReal.ofReal A₁ * bandSq H := by
    intro H hH
    by_cases hb0 : bandSq H = 0
    · refine ⟨1/2, by rw [hδdef, abs_of_pos (by norm_num)]; norm_num, ?_⟩
      have hbs : bandSq (transl H (1/2)) = 0 := by rw [bandSq_transl, hb0]
      have h := hCK (transl H (1/2)) (fun k => (hH.1 k).comp_measurePreserving
        (measurePreserving_add_right volume (1/2)))
      rw [hbs, mul_zero] at h
      rw [hb0, mul_zero]
      exact h
    · by_contra hcon
      have hcon' : ∀ y : ℝ, |y| ≤ δ →
          ENNReal.ofReal A₁ * bandSq H < bandMax Ψ lam (transl H y) := by
        intro y hy
        by_contra hle
        exact hcon ⟨y, hy, le_of_not_gt hle⟩
      have hb : ∫⁻ y in Set.Ioc (0:ℝ) 1, bandMax Ψ lam (transl H y)
          ≤ ENNReal.ofReal A₀ * bandSq H := hA₀ H hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1
      have hlt : ∀ y ∈ Set.Ioc (0:ℝ) δ,
          ENNReal.ofReal A₁ * bandSq H < bandMax Ψ lam (transl H y) := by
        intro y hy
        have h1 : |y| ≤ δ := by rw [abs_of_pos hy.1]; exact hy.2
        exact hcon' y h1
      have h2 : (∫⁻ y in Set.Ioc (0:ℝ) δ, ENNReal.ofReal A₁ * bandSq H)
          ≤ ∫⁻ y in Set.Ioc (0:ℝ) δ, bandMax Ψ lam (transl H y) :=
        setLIntegral_mono' measurableSet_Ioc (fun y hy => (hlt y hy).le)
      have h3 : (∫⁻ y in Set.Ioc (0:ℝ) δ, bandMax Ψ lam (transl H y))
          ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, bandMax Ψ lam (transl H y) :=
        lintegral_mono_set (fun y hy => ⟨hy.1, by rw [hδdef] at hy; linarith [hy.2]⟩)
      have h4 : (∫⁻ y in Set.Ioc (0:ℝ) δ, ENNReal.ofReal A₁ * bandSq H)
          = ENNReal.ofReal (2 * A₀) * bandSq H := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
        have hA : ENNReal.ofReal A₁ * bandSq H * ENNReal.ofReal δ
            = (ENNReal.ofReal A₁ * ENNReal.ofReal δ) * bandSq H := by ring
        rw [hA, ← ENNReal.ofReal_mul (le_of_lt hA₁pos)]
        congr 1
        rw [hA₁def]
        field_simp
      rw [h4] at h2
      have h5 : ENNReal.ofReal (2 * A₀) * bandSq H ≤ ENNReal.ofReal A₀ * bandSq H :=
        le_trans h2 (le_trans h3 hb)
      have hbst : bandSq H ≠ ⊤ := bandSq_ne_top H hH.1
      have h6 := (ENNReal.mul_le_mul_iff_left hb0 hbst).mp h5
      rw [ENNReal.ofReal_le_ofReal_iff (le_of_lt hA₀pos)] at h6
      linarith [hA₀pos, h6]
  -- the contraction
  have hcon : ∀ (H : Fin K → ℝ → ℂ), Adm a H → ∀ y, |y| ≤ δ →
      bandSq (fun k u => H k u - H k (u + y))
        ≤ ENNReal.ofReal ((2 * Real.pi * a * δ)^2) * bandSq H := by
    intro H hH y hy
    have hdiff : ∀ k : Fin K,
        MemLp (fun u : ℝ => H k (u + y) - H k u) 2 (volume : Measure ℝ) := fun k =>
      ((hH.1 k).comp_measurePreserving (measurePreserving_add_right volume y)).sub (hH.1 k)
    have hsum : bandSq (fun k u => H k u - H k (u + y))
        ≤ ∑ k : Fin K, ∫⁻ x : ℝ, ‖H k (x + y) - H k x‖ₑ ^ (2:ℝ) := by
      rw [← bandSq_eq_sum_L2 (fun k u => H k (u + y) - H k u) hdiff]
      unfold bandSq
      refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
      exact Finset.sum_le_sum (fun k _ => by rw [norm_sub_rev])
    have hterm : ∀ k : Fin K, (∫⁻ x : ℝ, ‖H k (x + y) - H k x‖ₑ ^ (2:ℝ))
        ≤ ENNReal.ofReal ((2 * Real.pi * a * δ)^2) * ∫⁻ x : ℝ, ‖H k x‖ₑ ^ (2:ℝ) := by
      intro k
      refine le_trans (lintegral_translate_sub_sq_le_of_fourier_support (hH.2.2.2.1 k)
        (hH.1 k) (le_of_lt ha) (hH.2.2.2.2 k)) ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have h2 : 2 * Real.pi * a * |y| ≤ 2 * Real.pi * a * δ := by
        have h3 : 0 ≤ 2 * Real.pi * a := by positivity
        exact mul_le_mul_of_nonneg_left hy h3
      exact pow_le_pow_left₀ (mul_nonneg (by positivity) (abs_nonneg y)) h2 2
    refine le_trans hsum ?_
    refine le_trans (Finset.sum_le_sum (fun k _ => hterm k)) (le_of_eq ?_)
    rw [← Finset.mul_sum]
    congr 1
    exact (bandSq_eq_sum_L2 H hH.1).symm
  -- the subadditivity and the a priori bound
  have hsub : ∀ (H : Fin K → ℝ → ℂ), Adm a H → ∀ y, |y| ≤ δ → bandMax Ψ lam H
      ≤ 2 * bandMax Ψ lam (transl H y)
        + 2 * bandMax Ψ lam (fun k u => H k u - H k (u + y)) := by
    intro H hH y hy
    refine bandMax_subadd Ψ lam H y hH.2.2.2.1 hH.1 ?_
    have htr : ∀ k : Fin K, Measurable (fun u : ℝ => H k (u + y)) := fun k =>
      (hH.2.2.1 k).comp (by fun_prop)
    exact aemeasurable_bandScaleOpJ Ψ lam (transl H y) htr
      (fun k => (hH.2.2.2.1 k).comp_add_right y)
  have hCKpos' : 0 < CK * ↑(K+1) := by
    have h1 : (0:ℝ) < ((K:ℝ) + 1) := by positivity
    positivity
  have happ : ∀ (H : Fin K → ℝ → ℂ), Adm a H →
      bandMax Ψ lam H ≤ ENNReal.ofReal (CK * ↑(K+1)) * bandSq H := by
    intro H hH
    refine le_trans (hCK H hH.1) ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hle : (K:ℝ) ≤ (K:ℝ) + 1 := by linarith
    push_cast
    exact mul_le_mul_of_nonneg_left hle hCKpos.le
  -- the constant of the conclusion
  set D : ℝ := 2 * A₁ / (1 - 2 * (2 * Real.pi * a * δ)^2) + 1 with hDdef
  have hden : 0 < 1 - 2 * (2 * Real.pi * a * δ)^2 := by
    rw [hδdef] at hth ⊢
    linarith
  have hDpos : 0 < D := by rw [hDdef]; positivity
  refine ⟨D, hDpos, ?_, fun H hH => ?_⟩
  · have hden' : 0 < 1 - 2 * (2 * Real.pi * a * (9/10))^2 := by rw [hδdef] at hden; exact hden
    have hA₁le : A₁ ≤ 2 * ((90 * ESU.cChain)^2 * (2 * (ESU.cCurve Ψ + 1)
          + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2)) / (9/10) := by
      rw [hA₁def, hδdef]
      linarith [hA₀le]
    have h2 : 2 * A₁ / (1 - 2 * (2 * Real.pi * a * (9/10))^2)
        ≤ 2 * (2 * ((90 * ESU.cChain)^2 * (2 * (ESU.cCurve Ψ + 1)
            + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2)) / (9/10))
            / (1 - 2 * (2 * Real.pi * a * (9/10))^2) := by
      apply div_le_div_of_nonneg_right _ hden'.le
      linarith [hA₁le]
    calc D = 2 * A₁ / (1 - 2 * (2 * Real.pi * a * (9/10))^2) + 1 := by rw [hDdef, hδdef]
      _ ≤ 2 * (2 * ((90 * ESU.cChain)^2 * (2 * (ESU.cCurve Ψ + 1)
            + 2 * (ESU.cEnt Ψ * (Real.log ((K:ℝ)+2))^2)^2)) / (9/10))
            / (1 - 2 * (2 * Real.pi * a * (9/10))^2) + 1 := by linarith
  · have h := bandMax_le_of_good_shift (A := A₁) (θ := 2 * Real.pi * a * δ)
      (CK := CK * ↑(K+1)) (δ := δ) (δ' := 1) Ψ lam hA₁pos
      (by positivity) hth
      (le_of_lt hCKpos') (by norm_num) (Adm a)
      (fun H hH y hy => ⟨
        fun k => (hH.1 k).sub ((hH.1 k).comp_measurePreserving
          (measurePreserving_add_right volume y)),
        fun k => (hH.2.1 k).sub ((hH.2.1 k).comp_measurePreserving
          (measurePreserving_add_right volume y)),
        fun k => (hH.2.2.1 k).sub ((hH.2.2.1 k).comp (by fun_prop)),
        fun k => (hH.2.2.2.1 k).sub ((hH.2.2.2.1 k).comp_add_right y),
        fun k ξ hξ => by
          rw [fourier_sub_translate (H k) (hH.2.2.2.1 k) y]
          simp [hH.2.2.2.2 k ξ hξ]⟩)
      hgood hcon hsub happ H hH
    exact h
end
end FWS

-- ==== inlined from Submission/Work/Analysis/ExponentialSums/qkmWall/LastMile.lean ====

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FWS
namespace LastMile

open OldSWM.BourgainMax OldSWM.BourgainAssembly OldSWM.BandDecomp OldSWM.BourgainFatou
open OldSWM Commons.Analysis.Fourier
open _root_.MeasureTheory _root_.Finset
open scoped BigOperators ENNReal Topology FourierTransform ContDiff

noncomputable section

/-- The commons `innerSmooth` kernel is the sum of the `BandDecomp.bandTerm` kernels. -/
theorem innerSmooth_eq_sum_bandTerm (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (x y : ℝ) :
    SepWin.innerSmooth φ K lam j (x - y)
      = ∑ k : Fin K, BandDecomp.bandTerm φ (lam k) (winScale j) x y := by
  unfold SepWin.innerSmooth BandDecomp.bandTerm
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [show SepWin.hJ j = winScale j from rfl]

lemma winScale_le_half (j : ℕ) : winScale j ≤ 1/2 := by
  unfold winScale
  calc (2:ℝ) ^ (-(j:ℝ) - 1) ≤ (2:ℝ) ^ (-(1:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg _
        linarith
    _ = 1/2 := by rw [Real.rpow_neg_one]; norm_num

/-- The modulated slice tuple: `H k = sliceOf f (λ_k) · e^{I λ_k ·}`. -/
noncomputable def sliceTuple {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ) : Fin K → ℝ → ℂ :=
  fun k y => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))

/-- **The pointwise identity**: the commons smooth-window operator on `f` is the framework's
`bandScaleOpJ` on the modulated slice tuple. -/
theorem smoothOp_eq_bandScaleOpJ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hbd : ∀ x : ℝ, ‖φ x‖ ≤ 1) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    (K : ℕ) (lam : Fin K → ℝ) {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (j : ℕ) (x : ℝ) :
    SepWin.smoothOp φ K lam f j x
      = BourgainMax.bandScaleOpJ (BandDecomp.winPsi φ hφ hsupp) lam
          (sliceTuple f lam) j x := by
  have h1 : SepWin.smoothOp φ K lam f j x
      = ∫ y, f y * (∑ k : Fin K, BandDecomp.bandTerm φ (lam k) (winScale j) x y) := by
    unfold SepWin.smoothOp
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [innerSmooth_eq_sum_bandTerm φ K lam j x y]
  rw [h1, bandSum_slice_windowed K φ hφ hbd hsupp lam (winScale_pos j) (winScale_le_half j)
    hf1 hf2 x]
  simp only [sliceTuple, BourgainMax.bandScaleOpJ, BourgainMax.winK]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [BandDecomp.winPsi_coe φ hφ hsupp]
  ring

/-- **Modulation.**  The Fourier transform of `g · e^{I λ ·}` is the shifted transform of `g`. -/
theorem fourier_mul_exp_I (g : ℝ → ℂ) (lam : ℝ) :
    𝓕 (fun y : ℝ => g y * Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ)))
      = fun ξ : ℝ => 𝓕 g (ξ - lam / (2 * Real.pi)) := by
  funext ξ
  have h2pi : (2:ℝ) * Real.pi ≠ 0 := by positivity
  rw [Real.fourier_eq', Real.fourier_eq']
  refine integral_congr_ae (ae_of_all _ (fun v => ?_))
  dsimp only
  rw [smul_eq_mul, smul_eq_mul, Real.inner_apply, Real.inner_apply]
  rw [show Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) *
        (g v * Complex.exp (Complex.I * (lam : ℂ) * (v : ℂ)))
      = (Complex.exp (↑(-2 * Real.pi * (v * ξ)) * Complex.I) *
          Complex.exp (Complex.I * (lam : ℂ) * (v : ℂ))) * g v by ring]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-! ## The band-limit of the modulated slices -/

lemma bddAbove_sliceKernel (lam : ℝ) :
    BddAbove (Set.range (fun x : ℝ => ‖(sliceKernel lam : ℝ → ℂ) x‖)) := by
  obtain ⟨C, _, hC⟩ := (sliceKernel lam).decay 0 0
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  simpa using hC x

/-- The slice of `f` at `lam` is continuous (as soon as `f` is integrable). -/
theorem continuous_sliceOf {f : ℝ → ℂ} (hf : Integrable f) (lam : ℝ) :
    Continuous (sliceOf f lam) := by
  rw [sliceOf_eq_convolution]
  exact BddAbove.continuous_convolution_left_of_integrable (L := ContinuousLinearMap.lsmul ℂ ℂ)
    (bddAbove_sliceKernel lam) (sliceKernel lam).continuous hf

/-- A uniform bound for the slice of a bounded integrable function. -/
theorem ae_norm_sliceOf_le {f : ℝ → ℂ} {C : ℝ} (hf : Integrable f) (hfC : ∀ y, ‖f y‖ ≤ C)
    (lam : ℝ) :
    ∀ᵐ x : ℝ, ‖sliceOf f lam x‖ ≤ C * ∫ y, ‖(sliceKernel lam : ℝ → ℂ) y‖ := by
  have hκ : Integrable (fun y : ℝ => (sliceKernel lam : ℝ → ℂ) y) := (sliceKernel lam).integrable
  have hκn : Integrable (fun y : ℝ => ‖(sliceKernel lam : ℝ → ℂ) y‖) := hκ.norm
  filter_upwards with x
  have hshift_asm : AEStronglyMeasurable (fun y : ℝ => f (x - y)) volume :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      ((volume : Measure ℝ).measurePreserving_sub_left x).quasiMeasurePreserving
  have hshift_norm : AEStronglyMeasurable (fun y : ℝ => ‖f (x - y)‖) volume := hshift_asm.norm
  have hInt : Integrable (fun y : ℝ => (sliceKernel lam : ℝ → ℂ) y * f (x - y)) :=
    hκ.mul_bdd hshift_asm (ae_of_all _ (fun y : ℝ => hfC (x - y)))
  have hInt2 : Integrable (fun y : ℝ => ‖(sliceKernel lam : ℝ → ℂ) y‖ * ‖f (x - y)‖) :=
    hκn.mul_bdd hshift_norm (ae_of_all _ (fun y : ℝ => by simpa using hfC (x - y)))
  calc ‖sliceOf f lam x‖
      = ‖∫ y, (sliceKernel lam : ℝ → ℂ) y * f (x - y)‖ := rfl
    _ ≤ ∫ y, ‖(sliceKernel lam : ℝ → ℂ) y * f (x - y)‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖(sliceKernel lam : ℝ → ℂ) y‖ * ‖f (x - y)‖ := by
        simp_rw [norm_mul]
    _ ≤ ∫ y, ‖(sliceKernel lam : ℝ → ℂ) y‖ * C := by
        refine integral_mono_ae hInt2 (hκn.mul_const C)
          (ae_of_all _ (fun y => mul_le_mul_of_nonneg_left (hfC (x - y)) (norm_nonneg _)))
    _ = (∫ y, ‖(sliceKernel lam : ℝ → ℂ) y‖) * C := integral_mul_const _ _
    _ = C * ∫ y, ‖(sliceKernel lam : ℝ → ℂ) y‖ := by ring

/-- The exponential factor is unimodular. -/
lemma norm_exp_I_mul (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [show Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))
      = Complex.exp (((lam * y : ℝ)) * Complex.I) by congr 1; push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The Fourier transform of a modulated slice. -/
theorem fourier_slice_modulated {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ) (hf : Integrable f)
    (k : Fin K) (ξ : ℝ) :
    𝓕 (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) ξ
      = (sliceFun (lam k) (ξ - lam k / (2 * Real.pi)) : ℂ) * 𝓕 f (ξ - lam k / (2 * Real.pi)) := by
  rw [fourier_mul_exp_I]
  simp only [BourgainAssembly.sliceOf_fourier hf (lam k)]

theorem fourier_slice_modulated_zero {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ) (hf : Integrable f)
    (k : Fin K) {ξ : ℝ} (hξ : 3 / (8 * Real.pi) < |ξ|) :
    𝓕 (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) ξ = 0 := by
  rw [fourier_slice_modulated f lam hf k ξ]
  have hzero : sliceFun (lam k) (ξ - lam k / (2 * Real.pi)) = 0 := by
    refine sliceFun_zero_of_abs ?_
    have harg : 4 * Real.pi * (ξ - lam k / (2 * Real.pi)) + 2 * lam k = 4 * Real.pi * ξ := by
      field_simp
      ring
    rw [harg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.pi)]
    have h2 : 4 * Real.pi * (3 / (8 * Real.pi)) < 4 * Real.pi * |ξ| :=
      mul_lt_mul_of_pos_left hξ (by positivity)
    have h3 : 4 * Real.pi * (3 / (8 * Real.pi)) = 3 / 2 := by field_simp; ring
    rw [h3] at h2
    linarith
  rw [hzero, Complex.ofReal_zero, zero_mul]

/-! ## The admissible-class verification -/

theorem sliceTuple_memLp_two {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (k : Fin K) :
    MemLp (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)))
      2 (volume : Measure ℝ) := by
  have hg := BourgainAssembly.sliceOf_memLp hf (lam k)
  refine (memLp_congr_norm hg.aestronglyMeasurable ?_
    (ae_of_all _ (fun y => ?_))).mp hg
  · exact hg.aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
  · rw [norm_mul, norm_exp_I_mul (lam k) y, mul_one]

theorem sliceTuple_memLp_top {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ) {C : ℝ}
    (hf : Integrable f) (hfC : ∀ y, ‖f y‖ ≤ C) (k : Fin K) :
    MemLp (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)))
      ⊤ (volume : Measure ℝ) := by
  have hb := ae_norm_sliceOf_le hf hfC (lam k)
  have hbd : ∀ᵐ y : ℝ,
      ‖sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖
        ≤ C * ∫ z, ‖(sliceKernel (lam k) : ℝ → ℂ) z‖ := by
    filter_upwards [hb] with y hy
    rw [norm_mul, norm_exp_I_mul (lam k) y, mul_one]
    exact hy
  have hasm : AEStronglyMeasurable
      (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) volume :=
    ((continuous_sliceOf hf (lam k)).mul (Complex.continuous_exp.comp (by fun_prop)))
      |>.aestronglyMeasurable
  exact memLp_top_of_bound hasm _ hbd

theorem sliceTuple_measurable {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ)
    (hf : Integrable f) (k : Fin K) :
    Measurable (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) :=
  (continuous_sliceOf hf (lam k)).measurable.mul
    (Complex.continuous_exp.comp (by fun_prop)).measurable

theorem sliceTuple_integrable {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ)
    (hf : Integrable f) (k : Fin K) :
    Integrable (fun y : ℝ => sliceOf f (lam k) y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))) :=
  (BourgainAssembly.sliceOf_integrable hf (lam k)).mul_bdd
    ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ (fun y => by rw [norm_exp_I_mul]))

/-- **The admissible-class verification**: for a bounded integrable `L²` function `f`, the modulated
slice tuple is admissible with band limit `3/(8π)`. -/
theorem sliceTuple_adm {K : ℕ} (f : ℝ → ℂ) (lam : Fin K → ℝ) {C : ℝ}
    (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hfC : ∀ y, ‖f y‖ ≤ C) :
    Adm (3 / (8 * Real.pi)) (sliceTuple f lam) := by
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  exact ⟨fun k => sliceTuple_memLp_two f lam hf2 k,
    fun k => sliceTuple_memLp_top f lam hfi hfC k,
    fun k => sliceTuple_measurable f lam hfi k,
    fun k => sliceTuple_integrable f lam hfi k,
    fun k ξ hξ => fourier_slice_modulated_zero f lam hfi k hξ⟩

/-! ## The frozen window and the constant -/

lemma bump_contDiff_smooth : ContDiff ℝ ∞ SepWin.bump :=
  BandDecomp.contDiff_infty_of_forall_nat SepWin.bump_contDiff

/-- The frozen smooth window of the target: `Ψ = 𝓕(2π · bump(2π ·))`. -/
noncomputable def bPsi : SchwartzMap ℝ ℂ :=
  BandDecomp.winPsi SepWin.bump bump_contDiff_smooth SepWin.bump_zero

lemma bPsi_coe (w : ℝ) : bPsi w = BandDecomp.hat SepWin.bump w :=
  BandDecomp.winPsi_coe _ _ _ w

/-- The `L⁴`-free part of the bound for the averaged constant. -/
noncomputable def bY0 : ℝ :=
  (90 * ESU.cChain)^2 * (2 * (ESU.cCurve bPsi + 1) + 2 * ESU.cEnt bPsi^2)

/-- The `K`-dependent averaged bound (with the explicit `(log (K+2))⁴`). -/
noncomputable def bY (K : ℕ) : ℝ :=
  (90 * ESU.cChain)^2 * (2 * (ESU.cCurve bPsi + 1)
    + 2 * (ESU.cEnt bPsi * (Real.log ((K:ℝ)+2))^2)^2)

/-- The (`L⁴`-free) constant appearing under the square root. -/
noncomputable def bLam : ℝ := (64000 / 639) * bY0 / (Real.log 2)^4 + 2 / (Real.log 2)^4

/-- The uniform constant of the fixed-bump smooth-window maximal estimate. -/
noncomputable def bCA : ℝ := Real.sqrt bLam + 1

lemma log2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

lemma log2_pow4_le_one : (Real.log 2)^4 ≤ 1 := by
  have h1 : Real.log 2 ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    linarith
  have h0 : 0 ≤ Real.log 2 := le_of_lt log2_pos
  calc (Real.log 2)^4 ≤ 1^4 := pow_le_pow_left₀ h0 h1 4
    _ = 1 := by norm_num

lemma bCA_pos : 0 < bCA := by
  unfold bCA; positivity

lemma bY0_nonneg : 0 ≤ bY0 := by
  unfold bY0
  refine mul_nonneg (sq_nonneg _) ?_
  have hcc : 0 ≤ ESU.cCurve bPsi + 1 := by have := ESU.cCurve_pos bPsi; linarith
  have he : 0 ≤ ESU.cEnt bPsi ^ 2 := sq_nonneg _
  linarith

lemma bLam_nonneg : 0 ≤ bLam := by
  unfold bLam
  have h1 : 0 ≤ bY0 := bY0_nonneg
  have h2 : (0:ℝ) < (Real.log 2)^4 := by positivity
  positivity

lemma bLam_le_bCA_sq : bLam ≤ bCA^2 := by
  have h1 : Real.sqrt bLam ≤ bCA := by unfold bCA; linarith
  have h2 : 0 ≤ Real.sqrt bLam := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt bLam_nonneg, h1, h2]

lemma logK_ge_log2 (K : ℕ) : Real.log 2 ≤ Real.log ((K:ℝ) + 2) :=
  Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg K : (0:ℝ) ≤ (K:ℝ))])

lemma bY_le (K : ℕ) :
    bY K ≤ bY0 * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4) := by
  have hL : 0 < Real.log ((K:ℝ)+2) := lt_of_lt_of_le log2_pos (logK_ge_log2 K)
  have h2 : 0 < (Real.log 2)^4 := by positivity
  have hL4 : (Real.log 2)^4 ≤ (Real.log ((K:ℝ)+2))^4 := by
    have h4 := logK_ge_log2 K
    exact pow_le_pow_left₀ (le_of_lt log2_pos) h4 4
  have hM : 1 ≤ (Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4 := by
    rw [le_div_iff₀ h2]; linarith
  have hcc : 0 ≤ ESU.cCurve bPsi + 1 := by have := ESU.cCurve_pos bPsi; linarith
  have he : 0 ≤ ESU.cEnt bPsi := le_of_lt (ESU.cEnt_pos bPsi)
  have he2 : 0 ≤ ESU.cEnt bPsi^2 := sq_nonneg _
  have hc : 0 ≤ (90 * ESU.cChain)^2 := sq_nonneg _
  have hL4' : (ESU.cEnt bPsi * (Real.log ((K:ℝ)+2))^2)^2
      = ESU.cEnt bPsi^2 * (Real.log ((K:ℝ)+2))^4 := by ring
  rw [bY, bY0, hL4']
  have hstep : 2 * (ESU.cCurve bPsi + 1) + 2 * (ESU.cEnt bPsi^2 * (Real.log ((K:ℝ)+2))^4)
      ≤ (2 * (ESU.cCurve bPsi + 1) + 2 * ESU.cEnt bPsi^2)
        * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4) := by
    rw [add_mul]
    have h1 : 2 * (ESU.cCurve bPsi + 1)
        ≤ 2 * (ESU.cCurve bPsi + 1) * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4) := by
      nlinarith [hM, hcc]
    have h3 : 2 * (ESU.cEnt bPsi^2 * (Real.log ((K:ℝ)+2))^4)
        ≤ 2 * ESU.cEnt bPsi^2 * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4) := by
      have hle4 : (Real.log 2)^4 ≤ 1 := log2_pow4_le_one
      have hpos4 : 0 ≤ (Real.log ((K:ℝ)+2))^4 := pow_nonneg (le_of_lt hL) 4
      have hdiv : (Real.log ((K:ℝ)+2))^4 ≤ (Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4 := by
        rw [le_div_iff₀ h2]
        calc (Real.log ((K:ℝ)+2))^4 * (Real.log 2)^4
            ≤ (Real.log ((K:ℝ)+2))^4 * 1 := mul_le_mul_of_nonneg_left hle4 hpos4
          _ = (Real.log ((K:ℝ)+2))^4 := by ring
      nlinarith [hdiv, he2]
    linarith
  calc (90 * ESU.cChain)^2
        * (2 * (ESU.cCurve bPsi + 1) + 2 * (ESU.cEnt bPsi^2 * (Real.log ((K:ℝ)+2))^4))
      ≤ (90 * ESU.cChain)^2 * ((2 * (ESU.cCurve bPsi + 1) + 2 * ESU.cEnt bPsi^2)
          * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4)) :=
        mul_le_mul_of_nonneg_left hstep hc
    _ = (90 * ESU.cChain)^2 * (2 * (ESU.cCurve bPsi + 1) + 2 * ESU.cEnt bPsi^2)
          * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4) := by ring

/-- **The arithmetic of the constant.**  `bandMax_le_log`'s explicit bound (an expression in
`Y = bY K`) implies the final estimate with the uniform constant `bCA`. -/
lemma two_mul_bound (K : ℕ) {D : ℝ}
    (hDle : D ≤ 2 * (2 * bY K / (9/10)) / (1 - 2 * (27/40)^2) + 1) :
    2 * D ≤ (bCA * (Real.log ((K:ℝ)+2))^2)^2 := by
  have hL : 0 < Real.log ((K:ℝ)+2) := lt_of_lt_of_le log2_pos (logK_ge_log2 K)
  have h2 : 0 < (Real.log 2)^4 := by positivity
  have hY0 : 0 ≤ bY0 := bY0_nonneg
  have hL4nn : 0 ≤ (Real.log ((K:ℝ)+2))^4 := pow_nonneg (le_of_lt hL) 4
  have hD1 : D ≤ (32000 / 639) * bY K + 1 := by
    have h1 : 2 * (2 * bY K / (9/10)) / (1 - 2 * (27/40)^2) + 1
        = (32000 / 639) * bY K + 1 := by
      field_simp
      ring
    linarith [h1 ▸ hDle]
  have hY : bY K ≤ bY0 * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4) := bY_le K
  have hM : (1:ℝ) ≤ (Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4 := by
    rw [le_div_iff₀ h2, one_mul]
    exact pow_le_pow_left₀ (le_of_lt log2_pos) (logK_ge_log2 K) 4
  have hB : (1:ℝ) ≤ (1 / (Real.log 2)^4) * (Real.log ((K:ℝ)+2))^4 := by
    have heq : (1 / (Real.log 2)^4) * (Real.log ((K:ℝ)+2))^4
        = (Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4 := by
      rw [div_mul_eq_mul_div, one_mul]
    rw [heq]; exact hM
  have hstep : (32000 / 639) * bY K + 1 ≤ bLam / 2 * (Real.log ((K:ℝ)+2))^4 := by
    have hA : (32000 / 639) * bY K
        ≤ (32000 / 639) * bY0 / (Real.log 2)^4 * (Real.log ((K:ℝ)+2))^4 := by
      calc (32000 / 639) * bY K
          ≤ (32000 / 639) * (bY0 * ((Real.log ((K:ℝ)+2))^4 / (Real.log 2)^4)) :=
            mul_le_mul_of_nonneg_left hY (by norm_num)
        _ = (32000 / 639) * bY0 / (Real.log 2)^4 * (Real.log ((K:ℝ)+2))^4 := by
            field_simp
    have hsum : ((64000 / 639) * bY0 / (Real.log 2)^4 + 2 / (Real.log 2)^4) / 2
          * (Real.log ((K:ℝ)+2))^4
        = (32000 / 639) * bY0 / (Real.log 2)^4 * (Real.log ((K:ℝ)+2))^4
          + (1 / (Real.log 2)^4) * (Real.log ((K:ℝ)+2))^4 := by
      have hden : (Real.log 2)^4 ≠ 0 := ne_of_gt h2
      field_simp
      ring
    rw [bLam, hsum]
    linarith [hA, hB]
  have h2D : 2 * D ≤ bLam * (Real.log ((K:ℝ)+2))^4 := by linarith [hD1, hstep]
  calc 2 * D ≤ bLam * (Real.log ((K:ℝ)+2))^4 := h2D
    _ ≤ bCA^2 * (Real.log ((K:ℝ)+2))^4 :=
        mul_le_mul_of_nonneg_right bLam_le_bCA_sq hL4nn
    _ = (bCA * (Real.log ((K:ℝ)+2))^2)^2 := by ring

/-! ## The bounded case and the Fatou step -/

open BourgainFatou in
theorem memLp_trunc_one {f : ℝ → ℂ} (hfmeas : Measurable f) (n : ℕ) :
    MemLp (BourgainFatou.trunc f n) 1 (volume : Measure ℝ) := by
  have hg : MemLp (fun y : ℝ => (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y)
      1 (volume : Measure ℝ) := by
    refine MemLp.const_mul ?_ _
    exact memLp_indicator_const 1 measurableSet_Icc (1:ℝ)
      (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  refine hg.mono' ?_ ?_
  · exact (BourgainFatou.trunc_measurable hfmeas n).aestronglyMeasurable
  · filter_upwards with y
    rw [BourgainFatou.trunc]
    split_ifs with h
    · rw [Set.indicator_of_mem, mul_one]
      · exact h.1
      · rw [Set.mem_Icc]
        exact ⟨by linarith [(abs_le.mp h.2).1], (abs_le.mp h.2).2⟩
    · rw [norm_zero]
      refine mul_nonneg (Nat.cast_nonneg n) ?_
      by_cases hy : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ)
      · rw [Set.indicator_of_mem hy]; norm_num
      · rw [Set.indicator_of_notMem hy]

theorem memLp_trunc_two {f : ℝ → ℂ} (hfmeas : Measurable f) (n : ℕ)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (BourgainFatou.trunc f n) 2 (volume : Measure ℝ) := by
  refine hf2.of_le ((BourgainFatou.trunc_measurable hfmeas n).aestronglyMeasurable) ?_
  filter_upwards with y
  exact BourgainFatou.norm_trunc_le f n y

theorem trunc_bound (f : ℝ → ℂ) (n : ℕ) (y : ℝ) : ‖BourgainFatou.trunc f n y‖ ≤ (n:ℝ) := by
  rw [BourgainFatou.trunc]
  split_ifs with h
  · exact h.1
  · simp

theorem trunc_le (f : ℝ → ℂ) (n : ℕ) : ∀ y, ‖BourgainFatou.trunc f n y‖ ≤ ‖f y‖ :=
  fun y => BourgainFatou.norm_trunc_le f n y

/-- **The fixed-bump estimate for bounded `L¹ ∩ L²` functions.** -/
theorem bump_maximal_of_bounded {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    {C₀ : ℝ} (hfC : ∀ y, ‖f y‖ ≤ C₀) :
    (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
      ≤ ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  have hbd : ∀ x : ℝ, ‖SepWin.bump x‖ ≤ 1 := fun x => by
    obtain ⟨h0, h1⟩ := SepWin.bump_bounds x
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hAdm : Adm (3 / (8 * Real.pi)) (sliceTuple f lam) :=
    sliceTuple_adm f lam hf1 hf2 hfC
  have ha : (0:ℝ) < 3 / (8 * Real.pi) := by positivity
  have aux : 2 * Real.pi * (3 / (8 * Real.pi)) * (9/10) = 27/40 := by field_simp; ring
  have hth : 2 * (2 * Real.pi * (3 / (8 * Real.pi)) * (9/10))^2 < 1 := by
    rw [aux]; norm_num
  obtain ⟨D, hDpos, hDle, hDbd⟩ := bandMax_le_log bPsi lam hsep ha hth
  have hEq : (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
      = bandMax bPsi lam (sliceTuple f lam) := by
    unfold bandMax
    refine lintegral_congr (fun x => ?_)
    congr 1
    exact iSup_congr (fun j => by
      rw [smoothOp_eq_bandScaleOpJ SepWin.bump bump_contDiff_smooth hbd SepWin.bump_zero K lam hf1 hf2 j x]
      simp only [bPsi])
  have hsq : bandSq (sliceTuple f lam) ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    rw [bandSq_eq_sum (sliceTuple f lam) (fun k => hAdm.2.2.1 k)]
    exact slice_energy_le K lam hsep hf1 hf2
  have h2D : 2 * D ≤ (bCA * (Real.log ((K:ℝ)+2))^2)^2 :=
    two_mul_bound K (by simpa only [bY, aux] using hDle)
  have hbound : ENNReal.ofReal D * bandSq (sliceTuple f lam)
      ≤ ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    calc ENNReal.ofReal D * bandSq (sliceTuple f lam)
        ≤ ENNReal.ofReal D * (2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := mul_le_mul_right hsq _
      _ = ENNReal.ofReal (2 * D) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
            rw [show ENNReal.ofReal D * (2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
                = (ENNReal.ofReal D * 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) by ring]
            congr 1
            rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
              ← ENNReal.ofReal_mul (le_of_lt hDpos)]
            ring_nf
      _ ≤ ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal h2D) _
  rw [hEq]
  exact le_trans (hDbd (sliceTuple f lam) hAdm) hbound

/-- **The Fatou step**: it suffices to know the estimate for bounded `L¹ ∩ L²` functions. -/
theorem bump_maximal_of_measurable {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {f : ℝ → ℂ}
    (hfmeas : Measurable f) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
      ≤ ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  have hb : ∀ j : ℕ, Measurable (SepWin.innerSmooth SepWin.bump K lam j) := fun j =>
    SepWin.measurable_innerSmooth SepWin.bump SepWin.bump_measurable SepWin.bump_bounds K lam j
  have hb2 : ∀ j : ℕ, MemLp (SepWin.innerSmooth SepWin.bump K lam j) 2 (volume : Measure ℝ) :=
    fun j => SepWin.memLp_innerSmooth SepWin.bump SepWin.bump_measurable SepWin.bump_bounds K lam j
  have hint : ∀ (j : ℕ) (x : ℝ),
      Integrable (fun y : ℝ => f y * SepWin.innerSmooth SepWin.bump K lam j (x - y)) volume := by
    intro j x
    have h1 : MemLp (fun y : ℝ => SepWin.innerSmooth SepWin.bump K lam j (x - y)) 2 volume :=
      (hb2 j).comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left x)
    have h2 : MemLp (fun y : ℝ => SepWin.innerSmooth SepWin.bump K lam j (x - y) * f y) 1 volume :=
      h1.mul hf2
    have h3 : MemLp (fun y : ℝ => f y * SepWin.innerSmooth SepWin.bump K lam j (x - y)) 1 volume :=
      h2.congr_norm (hf2.aestronglyMeasurable.mul h1.aestronglyMeasurable)
        (ae_of_all _ (fun y => by rw [norm_mul, norm_mul]; exact mul_comm _ _))
    exact memLp_one_iff_integrable.mp h3
  have hFatou := BourgainFatou.lintegral_sup_enorm_le_liminf hfmeas
    (fun j => SepWin.innerSmooth SepWin.bump K lam j) hb hint
  have hstep : ∀ n : ℕ,
      (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, BourgainFatou.trunc f n y
          * SepWin.innerSmooth SepWin.bump K lam j (x - y)‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    intro n
    refine le_trans (bump_maximal_of_bounded lam hsep (memLp_trunc_one hfmeas n)
      (memLp_trunc_two hfmeas n hf2) (trunc_bound f n)) ?_
    refine mul_le_mul_right ?_ _
    refine lintegral_mono (fun x => ?_)
    exact ENNReal.rpow_le_rpow (by
      rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (trunc_le f n x)) (by norm_num)
  calc (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
      = (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y
          * SepWin.innerSmooth SepWin.bump K lam j (x - y)‖ₑ) ^ (2:ℝ)) := rfl
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, BourgainFatou.trunc f n y
          * SepWin.innerSmooth SepWin.bump K lam j (x - y)‖ₑ) ^ (2:ℝ)) Filter.atTop := hFatou
    _ ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hstep)
    _ = ENNReal.ofReal ((bCA * (Real.log ((K:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) :=
        Filter.liminf_const _

/-- **The fixed-bump smooth-window maximal estimate for `L²` functions** (the single remaining
analytic input of the whole reduction). -/
theorem bump_smoothOp_maximal_l2 :
    ∃ CA : ℝ, 0 < CA ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
        (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
          ≤ ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2)
            * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
  refine ⟨bCA, bCA_pos, fun K lam hsep f hf => ?_⟩
  set g : ℝ → ℂ := hf.aemeasurable.mk f with hgdef
  have hgmeas : Measurable g := hf.aemeasurable.measurable_mk
  have hgeq : f =ᵐ[volume] g := hf.aemeasurable.ae_eq_mk
  have hg2 : MemLp g 2 (volume : Measure ℝ) := hf.ae_eq hgeq
  have hmain := bump_maximal_of_measurable lam hsep hgmeas hg2
  have hinner : ∀ (j : ℕ) (x : ℝ),
      SepWin.smoothOp SepWin.bump K lam g j x = SepWin.smoothOp SepWin.bump K lam f j x := by
    intro j x
    unfold SepWin.smoothOp
    refine integral_congr_ae ?_
    filter_upwards [hgeq] with y hy
    rw [hy]
  have hEq : (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam g j x‖ₑ) ^ (2:ℝ))
      = (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ)) := by
    refine lintegral_congr (fun x => ?_)
    congr 1
    exact iSup_congr (fun j => by rw [hinner j x])
  have hEqf : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ)) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgeq] with x hx
    rw [hx]
  rw [← hEq, ← hEqf]
  exact hmain

end
end LastMile
end FWS


namespace Commons.Analysis.ExponentialSums

theorem quadratic_kernel_model_maximal_l2 :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  exact quadratic_kernel_model_maximal_l2_of_fixed_bump FWS.LastMile.bump_smoothOp_maximal_l2

end Commons.Analysis.ExponentialSums
