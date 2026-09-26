/-
# The second-order cusp expansion of `𝓛 - πiτ`

For any CKMRV logarithm data `(𝓛, 𝓛_S)` (Section 2.1.5) the function `𝓛 - πiτ` has a
limit at the cusp, with an explicit second-order asymptotic expansion in the cusp
parameter `E = e^{πiτ}`:

  `𝓛(τ) = πiτ + c - 8E + 12E² + O(‖E‖³)`.

This is the statement `cusp_L_second` needed for the Fourier interpolation argument.

The proof splits into three independent parts:

* `ll_sub_Lfun_const`: every logarithm data `𝓛` differs from the explicit branch
  `Lfun = LU` by a constant (both are logarithms of the modular `λ` and `ℍ` is
  connected);
* `Lfun_second_order`: `Lfun τ - πiτ - 4 log 2 + 8E - 12E² = O(‖E‖³)`, obtained from
  `LU = πiτ + 4 log 2 + 4 log(θ₂(τ/2,τ)/2) - 4 log θ₀₀(τ)` and the second-order cusp
  expansions of `θ₀₀` (`thetaC00_second_order`) and of `θ₂(τ/2,τ)/2`
  (`ratio_second_order`), together with the Taylor bound
  `log(1+u) = u - u²/2 + O(‖u‖³)`;
* the assembly, where the constant `4 log 2` is absorbed into `c`.
-/
import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.LogLambdaBound
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound
import Submission.Work.Analysis.BranchLog.holomorphic_of_exp
import Submission.Work.Analysis.DiscreteValues.eq_const_of_isPreconnected
import Submission.Work.Asymptotics.ratio_second_order
import Submission.Work.Asymptotics.thetaC00_second_order

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

/-! ## The `O(‖E‖³)` expansions of the two theta factors

Both are imported: `Work.Asymptotics.ratio_second_order` (the second-order cusp expansion of
`θ₂(τ/2,τ)/2 = 1 + E² + O(‖E‖³)`) and `Work.Asymptotics.thetaC00_second_order`
(`θ₀₀ = 1 + 2E + O(‖E‖⁴)`), with `E = e^{πiτ}`. -/

/-! ## Two elementary lemmas -/

/-- `‖e^{πiz}‖ = e^{-π Im z}`. -/
lemma norm_exp_pi_I_mul (z : ℂ) :
    ‖Complex.exp (Real.pi * Complex.I * z)‖ = Real.exp (-(Real.pi * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * z = ((Real.pi : ℝ) : ℂ) * (Complex.I * z) by ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/-- `log (1+u) = u - u²/2 + O(‖u‖³)` for `‖u‖ ≤ 1/2`. -/
lemma log_second_order (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - u + u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 := by
  have hu1 : ‖u‖ < 1 := by linarith
  have h1 : ‖Complex.log (1 + u) - Complex.logTaylor 3 u‖ ≤ ‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / 3 := by
    have := Complex.norm_log_sub_logTaylor_le 2 hu1
    norm_num at this ⊢
    exact this
  rw [show Complex.logTaylor 3 u = u - u ^ 2 / 2 from by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_succ, zero_add]
    ring] at h1
  have h2 : ‖Complex.log (1 + u) - u + u ^ 2 / 2‖ = ‖Complex.log (1 + u) - (u - u ^ 2 / 2)‖ := by
    ring_nf
  rw [h2]
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h3 : ‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / 3 ≤ ‖u‖ ^ 3 * 2 / 3 := by gcongr
  have h4 : (0 : ℝ) ≤ ‖u‖ ^ 3 := by positivity
  linarith

/-! ## `𝓛` differs from the explicit branch `Lfun` by a constant -/

/-- Every CKMRV logarithm `𝓛` is `Lfun` plus a constant: both have exponential `λ` and
`ℍ` is connected, so their difference is a continuous `2πiℤ`-valued function. -/
theorem ll_sub_Lfun_const (ℓ : Work.Kernels.LogLambdaData) :
    ∃ c : ℂ, ∀ τ : UpperHalfPlane, ℓ.L τ = Work.Kernels.LogLambda.Lfun (τ : ℂ) + c := by
  have hcont : ContinuousOn (fun τ : UpperHalfPlane =>
      ℓ.L τ - Work.Kernels.LogLambda.Lfun (τ : ℂ)) Set.univ :=
    (ℓ.holo.continuous.continuousOn).sub
      ((Work.Kernels.LogLambda.Lfun_spec.1.continuousOn).comp
        continuous_coe.continuousOn (fun τ _ => τ.im_pos))
  have hmaps : Set.MapsTo (fun τ : UpperHalfPlane =>
      ℓ.L τ - Work.Kernels.LogLambda.Lfun (τ : ℂ)) Set.univ {w : ℂ | Complex.exp w = 1} := by
    intro τ _
    show Complex.exp (ℓ.L τ - Work.Kernels.LogLambda.Lfun (τ : ℂ)) = 1
    rw [Complex.exp_sub, ℓ.exp_L τ,
      Work.Kernels.LogLambda.Lfun_spec.2.1 (τ : ℂ) τ.2,
      Work.Kernels.LogLambda.lamC_of_mem τ.2,
      div_self]
    rw [← ℓ.exp_L τ]
    exact Complex.exp_ne_zero (ℓ.L τ)
  refine ⟨ℓ.L ⟨Complex.I, by norm_num⟩ - Work.Kernels.LogLambda.Lfun (Complex.I), fun τ => ?_⟩
  have hcon := isPreconnected_univ.constant_of_mapsTo
    (Work.Analysis.BranchLog.isDiscrete_exp_eq_one)
    hcont hmaps
    (Set.mem_univ (⟨Complex.I, by norm_num⟩ : UpperHalfPlane)) (Set.mem_univ τ)
  have h := hcon.symm
  simp only at h
  linear_combination h

/-! ## The second-order expansion of the explicit branch `Lfun` -/

/-- `Lfun τ - πiτ = 4 log 2 - 8E + 12E² + O(‖E‖³)`, `E = e^{πiτ}`, for `Im τ ≥ 1`. -/
theorem Lfun_second_order :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.im →
      ‖Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z - 4 * (Real.log 2 : ℂ)
        + 8 * Complex.exp (Real.pi * Complex.I * z)
        - 12 * (Complex.exp (Real.pi * Complex.I * z)) ^ 2‖
      ≤ C * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 3 := by
  refine ⟨1000, by norm_num, fun z hz => ?_⟩
  set E : ℂ := Complex.exp (Real.pi * Complex.I * z) with hEdef
  set r : ℂ := jacobiTheta₂ (z / 2) z / 2 with hrdef
  set θ : ℂ := Work.Kernels.LogLambda.thetaC00 z with hθdef
  have hEnorm : ‖E‖ = Real.exp (-(Real.pi * z.im)) := by rw [hEdef, norm_exp_pi_I_mul]
  have hEnn : 0 ≤ ‖E‖ := norm_nonneg E
  have hE8 : ‖E‖ ≤ 1 / 8 := by
    rw [hEnorm]
    refine le_trans (Real.exp_le_exp.mpr ?_) (by
      simpa using Work.Kernels.LogLambda.LogGrowth.exp_le_inv_eight_of_le_neg_pi
        (u := -Real.pi) le_rfl)
    nlinarith [Real.pi_pos, hz]
  have hE1 : ‖E‖ ≤ 1 := by linarith
  have hA : ‖r - 1 - E ^ 2‖ ≤ 4 * ‖E‖ ^ 3 := by
    rw [hrdef, hEdef]
    exact ratio_second_order z hz
  have hB : ‖θ - 1 - 2 * E‖ ≤ 4 * ‖E‖ ^ 4 := by
    rw [hθdef, hEdef]
    exact thetaC00_second_order z hz
  -- the two key bounds
  have hs_bound : ‖r - 1‖ ≤ 5 * ‖E‖ ^ 2 := by
    have h1 : r - 1 = E ^ 2 + (r - 1 - E ^ 2) := by ring
    have h2 : ‖r - 1‖ ≤ ‖E ^ 2‖ + ‖r - 1 - E ^ 2‖ := by
      calc ‖r - 1‖ = ‖E ^ 2 + (r - 1 - E ^ 2)‖ := congrArg norm h1
        _ ≤ ‖E ^ 2‖ + ‖r - 1 - E ^ 2‖ := norm_add_le _ _
    rw [norm_pow] at h2
    have h3 : ‖E‖ ^ 3 ≤ ‖E‖ ^ 2 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (2:ℕ) ≤ 3)
    nlinarith [h2, hA, h3]
  have hs2 : ‖r - 1‖ ≤ 1 / 2 := by
    have hE2 : ‖E‖ ^ 2 ≤ 1 / 64 := by nlinarith [hE8, hEnn]
    nlinarith [hs_bound, hE2]
  have hI : ‖Complex.log r - E ^ 2‖ ≤ 150 * ‖E‖ ^ 3 := by
    have hr1 : r = 1 + (r - 1) := by ring
    have hlr : Complex.log r = Complex.log (1 + (r - 1)) := congrArg Complex.log hr1
    have hlog : ‖Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2‖ ≤ ‖r - 1‖ ^ 3 :=
      log_second_order (r - 1) hs2
    rw [hlr,
      show Complex.log (1 + (r - 1)) - E ^ 2
        = (Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
          + (r - 1 - E ^ 2) - (r - 1) ^ 2 / 2 from by ring]
    have hnorm : ‖(Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
        + (r - 1 - E ^ 2) - (r - 1) ^ 2 / 2‖
        ≤ ‖Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2‖
          + ‖r - 1 - E ^ 2‖ + ‖(r - 1) ^ 2 / 2‖ := by
      refine le_trans (norm_sub_le ((Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
        + (r - 1 - E ^ 2)) ((r - 1) ^ 2 / 2)) ?_
      have h := norm_add_le (Complex.log (1 + (r - 1)) - (r - 1) + (r - 1) ^ 2 / 2)
        (r - 1 - E ^ 2)
      linarith
    have hsq : ‖(r - 1) ^ 2 / 2‖ ≤ (5 * ‖E‖ ^ 2) ^ 2 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
      have h5 : ‖r - 1‖ ^ 2 ≤ (5 * ‖E‖ ^ 2) ^ 2 := by
        nlinarith [hs_bound, norm_nonneg (r - 1), norm_nonneg E]
      linarith
    have hcube : ‖r - 1‖ ^ 3 ≤ (5 * ‖E‖ ^ 2) ^ 3 := by gcongr
    have hE4 : ‖E‖ ^ 4 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 4)
    have hE6 : ‖E‖ ^ 6 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 6)
    have h1 : ‖E‖ ^ 3 ≤ 1 := pow_le_one₀ hEnn hE1
    nlinarith [hnorm, hlog, hA, hsq, hcube, hE4, hE6, h1, hEnn]
  have hv_bound : ‖θ - 1‖ ≤ 3 * ‖E‖ := by
    have h1 : θ - 1 = 2 * E + (θ - 1 - 2 * E) := by ring
    have h2 : ‖θ - 1‖ ≤ ‖2 * E‖ + ‖θ - 1 - 2 * E‖ := by
      calc ‖θ - 1‖ = ‖2 * E + (θ - 1 - 2 * E)‖ := congrArg norm h1
        _ ≤ ‖2 * E‖ + ‖θ - 1 - 2 * E‖ := norm_add_le _ _
    have h3 : ‖2 * E‖ = 2 * ‖E‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h4 : 4 * ‖E‖ ^ 4 ≤ ‖E‖ := by
      have h3' : ‖E‖ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hEnn hE8 3
      nlinarith [h3', hEnn]
    nlinarith [h2, hB, h3, h4, hEnn]
  have hv2 : ‖θ - 1‖ ≤ 1 / 2 := by nlinarith [hv_bound, hE8]
  have hII : ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ ≤ 50 * ‖E‖ ^ 3 := by
    have hθ1 : θ = 1 + (θ - 1) := by ring
    have hlθ : Complex.log θ = Complex.log (1 + (θ - 1)) := congrArg Complex.log hθ1
    have hlog : ‖Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2‖ ≤ ‖θ - 1‖ ^ 3 :=
      log_second_order (θ - 1) hv2
    have h3 : 2 * E ^ 2 - (θ - 1) ^ 2 / 2
        = -2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2 := by ring
    rw [hlθ,
      show Complex.log (1 + (θ - 1)) - 2 * E + 2 * E ^ 2
        = (Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
          + (θ - 1 - 2 * E) + (2 * E ^ 2 - (θ - 1) ^ 2 / 2) from by ring, h3]
    have ha : ‖-2 * E * (θ - 1 - 2 * E)‖ = 2 * ‖E‖ * ‖θ - 1 - 2 * E‖ := by
      rw [norm_mul, norm_mul]
      norm_num
    have hb : ‖(θ - 1 - 2 * E) ^ 2 / 2‖ = ‖θ - 1 - 2 * E‖ ^ 2 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
    have hnorm : ‖(Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
        + (θ - 1 - 2 * E) + (-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2)‖
        ≤ ‖Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2‖ + ‖θ - 1 - 2 * E‖
          + (2 * ‖E‖ * ‖θ - 1 - 2 * E‖ + ‖θ - 1 - 2 * E‖ ^ 2 / 2) := by
      refine le_trans (norm_add_le ((Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
        + (θ - 1 - 2 * E)) (-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2)) ?_
      have h5 : ‖-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2‖
          ≤ 2 * ‖E‖ * ‖θ - 1 - 2 * E‖ + ‖θ - 1 - 2 * E‖ ^ 2 / 2 := by
        calc ‖-2 * E * (θ - 1 - 2 * E) - (θ - 1 - 2 * E) ^ 2 / 2‖
            ≤ ‖-2 * E * (θ - 1 - 2 * E)‖ + ‖(θ - 1 - 2 * E) ^ 2 / 2‖ := norm_sub_le _ _
          _ = 2 * ‖E‖ * ‖θ - 1 - 2 * E‖ + ‖θ - 1 - 2 * E‖ ^ 2 / 2 := by rw [ha, hb]
      have h6 := norm_add_le (Complex.log (1 + (θ - 1)) - (θ - 1) + (θ - 1) ^ 2 / 2)
        (θ - 1 - 2 * E)
      linarith
    have hcube : ‖θ - 1‖ ^ 3 ≤ (3 * ‖E‖) ^ 3 := by gcongr
    have hB4 : ‖θ - 1 - 2 * E‖ ^ 2 ≤ (4 * ‖E‖ ^ 4) ^ 2 := by gcongr
    have hE4 : ‖E‖ ^ 4 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 4)
    have hE5 : ‖E‖ ^ 5 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 5)
    have hE8' : ‖E‖ ^ 8 ≤ ‖E‖ ^ 3 := pow_le_pow_of_le_one hEnn hE1 (by norm_num : (3:ℕ) ≤ 8)
    have h1 : ‖E‖ ^ 3 ≤ 1 := pow_le_one₀ hEnn hE1
    nlinarith [hnorm, hlog, hB, hB4, hcube, hE4, hE5, hE8', h1, hEnn, hv_bound]
  -- assemble
  have hzW : z ∈ Work.Kernels.LogLambda.W := by
    show (1 / 2 : ℝ) < z.im
    linarith
  have hLU : Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z
      = 4 * (Real.log 2 : ℂ) + 4 * Complex.log r - 4 * Complex.log θ := by
    rw [Work.Kernels.LogLambda.LU, Work.Kernels.LogLambda.thetaC10_div_exp]
    simp only [hrdef, hθdef, Work.Kernels.LogLambda.thetaC00]
    ring
  have hkey : Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z
        - 4 * (Real.log 2 : ℂ) + 8 * E - 12 * E ^ 2
      = 4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2) := by
    rw [Work.Kernels.LogLambda.Lfun_eq_LU_on_W z hzW, hLU]
    ring
  rw [hkey]
  have hfin : ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖
      ≤ 4 * ‖Complex.log r - E ^ 2‖ + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ := by
    calc ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖
        ≤ ‖4 * (Complex.log r - E ^ 2)‖ + ‖4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖ :=
          norm_sub_le _ _
      _ = 4 * ‖Complex.log r - E ^ 2‖ + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
  calc ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2)‖
      ≤ 4 * ‖Complex.log r - E ^ 2‖ + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2‖ := hfin
    _ ≤ 4 * (150 * ‖E‖ ^ 3) + 4 * (50 * ‖E‖ ^ 3) := by linarith [hI, hII]
    _ = 800 * ‖E‖ ^ 3 := by ring
    _ ≤ 1000 * ‖E‖ ^ 3 := by
        have : (0 : ℝ) ≤ ‖E‖ ^ 3 := by positivity
        linarith

/-! ## The target statement -/

theorem cusp_L_second (ℓ : Work.Kernels.LogLambdaData) : ∃ c : ℂ, ∃ C : ℝ, 0 < C ∧
    ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + c - 8 * Work.Residues.Ept z +
          12 * (Work.Residues.Ept z) ^ 2)‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3 := by
  obtain ⟨c₀, hc₀⟩ := ll_sub_Lfun_const ℓ
  obtain ⟨C, hC, hCb⟩ := Lfun_second_order
  refine ⟨c₀ + 4 * (Real.log 2 : ℂ), C, hC, fun z hz => ?_⟩
  have h1 := hCb (z : ℂ) hz
  have h2 := hc₀ z
  have hgoal : Work.Kernels.LogLambda.Lfun (z : ℂ) + c₀
        - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + (c₀ + 4 * (Real.log 2 : ℂ))
            - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2)
      = Work.Kernels.LogLambda.Lfun (z : ℂ) - (Real.pi : ℂ) * Complex.I * (z : ℂ)
        - 4 * (Real.log 2 : ℂ) + 8 * Complex.exp (Real.pi * Complex.I * (z : ℂ))
        - 12 * (Complex.exp (Real.pi * Complex.I * (z : ℂ))) ^ 2 := by
    rw [Work.Residues.Ept_apply]
    ring
  rw [h2, hgoal]
  simpa only [Work.Residues.Ept_apply] using h1

end Work.Asymptotics
