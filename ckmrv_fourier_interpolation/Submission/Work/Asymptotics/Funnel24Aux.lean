/-
# Funnel estimates for the `d = 24` tail: atom bounds on the funnel and the contour

(Copy of the helper lemmas formerly in `Funnel24Aux`; restored after an accidental overwrite.)
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.E4cube_cusp_second
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_aux
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Residues.LamSExpansion
import Submission.Work.Residues.LamSExpBound
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.FunnelNumerics.Delta_funnel_bounds
import Submission.Work.FunnelNumerics.Lamb_funnel_bound
import Submission.Work.Residues.LogLambdaBound

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-! ## Elementary facts on the contour `z = i t` -/

/-- On the contour `z = i t`, the imaginary part of `z` is `t`. -/
theorem ft_im_of_coe {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) : z.im = t := by
  have h := congrArg Complex.im hz
  simp [UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at h
  linarith [h]

/-- `‖Ept z‖ = exp (-π t)` on the contour. -/
theorem ft_norm_Ept {z : ℍ} {t : ℝ} (hz : z.im = t) :
    ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept, hz]

/-- `‖q(z)‖ = exp (-2π t)` on the contour. -/
theorem ft_norm_qParam {z : ℍ} {t : ℝ} (hz : z.im = t) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
  rw [norm_qParamFun, hz]

/-- `‖(z : ℂ)‖ = t` for `z = i t`, `t ≥ 0`. -/
theorem ft_norm_coe {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) (ht : 0 ≤ t) :
    ‖(z : ℂ)‖ = t := by
  rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

/-- `‖Ept z‖ ≤ 1` when `1 ≤ z.im`. -/
theorem ft_Ept_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Work.Residues.Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

/-- `exp (2π) ≥ 216`. -/
theorem ft_exp_two_pi_ge : (216 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
  have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = ((6:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h4 : (216 : ℝ) ≤ Real.exp 6 := by
    rw [h3]; linarith [h2, (by norm_num : (216:ℝ) ≤ 2.7^6)]
  exact le_trans h4 (Real.exp_le_exp.mpr h6)

/-- `exp (-(2π Im τ)) ≤ 1/40000` when `12 ≤ 2π Im τ`. -/
theorem ft_exp_neg_two_pi_im_le (τ : ℍ) (hn : 12 ≤ 2 * Real.pi * τ.im) :
    Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 40000 := by
  have h1 : (12:ℝ) ≤ 2 * Real.pi * τ.im := hn
  have h2 : Real.exp (12:ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := Real.exp_le_exp.mpr h1
  have h3 : (40000:ℝ) ≤ Real.exp 12 := by
    have h4 : Real.exp 12 = (Real.exp 1)^12 := by
      rw [show (12:ℝ) = ((12:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h4]
    have h5 : (2.7:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h6 : (2.7:ℝ)^12 ≤ (Real.exp 1)^12 := pow_le_pow_left₀ (by norm_num) h5 12
    linarith [h6, (by norm_num : (40000:ℝ) ≤ 2.7^12)]
  have h3' : (40000:ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := le_trans h3 h2
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h3'

/-- `(scale τ)^N ≥ 0`. -/
theorem ft_scale_rpow_nonneg (τ : ℍ) (N : ℝ) :
    (0:ℝ) ≤ Work.Kernels.scale τ ^ N :=
  Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N

/-! ## Bounds for `E₄` and `Δ` on the funnel and on the contour -/

/-- `‖E₄ τ‖ ≤ 3/2` on the funnel. -/
theorem E4_funnel_upper' (τ : ℍ) (hτ : Funnel τ) :
    ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := by
  have hτ1 : (1:ℝ) ≤ τ.im := le_trans (by norm_num) hτ.2
  have h := E4Fun_sub_one_explicit hτ1
  rw [norm_qParamFun] at h
  have h4 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 40000 :=
    ft_exp_neg_two_pi_im_le τ (by
      have : (6:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith [hτ.2, Real.pi_pos])
  have h6 : (20000:ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 20000)
    linarith
  have h7 : ‖Work.Kernels.E4Fun τ‖ ≤ ‖Work.Kernels.E4Fun τ - 1‖ + 1 := by
    have hh := norm_add_le (Work.Kernels.E4Fun τ - 1) (1:ℂ)
    simpa using hh
  have h8 : ‖Work.Kernels.E4Fun τ - 1‖ ≤ 1 / 2 := le_trans h h6
  linarith

/-- `‖E₄ z‖ ≥ 1/2` for `3 ≤ z.im`. -/
theorem E4_imagAxis_lower' (z : ℍ) (hz : 3 ≤ z.im) :
    (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ := by
  have h := E4Fun_sub_one_explicit (le_trans (by norm_num) hz)
  rw [norm_qParamFun] at h
  have h4 : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 / 40000 :=
    ft_exp_neg_two_pi_im_le z (by
      have : (6:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith [hz, Real.pi_pos])
  have h6 : (20000:ℝ) * Real.exp (-(2 * Real.pi * z.im)) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 20000)
    linarith
  have h8 : ‖Work.Kernels.E4Fun z - 1‖ ≤ 1 / 2 := le_trans h h6
  have h11 : ‖Work.Kernels.E4Fun z‖ ≥ (1:ℝ) - ‖(1:ℂ) - Work.Kernels.E4Fun z‖ := by
    have hh := abs_norm_sub_norm_le (1:ℂ) ((1:ℂ) - Work.Kernels.E4Fun z)
    rw [show (1:ℂ) - ((1:ℂ) - Work.Kernels.E4Fun z) = Work.Kernels.E4Fun z by ring] at hh
    rw [norm_one] at hh
    exact le_trans (le_abs_self _) hh
  have h12 : ‖(1:ℂ) - Work.Kernels.E4Fun z‖ = ‖Work.Kernels.E4Fun z - 1‖ := by
    rw [show (1:ℂ) - Work.Kernels.E4Fun z = -(Work.Kernels.E4Fun z - 1) by ring, norm_neg]
  rw [h12] at h11
  linarith

/-- `‖Δ τ‖ ≤ 2 exp (-2π Im τ)` for `1 ≤ Im τ`. -/
theorem DeltaFun_le_two_exp (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) :=
  DeltaFun_upper_sharp τ hτ

/-- `‖Δ τ‖ ≥ (1/2) ‖q(τ)‖` for `2 ≤ Im τ`. -/
theorem DeltaFun_ge_half_qParam (τ : ℍ) (hτ : 2 ≤ τ.im) :
    (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  rw [norm_qParamFun]
  exact DeltaFun_funnel_lower_sharp hτ

/-! ## The uniform divisor bound for `Sh` on the contour -/

/-- `‖Δ(z) j(τ)‖ ≤ 27/4 · exp (-(π (t - Im τ)))²` for `τ` in the funnel and `z = i t`. -/
theorem funnel_rho_exp (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ (27 / 2) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := by
  have hτ2 : 2 ≤ τ.im := hτ.2
  have ht0 : 0 < t := by linarith
  have hzim : z.im = t := ft_im_of_coe hz
  have hΔz : ‖Work.Kernels.DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * t)) := by
    rw [← hzim]
    exact DeltaFun_upper_sharp z (by rw [hzim]; linarith)
  have hjτ : ‖Work.Kernels.jInvariantFun τ‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
    have hΔlow : (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := by
      rw [← norm_qParamFun]
      exact Work.FunnelNumerics.Delta_funnel_bounds.1 τ hτ2
    have hE4b : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
    have hnum : ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ (3 / 2) ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hE4b 3
    have hpos : 0 < (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
    have hmain : ‖Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ‖
        ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
      rw [norm_div]
      have hinv : (‖Work.Kernels.DeltaFun τ‖)⁻¹
          ≤ ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ :=
        inv_anti₀ hpos hΔlow
      have hrec : ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹
          = 2 * Real.exp (2 * Real.pi * τ.im) := by
        rw [Real.exp_neg]
        field_simp
      rw [hrec] at hinv
      calc ‖Work.Kernels.E4Fun τ ^ 3‖ / ‖Work.Kernels.DeltaFun τ‖
          = ‖Work.Kernels.E4Fun τ ^ 3‖ * (‖Work.Kernels.DeltaFun τ‖)⁻¹ := by ring
        _ ≤ (3 / 2) ^ 3 * (2 * Real.exp (2 * Real.pi * τ.im)) :=
            mul_le_mul hnum hinv (by positivity) (by positivity)
        _ = (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by norm_num; ring
    simpa [Work.Kernels.jInvariantFun] using hmain
  rw [norm_mul]
  have hcombi : (2 * Real.exp (-(2 * Real.pi * t))) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
      = (27 / 2) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := by
    rw [show (2 * Real.exp (-(2 * Real.pi * t))) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
        = (27 / 2) * (Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * τ.im)) by ring]
    rw [← Real.exp_add, show -(2 * Real.pi * t) + 2 * Real.pi * τ.im
      = -(Real.pi * (t - τ.im)) + -(Real.pi * (t - τ.im)) by ring, Real.exp_add]
    ring
  calc ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ‖
      ≤ (2 * Real.exp (-(2 * Real.pi * t))) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) :=
        mul_le_mul hΔz hjτ (norm_nonneg _) (by positivity)
    _ = (27 / 2) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := hcombi

/-- `‖Δ(z) j(τ)‖ ≤ 1/16` for `τ` in the funnel and `z = i t`, `t ≥ Im τ + 1`. -/
theorem funnel_rho_le (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ ≤ (1 / 16 : ℝ) := by
  refine le_trans (funnel_rho_exp τ z t hτ ht hz) ?_
  have hsq : Real.exp (-(Real.pi * (t - τ.im))) ^ 2
      = Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hsq]
  have h1 : (1 : ℝ) ≤ t - τ.im := by linarith
  have h2 : Real.exp (-(2 * Real.pi * (t - τ.im))) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, h1])
  have h3 : (27 / 2 : ℝ) * Real.exp (-(2 * Real.pi)) ≤ 1 / 16 := by
    rw [Real.exp_neg,
      show (27 / 2 : ℝ) * (Real.exp (2 * Real.pi))⁻¹
        = 27 / (2 * Real.exp (2 * Real.pi)) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.exp (2 * Real.pi))]
    nlinarith [ft_exp_two_pi_ge]
  linarith [h2, h3]

/-- `‖Sh τ z‖ ≥ 1/16` on the funnel. -/
theorem funnel_Sh_ge (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    (1 / 16 : ℝ) ≤ ‖Compact.Sh τ z‖ := by
  have ht3 : 3 ≤ t := by linarith [hτ.2]
  have hzim : z.im = t := ft_im_of_coe hz
  have hz3 : 3 ≤ z.im := by rw [hzim]; linarith
  have hρ := funnel_rho_le τ z t hτ ht hz
  have hE4z : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
    Work.FunnelNumerics.E4_funnel_bounds.2 z hz3
  have hE4z3 : (1 / 8 : ℝ) ≤ ‖Work.Kernels.E4Fun z ^ 3‖ := by
    rw [norm_pow]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hE4z 3
    norm_num at h
    linarith
  rw [show Compact.Sh τ z
      = Work.Kernels.E4Fun z ^ 3 - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
    from rfl]
  have h := abs_norm_sub_norm_le (Work.Kernels.E4Fun z ^ 3)
    (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)
  have h2 : ‖Work.Kernels.E4Fun z ^ 3‖
      - ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ ‖Work.Kernels.E4Fun z ^ 3
          - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ :=
    le_trans (le_abs_self _) h
  linarith [h2, hE4z3, hρ]

/-! ## Growth of the `τ`-atoms on the funnel -/

/-- `ψ₂` and `ψ₄` have moderate growth on the funnel. -/
theorem psi_scale_funnel (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.psi2 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.psi4 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  have h2 := (psi_InP ℓ).1.2
  have h4 := (psi_InP ℓ).2.2
  obtain ⟨α2, N2, hα2, hN2, hb2⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ (Work.Kernels.psi2 ℓ)).mp h2
  obtain ⟨α4, N4, hα4, hN4, hb4⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ (Work.Kernels.psi4 ℓ)).mp h4
  refine ⟨max α2 α4 + 1, max N2 N4, by positivity,
    le_trans hN2 (le_max_left _ _), ?_⟩
  intro τ hτ
  have hs1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsN : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max N2 N4) := ft_scale_rpow_nonneg τ _
  have h2b : ‖Work.Kernels.psi2 ℓ τ‖ ≤ α2 * (Work.Kernels.scale τ) ^ N2 :=
    hb2 τ (Set.mem_univ τ)
  have h4b : ‖Work.Kernels.psi4 ℓ τ‖ ≤ α4 * (Work.Kernels.scale τ) ^ N4 :=
    hb4 τ (Set.mem_univ τ)
  have h2c : α2 * (Work.Kernels.scale τ) ^ N2
      ≤ (max α2 α4 + 1) * (Work.Kernels.scale τ) ^ (max N2 N4) := by
    have h1 : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (max N2 N4) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
    have h3 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := ft_scale_rpow_nonneg τ N2
    nlinarith [h1, h3, hsN, le_max_left α2 α4, hα2]
  have h4c : α4 * (Work.Kernels.scale τ) ^ N4
      ≤ (max α2 α4 + 1) * (Work.Kernels.scale τ) ^ (max N2 N4) := by
    have h1 : (Work.Kernels.scale τ) ^ N4 ≤ (Work.Kernels.scale τ) ^ (max N2 N4) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
    have h3 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N4 := ft_scale_rpow_nonneg τ N4
    nlinarith [h1, h3, hsN, le_max_right α2 α4, hα4]
  exact ⟨le_trans h2b h2c, le_trans h4b h4c⟩

/-- `‖Δ τ‖ ≤ 2 ‖q(τ)‖` on the funnel. -/
theorem DeltaFun_funnel_le (τ : ℍ) (hτ : Funnel τ) :
    ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ := by
  rw [norm_qParamFun]
  exact DeltaFun_upper_sharp τ (Funnel.im_one hτ)

/-- `‖E₄ τ ^ 3‖ ≤ 27/8` on the funnel. -/
theorem E4cube_funnel_le (τ : ℍ) (hτ : Funnel τ) :
    ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ 27 / 8 := by
  have h := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
  rw [norm_pow]
  have := pow_le_pow_left₀ (norm_nonneg _) h 3
  norm_num at this
  exact this

/-- `‖Xc ℓ z‖ ≤ (π + ‖cuspC ℓ‖) (1 + ‖z‖)`. -/
theorem Xc_le (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    ‖Compact.Xc ℓ z‖ ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) :=
  Compact.kaux_norm_Xc_le ℓ z

/-- `tpar τ ^ 2 = ‖q(τ)‖`. -/
theorem tpar_sq_eq_norm_qParam (τ : ℍ) :
    Work.Residues.tpar τ ^ 2 = ‖Work.Kernels.qParamFun τ‖ := by
  rw [Work.Residues.tpar_eq_norm_Ept, Work.Residues.norm_Ept, norm_qParamFun, sq,
    ← Real.exp_add]
  congr 1
  ring

/-- The near-identity `ψ₄E₈ - ψ₂E₁₀ = O(q_τ scale^N)` on the funnel. -/
theorem psi4E8_sub_psi2E10_funnel (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
          - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨CX, hCX, hX⟩ :=
    Work.FunnelNumerics.cusp_bound_two (S := Work.Residues.S_X)
      (by unfold Work.Residues.S_X; fun_prop) 2
  obtain ⟨CY, hCY, hY⟩ :=
    Work.FunnelNumerics.cusp_bound_two (S := Work.Residues.S_Y)
      (by unfold Work.Residues.S_Y; fun_prop) 1
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := Work.FunnelNumerics.L_scale_bound ℓ
  obtain ⟨CS, hCS, hLS⟩ := Work.FunnelNumerics.LS_tpar_bound ℓ
  refine ⟨CL * CX + CS * CY + 1, NL, by positivity, hNL, fun τ hτ => ?_⟩
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hXb : ‖Work.Residues.Xfun τ‖ ≤ CX * Work.Residues.tpar τ ^ 2 := by
    rw [Work.Residues.Xfun_eq]; exact hX τ hτ2
  have hYb : ‖Work.Residues.Yfun τ‖ ≤ CY * Work.Residues.tpar τ := by
    rw [Work.Residues.Yfun_eq]
    simpa only [pow_one] using hY τ hτ2
  have hLb : ‖ℓ.L τ‖ ≤ CL * (Work.Kernels.scale τ) ^ NL := hL τ
  have hLSb : ‖ℓ.L_S τ‖ ≤ CS * Work.Residues.tpar τ := hLS τ hτ2
  have hq : Work.Residues.tpar τ ^ 2 = ‖Work.Kernels.qParamFun τ‖ :=
    tpar_sq_eq_norm_qParam τ
  have h1 : ‖ℓ.L τ * Work.Residues.Xfun τ‖
      ≤ CL * CX * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul, ← hq]
    calc ‖ℓ.L τ‖ * ‖Work.Residues.Xfun τ‖
        ≤ (CL * (Work.Kernels.scale τ) ^ NL) * (CX * Work.Residues.tpar τ ^ 2) :=
          mul_le_mul hLb hXb (norm_nonneg _)
            (mul_nonneg hCL.le (ft_scale_rpow_nonneg τ NL))
      _ = CL * CX * (Work.Kernels.scale τ) ^ NL * Work.Residues.tpar τ ^ 2 := by ring
  have h2 : ‖ℓ.L_S τ * Work.Residues.Yfun τ‖
      ≤ CS * CY * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul, ← hq]
    calc ‖ℓ.L_S τ‖ * ‖Work.Residues.Yfun τ‖
        ≤ (CS * Work.Residues.tpar τ) * (CY * Work.Residues.tpar τ) :=
          mul_le_mul hLSb hYb (norm_nonneg _)
            (mul_nonneg hCS.le (Work.Residues.tpar_pos τ).le)
      _ = CS * CY * Work.Residues.tpar τ ^ 2 := by ring
  rw [Work.Residues.psi4E8_sub ℓ τ]
  have hnn : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := by
    have := ft_scale_rpow_nonneg τ NL; positivity
  calc ‖ℓ.L τ * Work.Residues.Xfun τ + ℓ.L_S τ * Work.Residues.Yfun τ‖
      ≤ ‖ℓ.L τ * Work.Residues.Xfun τ‖ + ‖ℓ.L_S τ * Work.Residues.Yfun τ‖ := norm_add_le _ _
    _ ≤ CL * CX * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖
          + CS * CY * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := by
        refine add_le_add h1 ?_
        have hs : (1:ℝ) ≤ (Work.Kernels.scale τ) ^ NL :=
          Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNL
        calc ‖ℓ.L_S τ * Work.Residues.Yfun τ‖
            = ‖ℓ.L_S τ‖ * ‖Work.Residues.Yfun τ‖ := norm_mul _ _
          _ ≤ CS * CY * ‖Work.Kernels.qParamFun τ‖ := by
              simpa only [norm_mul] using h2
          _ = CS * CY * ‖Work.Kernels.qParamFun τ‖ * 1 := by ring
          _ ≤ CS * CY * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ NL :=
              mul_le_mul_of_nonneg_left hs (by positivity)
          _ = CS * CY * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := by ring
    _ = (CL * CX + CS * CY) * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := by ring
    _ ≤ (CL * CX + CS * CY + 1) * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := by
        nlinarith [hnn]

end

end Work.Asymptotics
