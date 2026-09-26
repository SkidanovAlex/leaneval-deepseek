import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

lemma Epoint_norm_qParamFun (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [Work.Kernels.qParamFun, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)).re = -(2 * Real.pi * z.im) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
  rw [hre]

lemma Epoint_norm_qParamFun_le (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖
      ≤ (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by
  rw [Epoint_norm_qParamFun]
  have h1 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (z : ℂ), sq_nonneg (1 + ‖(z : ℂ)‖)]
  have h2 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, z.im_pos])
  exact le_trans h2 (le_mul_of_one_le_left (Real.exp_nonneg _) h1)

/-- The `(quotientbounds1new)` slash bound for `K_+^{(8)}` on the cusp-`0` disk, from the
`Ξ_8` bound. -/
lemma KPlus8_slash_bound_of_Xi8
    (h : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      ‖Xi8 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (2 : ℤ) * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
            Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  set c8 : ℂ := (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hc8
  have hc8ne : c8 ≠ 0 := by
    rw [hc8]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)))
      Complex.I_ne_zero
  have hc8pos : 0 < ‖c8‖ := norm_pos_iff.mpr hc8ne
  refine ⟨C / ‖c8‖ + 1, N, by positivity, hN, ?_⟩
  intro τ z hτ hz hne
  set D : ℝ := ‖Work.Kernels.DeltaFun z *
    (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hDdef
  have hD : Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hDpos : 0 < D := by rw [hDdef]; exact norm_pos_iff.mpr hD
  have key : c8 * (Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
      ((z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)) = Xi8 τ z := by
    rw [hc8]; exact Xi8_eq τ z hne
  have hval : (z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)
      = Xi8 τ z / (c8 * (Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
    rw [eq_div_iff (mul_ne_zero hc8ne hD), mul_comm]
    exact key
  have hnum : ‖Xi8 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖ :=
    hb τ z hτ hz
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  calc ‖(z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)‖
      = ‖Xi8 τ z‖ / (‖c8‖ * D) := by
        rw [hval, norm_div, norm_mul, hDdef]
    _ ≤ (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖) / (‖c8‖ * D) := by
        apply div_le_div_of_nonneg_right hnum
        positivity
    _ ≤ (C * (Work.Kernels.scale τ) ^ N *
          ((1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)))) / (‖c8‖ * D) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Epoint_norm_qParamFun_le z)
          (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) N))
    _ = ((C / ‖c8‖) * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
          Real.exp (-(Real.pi * z.im))) / D := by
        field_simp
    _ ≤ ((C / ‖c8‖ + 1) * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
          Real.exp (-(Real.pi * z.im))) / D := by
        apply div_le_div_of_nonneg_right _ hDpos.le
        have hle : C / ‖c8‖ ≤ C / ‖c8‖ + 1 := by linarith
        have hb0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N *
            ((1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))) :=
          mul_nonneg (Real.rpow_nonneg (by linarith [Work.Kernels.one_le_scale τ]) N)
            (by positivity)
        nlinarith [hle, hb0]

/-- The `(quotientbounds1new)` slash bound for `K_+^{(24)}` on the cusp-`0` disk, from the
`Ξ_24` bound. -/
lemma KPlus24_slash_bound_of_Xi24
    (h : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      ‖Xi24 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (10 : ℤ) * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
            Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  set c24 : ℂ := (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hc24
  have hc24ne : c24 ≠ 0 := by
    rw [hc24]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · simp [Work.Kernels.c1728]
    · exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hc24pos : 0 < ‖c24‖ := norm_pos_iff.mpr hc24ne
  refine ⟨C / ‖c24‖ + 1, N, by positivity, hN, ?_⟩
  intro τ z hτ hz hne
  set D : ℝ := ‖Work.Kernels.DeltaFun z *
    (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hDdef
  have hD : Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hDpos : 0 < D := by rw [hDdef]; exact norm_pos_iff.mpr hD
  have key : c24 * (Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
      ((z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)) = Xi24 τ z := by
    rw [hc24]; exact Xi24_eq τ z hne
  have hval : (z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)
      = Xi24 τ z / (c24 * (Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
    rw [eq_div_iff (mul_ne_zero hc24ne hD), mul_comm]
    exact key
  have hnum : ‖Xi24 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖ :=
    hb τ z hτ hz
  calc ‖(z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖
      = ‖Xi24 τ z‖ / (‖c24‖ * D) := by
        rw [hval, norm_div, norm_mul, hDdef]
    _ ≤ (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖) / (‖c24‖ * D) := by
        apply div_le_div_of_nonneg_right hnum
        positivity
    _ ≤ (C * (Work.Kernels.scale τ) ^ N *
          ((1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)))) / (‖c24‖ * D) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Epoint_norm_qParamFun_le z)
          (mul_nonneg hC.le (Real.rpow_nonneg (by linarith [Work.Kernels.one_le_scale τ]) N))
    _ = ((C / ‖c24‖) * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
          Real.exp (-(Real.pi * z.im))) / D := by
        field_simp
    _ ≤ ((C / ‖c24‖ + 1) * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) *
          Real.exp (-(Real.pi * z.im))) / D := by
        apply div_le_div_of_nonneg_right _ hDpos.le
        have hle : C / ‖c24‖ ≤ C / ‖c24‖ + 1 := by linarith
        have hb0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N *
            ((1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))) :=
          mul_nonneg (Real.rpow_nonneg (by linarith [Work.Kernels.one_le_scale τ]) N)
            (by positivity)
        nlinarith [hle, hb0]

/-- `EPolyWin` follows from `EFlat` (take the window `N₀ = 0`). -/
lemma EPolyWin_of_EFlat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (h : EFlat ℓ d) :
    EPolyWin ℓ d := by
  obtain ⟨c, N', hc, hb⟩ := h 0 le_rfl
  refine ⟨0, max c 1, max N' 0, 0, le_rfl, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    le_max_right _ _, le_rfl, ?_⟩
  intro w t hw ht htwin
  have ht1 : t ≤ 1 := by
    have h := htwin
    rwa [Real.rpow_zero] at h
  have h1 := hb w t hw ht ht1
  have h2 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      ≤ max c 1 * (Work.Kernels.scale w) ^ (max N' 0) := by
    have hs : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hN'm : (Work.Kernels.scale w) ^ N' ≤ (Work.Kernels.scale w) ^ (max N' 0) :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c * (Work.Kernels.scale w) ^ N' := by
          simpa using h1
      _ ≤ max c 1 * (Work.Kernels.scale w) ^ (max N' 0) :=
          mul_le_mul (le_max_left _ _) hN'm (Real.rpow_nonneg (by linarith) _) (by positivity)
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      ≤ max c 1 * (Work.Kernels.scale w) ^ (max N' 0) := h2
    _ = max c 1 * (Work.Kernels.scale w) ^ (max N' 0) * (1 + t) ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]




end Work.Asymptotics
