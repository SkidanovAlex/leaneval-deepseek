import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Kernels.ModerateGrowth

namespace Work.CKFinal

theorem gaussTerm_iteratedDeriv_bound (l : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
        ≤ A * (Work.Kernels.scale τ) ^ B * (1 + |r|) ^ l
            * Real.exp (-(Real.pi * τ.im * r ^ 2)) := by
  refine ⟨((l + 1 : ℕ) : ℝ) * (Nat.factorial (l + 2) : ℝ) * (1 + Real.pi) ^ (2 * l),
    ((2 * l : ℕ) : ℝ), by positivity, by positivity, ?_⟩
  intro τ r
  -- Write `gaussTerm τ s = exp (a * s^2 * (-1))` with `a = -(π i τ)`, the shape handled by
  -- `Work.Asymptotics.iteratedDeriv_exp_neg_sq_bound`.
  set a : ℂ := -(Real.pi * Complex.I * (τ : ℂ)) with ha
  have hfun : (fun s : ℝ => Work.Kernels.gaussTerm τ s)
      = fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2)) := by
    funext s
    unfold Work.Kernels.gaussTerm
    rw [ha]
    congr 1
    ring
  rw [hfun]
  have hmain := Work.Asymptotics.iteratedDeriv_exp_neg_sq_bound l a r
  -- Real and imaginary parts of the parameter.
  have hre : a.re = Real.pi * τ.im := by
    rw [ha]
    simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
  have hnorm_a : ‖a‖ = Real.pi * ‖(τ : ℂ)‖ := by
    rw [ha, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
    congr 1
    rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg]
  -- Bound the parameter-dependent constant by a power of `scale τ`.
  have hstep : (1 + ‖a‖) ^ (2 * l)
      ≤ (1 + Real.pi) ^ (2 * l) * (Work.Kernels.scale τ) ^ (2 * l) := by
    have hscale1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hnorm : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hkey : 1 + ‖a‖ ≤ (1 + Real.pi) * Work.Kernels.scale τ := by
      rw [hnorm_a]; nlinarith [hnorm, hscale1, hpi]
    calc (1 + ‖a‖) ^ (2 * l)
        ≤ ((1 + Real.pi) * Work.Kernels.scale τ) ^ (2 * l) := by
          apply pow_le_pow_left₀ _ hkey; positivity
      _ = (1 + Real.pi) ^ (2 * l) * (Work.Kernels.scale τ) ^ (2 * l) := by rw [mul_pow]
  -- Match the exponential factors.
  have hexp : Real.exp (-(a.re) * r ^ 2) = Real.exp (-(Real.pi * τ.im * r ^ 2)) := by
    congr 1
    rw [hre]; ring
  rw [hexp] at hmain
  set C0 : ℝ := ((l + 1 : ℕ) : ℝ) * (Nat.factorial (l + 2) : ℝ) with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have h1 : C0 * (1 + ‖a‖) ^ (2 * l)
      ≤ C0 * (1 + Real.pi) ^ (2 * l) * (Work.Kernels.scale τ) ^ (2 * l) := by
    calc C0 * (1 + ‖a‖) ^ (2 * l)
        ≤ C0 * ((1 + Real.pi) ^ (2 * l) * (Work.Kernels.scale τ) ^ (2 * l)) :=
          mul_le_mul_of_nonneg_left hstep hC0nn
      _ = C0 * (1 + Real.pi) ^ (2 * l) * (Work.Kernels.scale τ) ^ (2 * l) := by ring
  have h2 : (0:ℝ) ≤ (1 + |r|) ^ l := by positivity
  have h3 : (0:ℝ) ≤ Real.exp (-(Real.pi * τ.im * r ^ 2)) := Real.exp_nonneg _
  refine le_trans hmain ?_
  calc C0 * (1 + ‖a‖) ^ (2 * l) * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2))
      ≤ (C0 * (1 + Real.pi) ^ (2 * l) * (Work.Kernels.scale τ) ^ (2 * l))
          * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) h3
    _ = (C0 * (1 + Real.pi) ^ (2 * l)) * (Work.Kernels.scale τ) ^ (2 * l)
          * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2)) := by ring
    _ = (C0 * (1 + Real.pi) ^ (2 * l)) * (Work.Kernels.scale τ) ^ ((2 * l : ℕ) : ℝ)
          * (1 + |r|) ^ l * Real.exp (-(Real.pi * τ.im * r ^ 2)) := by
        rw [Real.rpow_natCast]

end Work.CKFinal
