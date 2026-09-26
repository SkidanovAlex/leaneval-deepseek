import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.E_deviation_sharp
import Submission.Work.Kernels.ModerateGrowth

/-!
# Auxiliary bounds for the kernel window on the cusp-`0` tile `E`

This file collects the easy halves of `Work.Asymptotics.E_window_exp`:

* `Work.Asymptotics.gcusp_bound_E` — the four cusp coefficient functions `Gcusp ℓ d i j`
  are bounded by `A (scale w)^N` on `E`;
* `Work.Asymptotics.EWindowAux_model_bound` — the cusp model `Aexp (Gcusp ℓ d) w t` is bounded by
  `C (scale w)^N (1+t)^M (1 + e^{2πt})` for `w ∈ E`, `t ≥ 1`;
* `Work.Asymptotics.EWindowAux_above` — the kernel itself obeys this bound for
  `t ≥ Im (S • w) + 1` (`E_deviation_sharp` plus the model bound).
-/

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics

/-- The four cusp coefficient functions are polynomially bounded on `E`. -/
theorem gcusp_bound_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ A N : ℝ, 0 ≤ A ∧ 0 ≤ N ∧ ∀ (w : ℍ), w ∈ KEpsilon → ∀ i j : Fin 2,
      ‖Gcusp ℓ d i j w‖ ≤ A * (Work.Kernels.scale w) ^ N := by
  have h : ∀ i j : Fin 2, ∃ A N : ℝ, 0 ≤ A ∧ 0 ≤ N ∧
      ∀ w : ℍ, w ∈ KEpsilon → ‖Gcusp ℓ d i j w‖ ≤ A * (Work.Kernels.scale w) ^ N := by
    intro i j
    obtain ⟨α, N, hα, hN, hb⟩ :=
      (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d i j)).mp (GcuspInP ℓ d i j)
    exact ⟨α, N, hα, hN, fun w hw => hb w hw.1⟩
  choose A N hA hN hb using h
  set Aall : ℝ := max (max (A 0 0) (A 0 1)) (max (A 1 0) (A 1 1)) with hAall
  set Nall : ℝ := max (max (N 0 0) (N 0 1)) (max (N 1 0) (N 1 1)) with hNall
  have hAle00 : A 0 0 ≤ Aall := by rw [hAall]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hAle01 : A 0 1 ≤ Aall := by rw [hAall]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hAle10 : A 1 0 ≤ Aall := by rw [hAall]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAle11 : A 1 1 ≤ Aall := by rw [hAall]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hAall0 : 0 ≤ Aall := le_trans (hA 0 0) hAle00
  have hNall0 : 0 ≤ Nall := by
    rw [hNall]
    exact le_trans (hN 0 0) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨Aall, Nall, hAall0, hNall0, fun w hw i j => ?_⟩
  have hAle : A i j ≤ Aall := by
    fin_cases i <;> fin_cases j <;>
      first | exact hAle00 | exact hAle01 | exact hAle10 | exact hAle11
  have hNle : N i j ≤ Nall := by
    rw [hNall]
    fin_cases i <;> fin_cases j <;>
      first
        | exact le_trans (le_max_left _ _) (le_max_left _ _)
        | exact le_trans (le_max_right _ _) (le_max_left _ _)
        | exact le_trans (le_max_left _ _) (le_max_right _ _)
        | exact le_trans (le_max_right _ _) (le_max_right _ _)
  calc ‖Gcusp ℓ d i j w‖ ≤ A i j * (Work.Kernels.scale w) ^ (N i j) := hb i j w hw
    _ ≤ Aall * (Work.Kernels.scale w) ^ Nall := by
        refine mul_le_mul hAle ?_ (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _) hAall0
        exact Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hNle

/-- **The cusp model `Aexp` is bounded by `C (scale w)^N (1+t)^M (1 + e^{2πt})` on `E`.** -/
theorem EWindowAux_model_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t →
        ‖Aexp (Gcusp ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
              * (1 + Real.exp (2 * Real.pi * t)) := by
  obtain ⟨A, N, hA, hN, hb⟩ := gcusp_bound_E ℓ d hd
  refine ⟨A + 1, N, 1, by linarith, hN, by norm_num, fun w t hw ht1 => ?_⟩
  have hsw : 0 ≤ Work.Kernels.scale w := (Work.Kernels.scale_pos w).le
  have hS0 : 0 ≤ (Work.Kernels.scale w) ^ N := Real.rpow_nonneg hsw N
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  have hnorm_t : ‖((t : ℝ) : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hexp_norm : ‖Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))‖
      = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hEu : 0 < Real.exp (2 * Real.pi * t) := Real.exp_pos _
  have hG00 : ‖Gcusp ℓ d 0 0 w‖ ≤ A * (Work.Kernels.scale w) ^ N := hb w hw 0 0
  have hG01 : ‖Gcusp ℓ d 0 1 w‖ ≤ A * (Work.Kernels.scale w) ^ N := hb w hw 0 1
  have hG10 : ‖Gcusp ℓ d 1 0 w‖ ≤ A * (Work.Kernels.scale w) ^ N := hb w hw 1 0
  have hG11 : ‖Gcusp ℓ d 1 1 w‖ ≤ A * (Work.Kernels.scale w) ^ N := hb w hw 1 1
  have h1 : ‖Gcusp ℓ d 0 0 w‖ ≤ A * (Work.Kernels.scale w) ^ N := hG00
  have h2 : ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w‖
      ≤ t * (A * (Work.Kernels.scale w) ^ N) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, hnorm_t]
    exact mul_le_mul_of_nonneg_left hG01 ht0
  have h3 : ‖Gcusp ℓ d 1 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w‖
      ≤ A * (Work.Kernels.scale w) ^ N + t * (A * (Work.Kernels.scale w) ^ N) := by
    refine le_trans (norm_add_le _ _) (add_le_add hG10 ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, hnorm_t]
    exact mul_le_mul_of_nonneg_left hG11 ht0
  have h4 : ‖Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))
        * (Gcusp ℓ d 1 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w)‖
      ≤ Real.exp (2 * Real.pi * t)
          * (A * (Work.Kernels.scale w) ^ N + t * (A * (Work.Kernels.scale w) ^ N)) := by
    rw [norm_mul, hexp_norm]
    exact mul_le_mul_of_nonneg_left h3 hEu.le
  rw [Aexp]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (norm_add_le _ _) (add_le_add h1 h2)) h4) ?_
  have hcoef : A * (Work.Kernels.scale w) ^ N + t * (A * (Work.Kernels.scale w) ^ N)
      = A * (Work.Kernels.scale w) ^ N * (1 + t) := by ring
  rw [hcoef]
  have hfac : A * (Work.Kernels.scale w) ^ N * (1 + t)
        + Real.exp (2 * Real.pi * t) * (A * (Work.Kernels.scale w) ^ N * (1 + t))
      = A * (Work.Kernels.scale w) ^ N * (1 + t) * (1 + Real.exp (2 * Real.pi * t)) := by ring
  rw [hfac]
  have h1t : (0:ℝ) < 1 + t := by linarith
  have hstep : A * (Work.Kernels.scale w) ^ N * (1 + t) * (1 + Real.exp (2 * Real.pi * t))
      ≤ (A + 1) * (Work.Kernels.scale w) ^ N * (1 + t) ^ (1 : ℝ)
          * (1 + Real.exp (2 * Real.pi * t)) := by
    rw [Real.rpow_one]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ h1t.le
    refine mul_le_mul_of_nonneg_right ?_ hS0
    linarith
  exact hstep

/-- **The kernel on `E` above the pole height.**  For `t ≥ Im (S • w) + 1`,
`‖K(w,it)‖ ≤ C (scale w)^N (1+t)^M (1 + e^{2πt})`. -/
theorem EWindowAux_above (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
              * (1 + Real.exp (2 * Real.pi * t)) := by
  obtain ⟨C₁, N₁, M₁, hC₁, hN₁, hM₁, hb₁⟩ := E_deviation_sharp ℓ d hd
  obtain ⟨C₂, N₂, M₂, hC₂, hN₂, hM₂, hb₂⟩ := EWindowAux_model_bound ℓ d hd
  refine ⟨2 * (C₁ + C₂), max N₁ N₂, max M₁ M₂, by linarith,
    le_trans hN₁ (le_max_left _ _), le_trans hM₁ (le_max_left _ _), fun w t hw ht => ?_⟩
  have hH2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hHt : (ModularGroup.S • w).im ≤ t := by linarith
  have hdev := hb₁ w t hw ht
  have hmod := hb₂ w t hw ht1
  have hsw : 0 ≤ Work.Kernels.scale w := (Work.Kernels.scale_pos w).le
  have hS0 : 0 ≤ (Work.Kernels.scale w) ^ max N₁ N₂ := Real.rpow_nonneg hsw _
  have hSN₁ : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ max N₁ N₂ :=
    Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_left _ _)
  have hSN₂ : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ max N₁ N₂ :=
    Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) (le_max_right _ _)
  have h1t0 : (0 : ℝ) < 1 + t := by linarith
  have hM10 : (0 : ℝ) ≤ (1 + t) ^ M₁ := Real.rpow_nonneg h1t0.le M₁
  have hM20 : (0 : ℝ) ≤ (1 + t) ^ M₂ := Real.rpow_nonneg h1t0.le M₂
  have hM0 : (0 : ℝ) ≤ (1 + t) ^ max M₁ M₂ := Real.rpow_nonneg h1t0.le _
  have hSM₁ : (1 + t) ^ M₁ ≤ (1 + t) ^ max M₁ M₂ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1 + t) (le_max_left _ _)
  have hSM₂ : (1 + t) ^ M₂ ≤ (1 + t) ^ max M₁ M₂ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1 + t) (le_max_right _ _)
  have hexp1 : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hHt]
  have hE1 : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * t) := by
    have := Real.exp_pos (2 * Real.pi * t)
    linarith
  have hprod0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂ :=
    mul_nonneg hS0 hM0
  have hterm1 : C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
        * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
      ≤ (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂
          * (1 + Real.exp (2 * Real.pi * t)) := by
    have hA : C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ := by
      have h0 : (0 : ℝ) ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ := by positivity
      calc C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
          ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ * 1 :=
            mul_le_mul_of_nonneg_left hexp1 h0
        _ = C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ := by ring
    have hB : C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
        ≤ (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂ := by
      calc C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
          = C₁ * ((Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁) := by ring
        _ ≤ (C₁ + C₂) * ((Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂) :=
            mul_le_mul (by linarith : C₁ ≤ C₁ + C₂)
              (mul_le_mul hSN₁ hSM₁ hM10 hS0)
              (mul_nonneg (Real.rpow_nonneg hsw _) hM10) (by positivity)
        _ = (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂ := by ring
    exact hA.trans (hB.trans (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ C₁ + C₂) hS0) hM0) hE1))
  have hterm2 : C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t) ^ M₂
        * (1 + Real.exp (2 * Real.pi * t))
      ≤ (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂
          * (1 + Real.exp (2 * Real.pi * t)) := by
    have hB : C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t) ^ M₂
        ≤ (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂ := by
      calc C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t) ^ M₂
          = C₂ * ((Work.Kernels.scale w) ^ N₂ * (1 + t) ^ M₂) := by ring
        _ ≤ (C₁ + C₂) * ((Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂) :=
            mul_le_mul (by linarith : C₂ ≤ C₁ + C₂)
              (mul_le_mul hSN₂ hSM₂ hM20 hS0)
              (mul_nonneg (Real.rpow_nonneg hsw _) hM20) (by positivity)
        _ = (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂ := by ring
    exact mul_le_mul_of_nonneg_right hB (by positivity)
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      = ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Aexp (Gcusp ℓ d) w t) + Aexp (Gcusp ℓ d) w t‖ := by ring_nf
    _ ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
          + ‖Aexp (Gcusp ℓ d) w t‖ := norm_add_le _ _
    _ ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        + C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t) ^ M₂
          * (1 + Real.exp (2 * Real.pi * t)) := add_le_add hdev hmod
    _ ≤ (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂
          * (1 + Real.exp (2 * Real.pi * t))
        + (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂
          * (1 + Real.exp (2 * Real.pi * t)) := add_le_add hterm1 hterm2
    _ = 2 * (C₁ + C₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t) ^ max M₁ M₂
          * (1 + Real.exp (2 * Real.pi * t)) := by ring

end Work.Asymptotics
