import Mathlib
import Submission.Commons.Analysis.Fourier.perron_kernel_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory
open scoped Interval ComplexConjugate

namespace Commons.Analysis.Fourier

/-! Truncated Perron kernel with a `σ`-shifted denominator:
`‖∫_{-T}^{T} e^{iαt} / (σ + it) dt‖ ≤ π + 2|α|T` for `σ > 0`, `T ≥ 0`.
Reduction: change variables `u = t/σ` and reuse `PerronKernel.abs_kern_le`. -/

lemma sigma_denom_ne_zero (a b : ℝ) (h : a ≠ 0) : (a : ℂ) + I * (b : ℂ) ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have : a = 0 := by simpa using hre
  exact h this

lemma sigma_one_add_I_mul_ne_zero (t : ℝ) : ((1 : ℂ) + I * (t : ℂ)) ≠ 0 := by
  exact sigma_denom_ne_zero 1 t (by norm_num)

/-- Pointwise scaling identity used for the change of variables `t = σu`. -/
lemma perronKernel_sigma_point (σ α t : ℝ) (hσ : σ ≠ 0) :
    cexp (I * (↑((α * σ) * (t / σ)) : ℂ)) / (1 + I * (↑(t / σ) : ℂ))
      = (σ : ℂ) * (cexp (I * (↑α * ↑t : ℂ)) / ((σ : ℂ) + I * (↑t : ℂ))) := by
  have harg : (α * σ) * (t / σ) = α * t := by
    field_simp [hσ]
  let A : ℂ := (σ : ℂ)
  let B : ℂ := 1 + I * (↑(t / σ) : ℂ)
  let C : ℂ := (σ : ℂ) + I * (↑t : ℂ)
  have hA : A ≠ 0 := by dsimp [A]; exact_mod_cast hσ
  have hB : B ≠ 0 := sigma_one_add_I_mul_ne_zero (t / σ)
  have hC : C ≠ 0 := sigma_denom_ne_zero σ t hσ
  have hσt : A * (I * (↑(t / σ) : ℂ)) = I * (↑t : ℂ) := by
    dsimp [A]
    calc
      (σ : ℂ) * (I * (↑(t / σ) : ℂ)) = I * ((σ : ℂ) * (↑(t / σ) : ℂ)) := by ring
      _ = I * (↑(σ * (t / σ)) : ℂ) := by rw [← Complex.ofReal_mul]
      _ = I * (↑t : ℂ) := by
        congr 2
        field_simp [hσ]
  have hdenprod : A * B = C := by
    dsimp [A, B, C]
    rw [mul_add, mul_one]
    rw [hσt]
  have hfrac : B⁻¹ = A * C⁻¹ := by
    field_simp [hB, hC]
    rw [mul_comm, hdenprod]
  calc
    cexp (I * (↑((α * σ) * (t / σ)) : ℂ)) / B
        = cexp (I * (↑α * ↑t : ℂ)) * B⁻¹ := by
        rw [div_eq_mul_inv]
        congr 1
        rw [harg]
        congr 1
        rw [← Complex.ofReal_mul]
    _ = cexp (I * (↑α * ↑t : ℂ)) * (A * C⁻¹) := by rw [hfrac]
    _ = A * (cexp (I * (↑α * ↑t : ℂ)) * C⁻¹) := by ring
    _ = A * (cexp (I * (↑α * ↑t : ℂ)) / C) := by
        rw [div_eq_mul_inv]
    _ = (σ : ℂ) * (cexp (I * (↑α * ↑t : ℂ)) / ((σ : ℂ) + I * (↑t : ℂ))) := by
        dsimp [A, C]

open intervalIntegral

/-- The `σ`-denominator truncated Perron integral equals the standard
`(1 + it)`-denominator kernel with scaled arguments. -/
lemma perronKernel_sigma_eq_kern (σ T α : ℝ) (hσ : 0 < σ) :
    (∫ t in -T..T, cexp (I * (↑α * ↑t : ℂ)) / ((σ : ℂ) + I * (↑t : ℂ)))
      = PerronKernel.kern (T / σ) (α * σ) := by
  let F0 : ℝ → ℂ := fun u => cexp (I * (↑((α * σ) * u) : ℂ)) / (1 + I * (↑u : ℂ))
  let F : ℝ → ℂ := fun t => cexp (I * (↑α * ↑t : ℂ)) / ((σ : ℂ) + I * (↑t : ℂ))
  have hpt : ∀ t : ℝ, F0 (t / σ) = (σ : ℂ) * F t := by
    intro t
    simpa [F0, F] using perronKernel_sigma_point σ α t hσ.ne'
  have hsub := intervalIntegral.integral_comp_div (f := F0) (a := -T) (b := T) (c := σ) (hc := hσ.ne')
  have hlhs : (∫ x in -T..T, F0 (x / σ)) = (σ : ℂ) * (∫ x in -T..T, F x) := by
    calc
      (∫ x in -T..T, F0 (x / σ)) = ∫ x in -T..T, (σ : ℂ) * F x := by
        apply intervalIntegral.integral_congr (μ := volume)
        intro x hx
        exact hpt x
      _ = (σ : ℂ) * (∫ x in -T..T, F x) := by
        rw [intervalIntegral.integral_const_mul]
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hcancel : (∫ x in (-T) / σ..T / σ, F0 x) = ∫ x in -T..T, F x := by
    have hsmul : (σ : ℝ) • (∫ x in (-T) / σ..T / σ, F0 x) = (σ : ℂ) * (∫ x in -T..T, F x) := by
      calc
        (σ : ℝ) • (∫ x in (-T) / σ..T / σ, F0 x) = ∫ x in -T..T, F0 (x / σ) := by
          simpa [mul_comm] using hsub.symm
        _ = (σ : ℂ) * (∫ x in -T..T, F x) := hlhs
    have hsmul' : (σ : ℂ) * (∫ x in (-T) / σ..T / σ, F0 x) = (σ : ℂ) * (∫ x in -T..T, F x) := by
      simpa using hsmul
    exact mul_left_cancel₀ hσc hsmul'
  have hbnds : (∫ x in (-T) / σ..T / σ, F0 x) = ∫ x in -(T / σ)..T / σ, F0 x := by
    congr 1
    ring
  have hptk : ∀ x : ℝ, F0 x = cexp (I * (↑(α * σ) * ↑x : ℂ)) / (1 + I * (↑x : ℂ)) := by
    intro x
    dsimp [F0]
    rw [Complex.ofReal_mul]
  have hkern0 : (∫ x in -(T / σ)..(T / σ), F0 x)
      = ∫ x in -(T / σ)..(T / σ), cexp (I * (↑(α * σ) * ↑x : ℂ)) / (1 + I * (↑x : ℂ)) := by
    apply intervalIntegral.integral_congr (μ := volume)
    intro x hx
    exact hptk x
  calc
    (∫ t in -T..T, cexp (I * (↑α * ↑t : ℂ)) / ((σ : ℂ) + I * (↑t : ℂ)))
        = ∫ t in -T..T, F t := rfl
    _ = ∫ x in (-T) / σ..T / σ, F0 x := hcancel.symm
    _ = ∫ x in -(T / σ)..T / σ, F0 x := by rw [hbnds]
    _ = ∫ x in -(T / σ)..(T / σ), cexp (I * (↑(α * σ) * ↑x : ℂ)) / (1 + I * (↑x : ℂ)) := hkern0
    _ = PerronKernel.kern (T / σ) (α * σ) := rfl

theorem perronKernelSigma_regionBound (σ T α : ℝ) (hσ : 0 < σ) (hT : 0 ≤ T) :
    ‖(∫ (t : ℝ) in -T..T, Complex.exp (Complex.I * (↑α * ↑t)) / ((σ : ℂ) + Complex.I * ↑t))‖ ≤
      Real.pi + 2 * |α| * T := by
  rw [perronKernel_sigma_eq_kern σ T α hσ]
  have hT' : 0 ≤ T / σ := div_nonneg hT (le_of_lt hσ)
  have hb := PerronKernel.abs_kern_le (T / σ) (α * σ) hT'
  have hsc : |α * σ| * (T / σ) = |α| * T := by
    calc
      |α * σ| * (T / σ) = (|α| * σ) * (T / σ) := by rw [abs_mul, abs_of_pos hσ]
      _ = |α| * T := by
        field_simp [hσ.ne']
  calc
    ‖PerronKernel.kern (T / σ) (α * σ)‖ ≤ Real.pi + 2 * |α * σ| * (T / σ) := hb
    _ = Real.pi + 2 * (|α * σ| * (T / σ)) := by ring
    _ = Real.pi + 2 * (|α| * T) := by rw [hsc]
    _ = Real.pi + 2 * |α| * T := by ring

end Commons.Analysis.Fourier
