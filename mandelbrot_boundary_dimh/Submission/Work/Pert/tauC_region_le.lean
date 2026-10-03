import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.norm_psi_sub_one_le
import Submission.Work.Pert.norm_div_one_sub_exp_neg_le
import Submission.Work.Pert.tauC_factor

namespace Work.Pert

/-- PERT (4.2.5) brick.  On the disc `‖ζ‖ ≤ 3η` the universal cover `τ_f = tauC σ α` satisfies
`‖τ_f ζ‖ ≤ 1.05/‖ζ‖`, uniformly.  Proof: `σ = (1-e^{2πiα})/u₀ = -(2πiα)·ψ/u₀` with `ψ = (e^x-1)/x`,
`x = 2πiα`; so `τ_f ζ = (ψ/u₀)·(xζ)/(1-e^{-xζ})·(1/ζ)` and for `‖xζ‖ ≤ 3/64` the middle factor has
modulus in `[0.953, 1]`, while `‖ψ‖ ≤ 1+3.3·10⁻⁵` and `‖u₀‖ ≥ 1-1/1024`. -/
theorem tauC_region_le {σ α u₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hη100 : 100 ≤ η) (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hu₀ : ‖u₀ - 1‖ ≤ 1 / 1024)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    (heq : 1 - σ * u₀ = Complex.exp (2 * Real.pi * Complex.I * α)) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 3 * η → ‖Work.Pert.tauC σ α ζ‖ ≤ 1.05 / ‖ζ‖ := by
  intro ζ hζ
  -- The only point of the disc where `τ_f` has no pole argument is `ζ = 0`, where `τ_f 0 = 0`.
  by_cases hζ0 : ζ = 0
  · rw [hζ0]
    simp [Work.Pert.tauC]
  · -- Set `x = 2πiα`; `set` also rewrites `2πiα` inside `heq`.
    set x : ℂ := 2 * Real.pi * Complex.I * α with hxdef
    have htau : Work.Pert.tauC σ α ζ = σ / (1 - Complex.exp (-(x * ζ))) := by
      rw [Work.Pert.tauC, ← hxdef]
    have hxnorm : ‖x‖ = 2 * Real.pi * ‖α‖ := by
      rw [hxdef, norm_mul, norm_mul, norm_mul]
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_I, mul_one]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hx_ne : x ≠ 0 := by
      have hpos : 0 < ‖x‖ := by rw [hxnorm]; positivity
      exact norm_pos_iff.mp hpos
    -- `‖x‖ = 2π‖α‖ ≤ 1/6400`, from `2π‖α‖·η ≤ 1/64` and `η ≥ 100`.
    have hxnorm_le : ‖x‖ ≤ 1 / 6400 := by
      rw [hxnorm]
      nlinarith [hαη, hη100, Real.pi_pos, norm_nonneg α]
    have hx_le_half : ‖x‖ ≤ 1 / 2 := by linarith
    -- `‖x ζ‖ ≤ 2π‖α‖·3η = 3·(2π‖α‖η) ≤ 3/64`.
    have hxζ_le : ‖x * ζ‖ ≤ 3 / 64 := by
      rw [norm_mul, hxnorm]
      have hnn : 0 ≤ 2 * Real.pi * ‖α‖ := by positivity
      calc 2 * Real.pi * ‖α‖ * ‖ζ‖ ≤ 2 * Real.pi * ‖α‖ * (3 * η) :=
            mul_le_mul_of_nonneg_left hζ hnn
        _ = 3 * (2 * Real.pi * ‖α‖ * η) := by ring
        _ ≤ 3 * (1 / 64) := by linarith [hαη]
        _ = 3 / 64 := by norm_num
    by_cases hD : (1 : ℂ) - Complex.exp (-(x * ζ)) = 0
    · -- A pole of the denominator: in Lean `σ / 0 = 0`, and the right-hand side is nonnegative.
      rw [htau, hD, div_zero, norm_zero]
      exact div_nonneg (by norm_num) (norm_nonneg ζ)
    · have hxζ_ne : x * ζ ≠ 0 := by
        intro h; exact hD (by rw [h]; simp)
      have hζ_ne : ζ ≠ 0 := fun h => hxζ_ne (by rw [h, mul_zero])
      -- The normal-form relation in the form `σ u₀ = 1 - e^x`.
      have hσu : σ * u₀ = 1 - Complex.exp x := by
        calc σ * u₀ = 1 - (1 - σ * u₀) := by ring
          _ = 1 - Complex.exp x := by rw [heq]
      have hu₀_ne : u₀ ≠ 0 := by
        intro h
        rw [h] at hu₀
        simp at hu₀
        norm_num at hu₀
      -- The factorization `τ_f ζ = -(ψ/u₀)·(xζ/(1-e^{-xζ}))·(1/ζ)`.
      have hfac : Work.Pert.tauC σ α ζ
          = -(((Complex.exp x - 1) / x) / u₀)
              * ((x * ζ) / (1 - Complex.exp (-(x * ζ)))) * (1 / ζ) := by
        rw [htau]
        exact tauC_factor hu₀_ne hx_ne hζ_ne hD hσu
      -- `‖ψ‖ ≤ 1.001` with `ψ = (e^x - 1)/x`.
      have hψ : ‖(Complex.exp x - 1) / x‖ ≤ 1.001 := by
        have h := norm_psi_sub_one_le hx_ne hx_le_half
        have hsmall : 29 / 48 * ‖x‖ ≤ 0.001 := by
          nlinarith [hxnorm_le, norm_nonneg x]
        calc ‖(Complex.exp x - 1) / x‖ = ‖(Complex.exp x - 1) / x - 1 + 1‖ := by
              congr 1; ring
          _ ≤ ‖(Complex.exp x - 1) / x - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ 0.001 + 1 := by rw [norm_one]; linarith
          _ = 1.001 := by norm_num
      -- `‖u₀‖ ≥ 1023/1024 ≥ 0.999`.
      have hu₀_ge : (0.999 : ℝ) ≤ ‖u₀‖ := by
        have h := norm_sub_norm_le (1 : ℂ) u₀
        rw [norm_one, norm_sub_rev] at h
        linarith
      have hψu : ‖((Complex.exp x - 1) / x) / u₀‖ ≤ 1.001 / 0.999 := by
        rw [Complex.norm_div]
        exact div_le_div₀ (by norm_num) hψ (by norm_num) hu₀_ge
      -- The Laurent factor.
      have hratio : ‖(x * ζ) / (1 - Complex.exp (-(x * ζ)))‖ ≤ 1.04 :=
        norm_div_one_sub_exp_neg_le hxζ_ne hxζ_le
      have hkey : ‖Work.Pert.tauC σ α ζ‖ ≤ 1.05 * ‖ζ‖⁻¹ := by
        rw [hfac]
        simp only [norm_mul, norm_neg]
        calc ‖((Complex.exp x - 1) / x) / u₀‖
                * ‖(x * ζ) / (1 - Complex.exp (-(x * ζ)))‖ * ‖(1 / ζ : ℂ)‖
            ≤ (1.001 / 0.999) * 1.04 * ‖(1 / ζ : ℂ)‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul hψu hratio (norm_nonneg _) (by norm_num)
          _ = (1.001 / 0.999) * 1.04 * ‖ζ‖⁻¹ := by rw [one_div, norm_inv]
          _ ≤ 1.05 * ‖ζ‖⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              norm_num
      rw [div_eq_mul_inv]
      exact hkey

end Work.Pert
