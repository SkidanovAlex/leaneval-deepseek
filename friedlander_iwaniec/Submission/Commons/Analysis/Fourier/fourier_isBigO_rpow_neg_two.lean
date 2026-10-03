import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Fourier

open MeasureTheory Filter Asymptotics
open scoped FourierTransform Topology ContDiff

/-- For a real number `x`, `|x| ^ (-2)` can be written as `(x ^ 2)⁻¹`. -/
lemma abs_rpow_neg_two (x : ℝ) : |x| ^ (-(2:ℝ)) = ((x:ℝ)^2)⁻¹ := by
  rw [Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]

/-- The `n`-th derivative of a compactly supported function `ℝ → ℂ` again has compact support. -/
lemma HasCompactSupport.iteratedDeriv {f : ℝ → ℂ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (hf.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)

/-- The norm of `2 * π * I * x` as a complex number is `2 * π * |x|`. -/
lemma norm_two_pi_I_mul (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x:ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi:ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

/-- The Fourier transform of a twice continuously differentiable compactly supported function
`F : ℝ → ℂ` decays like `|x| ^ (-2)` at infinity. -/
theorem fourier_isBigO_rpow_neg_two {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) :
    Asymptotics.IsBigO (Filter.cocompact ℝ) (FourierTransform.fourier F)
      (fun x : ℝ => |x| ^ (-(2:ℝ))) := by
  -- all derivatives of `F` up to order `2` are integrable
  have hint : ∀ n : ℕ, n ≤ 2 → Integrable (iteratedDeriv n F) := by
    intro n hn
    have h : ContDiff ℝ (↑n) F := hF.of_le (by exact_mod_cast hn)
    exact (h.continuous_iteratedDeriv' n).integrable_of_hasCompactSupport
      (HasCompactSupport.iteratedDeriv hc n)
  -- integrate by parts twice: `𝓕 F'' = (2πI·)² • 𝓕 F`
  have hfourier := Real.fourier_iteratedDeriv (f := F) (N := (2:ℕ∞)) hF
    (fun n hn => hint n (by exact_mod_cast hn)) (n := 2) le_rfl
  have hfourier' : ∀ x : ℝ,
      𝓕 (iteratedDeriv 2 F) x = (2 * Real.pi * Complex.I * (x:ℂ)) ^ 2 • (𝓕 F x) :=
    fun x => congrFun hfourier x
  -- `C` bounds the Fourier transform of `F''` uniformly
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 F y‖ with hCdef
  have hCbound (x : ℝ) : ‖𝓕 (iteratedDeriv 2 F) x‖ ≤ C := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq hCdef.symm
  have hnorm (x : ℝ) :
      ‖(2 * Real.pi * Complex.I * (x:ℂ)) ^ 2‖ = 4 * Real.pi^2 * x^2 := by
    rw [norm_pow, norm_two_pi_I_mul x, mul_pow, sq_abs]
    ring
  have hkey (x : ℝ) : ‖(2 * Real.pi * Complex.I * (x:ℂ)) ^ 2 • (𝓕 F x)‖ ≤ C := by
    rw [← hfourier' x]
    exact hCbound x
  -- hence `‖𝓕 F x‖ ≤ (C / (4π²)) * |x| ^ (-2)` for `x ≠ 0`
  have hfinal (x : ℝ) (hx : x ≠ 0) :
      ‖𝓕 F x‖ ≤ (C / (4 * Real.pi^2)) * |x| ^ (-(2:ℝ)) := by
    have hpos : (0:ℝ) < 4 * Real.pi^2 * x^2 := by
      have : (0:ℝ) < x^2 := by positivity
      positivity
    have h1 : ‖𝓕 F x‖ * (4 * Real.pi^2 * x^2) ≤ C := by
      have hh := hkey x
      rw [norm_smul, hnorm x] at hh
      calc ‖𝓕 F x‖ * (4 * Real.pi^2 * x^2) = 4 * Real.pi^2 * x^2 * ‖𝓕 F x‖ := by ring
        _ ≤ C := hh
    have h2 : ‖𝓕 F x‖ ≤ C / (4 * Real.pi^2 * x^2) := (le_div_iff₀ hpos).mpr h1
    refine h2.trans (le_of_eq ?_)
    rw [abs_rpow_neg_two x, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  rw [Asymptotics.isBigO_iff]
  refine ⟨C / (4 * Real.pi^2), ?_⟩
  have hne : ∀ᶠ x : ℝ in Filter.cocompact ℝ, x ≠ 0 :=
    Filter.Eventually.filter_mono Filter.cocompact_le_cofinite (Filter.eventually_cofinite_ne 0)
  filter_upwards [hne] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  exact hfinal x hx

end Commons.Analysis.Fourier