import Mathlib.Analysis.Fourier.AddCircle

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- **Plancherel for a bounded measurable multiplier on the circle.**  For a bounded measurable
`m : ℝ → ℂ` and a square-integrable periodic `g`,

`∑'_n ‖∫_{[0,1]} m(θ) g(θ) e(-2πi n θ) dθ‖² = ∫_{[0,1]} ‖m(θ)‖² ‖g(θ)‖² dθ`.

This is the `L²(𝕋)` isometry that converts operator-norm statements for a multiplier `m` into
weighted `L²`-estimates on the Fourier side; it is the tool behind the "square-function"
reduction of maximal multiplier inequalities to pointwise bounds on the symbols. -/
theorem multiplier_plancherel_circle (m g : ℝ → ℂ) (hm : Measurable m)
    (hmb : ∃ C : ℝ, ∀ θ, ‖m θ‖ ≤ C)
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    ∑' n : ℤ, ‖∫ θ in (0:ℝ)..1, m θ * g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))‖^2
      = ∫ θ in (0:ℝ)..1, ‖m θ‖^2 * ‖g θ‖^2 := by
  have hab : (0:ℝ) < 1 := by norm_num
  obtain ⟨C, hC⟩ := hmb
  -- The bounded measurable multiplier is essentially bounded, hence in `L∞`, so the product
  -- `m * g` is again square integrable.
  have hm_top : MemLp m ⊤ (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound (p := ⊤) hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hhmg : MemLp (fun θ => m θ * g θ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.ae_eq (ae_of_all _ fun θ => mul_comm (g θ) (m θ)) (hg.mul' hm_top)
  -- The interval integrals are exactly the Fourier coefficients of `m * g` on `[0,1]`.
  have key : ∀ n : ℤ, ∫ θ in (0:ℝ)..1, m θ * g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
      = fourierCoeffOn hab (fun θ => m θ * g θ) n := by
    intro n
    have hfourier : ∀ x : ℝ, fourier (-n) (x : AddCircle (1-0:ℝ))
        = Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(x:ℂ))) := by
      intro x
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring
    rw [fourierCoeffOn_eq_integral]
    rw [show (1:ℝ) / ((1:ℝ) - (0:ℝ)) = 1 by norm_num, one_smul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [smul_eq_mul]
    rw [hfourier]
    ring
  simp_rw [key]
  -- Parseval/Plancherel for the circle on `[0,1]`.
  rw [tsum_sq_fourierCoeffOn hab hhmg]
  rw [show ((1:ℝ) - 0)⁻¹ = 1 by norm_num, one_smul]
  apply intervalIntegral.integral_congr
  intro x hx
  -- `‖m x * g x‖² = ‖m x‖² * ‖g x‖²`.
  simp only [norm_mul, mul_pow]

end Commons.Analysis.Fourier