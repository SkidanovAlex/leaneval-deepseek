import Mathlib

/-!
# The multiplier of a polynomial-curve average

For a real polynomial `q` and a scale `n : ℕ` the `n`-th curve average of a band-limited function
`Ψ` is `y ↦ ∫ t in (0,1], Ψ (y + q (2 ^ n * t))`.  Its Fourier multiplier is the bounded continuous
function

`curveMultiplier q n ξ = ∫ t in (0,1], exp (2 π i ξ q (2 ^ n t))`.

Since the modulus of the exponential is `1`, the multiplier is bounded by `1`; this is what makes
the amplitude `ξ ↦ W ξ * curveMultiplier q n ξ` integrable whenever `W` is, and hence allows the
`L¹`-free lattice comparison `lattice_sup_le_integral_sup_band_limited_fourierInv_rpow` to be
applied to the family of curve averages.
-/

open MeasureTheory
open scoped ENNReal BigOperators FourierTransform

namespace Work.BourgainPlan.Maximal

/-- The Fourier multiplier of the `n`-th curve average of the polynomial `q`. -/
noncomputable def curveMultiplier (q : Polynomial ℝ) (n : ℕ) (ξ : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, Complex.exp (↑(2 * Real.pi * (ξ * q.eval ((2:ℝ)^n * t))) * Complex.I)

/-- The multiplier of a curve average is continuous. -/
lemma continuous_curveMultiplier (q : Polynomial ℝ) (n : ℕ) : Continuous (curveMultiplier q n) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := (volume : Measure ℝ)) (a₀ := (0:ℝ)) (s := fun _ : ℝ => (1:ℝ))
    (f := fun ξ t => Complex.exp (↑(2 * Real.pi * (ξ * q.eval ((2:ℝ)^n * t))) * Complex.I))
    (by fun_prop) continuous_const
  exact h

/-- The curve multiplier is bounded by `1`. -/
lemma norm_curveMultiplier_le_one (q : Polynomial ℝ) (n : ℕ) (ξ : ℝ) :
    ‖curveMultiplier q n ξ‖ ≤ 1 := by
  rw [curveMultiplier, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [show (∫ t in Set.Ioc (0:ℝ) 1,
        ‖Complex.exp (↑(2 * Real.pi * (ξ * q.eval ((2:ℝ)^n * t))) * Complex.I)‖)
      = ∫ _t in Set.Ioc (0:ℝ) 1, (1:ℝ) from by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (ξ * q.eval ((2:ℝ)^n * t)))]
  rw [setIntegral_const]
  simp [Measure.real, Real.volume_Ioc]

end Work.BourgainPlan.Maximal
