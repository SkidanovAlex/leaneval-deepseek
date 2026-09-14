import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section

open MeasureTheory Set
open scoped Real Interval

namespace Commons.Analysis.GaussianMeasure

/-- The cumulative one-dimensional Gaussian distribution function
`t ↦ ∫_{x ≤ t} exp (-π x²)` is strictly increasing: a strictly larger upper limit adds
strictly positive mass, since the density `x ↦ exp (-π x²)` is everywhere positive.

PROOF OUTLINE. Let `C t := ∫ x in Iic t, exp (-π x²)`.  Additivity of the Lebesgue
integral gives `C t = C 0 + ∫ x in 0..t, exp (-π x²)` (`integral_Iic_sub_Iic`), and the
fundamental theorem of calculus (`Continuous.deriv_integral`) gives
`deriv C t = exp (-π t²) > 0` at every `t`.  By `strictMono_of_deriv_pos`, `C` is strictly
monotone. -/
theorem gaussian_cdf_strictMono :
    StrictMono (fun t : ℝ => ∫ x : ℝ in {x : ℝ | x ≤ t}, Real.exp (-Real.pi * x ^ 2)) := by
  let g : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let C : ℝ → ℝ := fun t => ∫ x : ℝ in Set.Iic t, g x
  have hg_cont : Continuous g := by
    dsimp [g]
    continuity
  have hg_int : Integrable g := by
    dsimp [g]
    exact integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
  -- `C t = C 0 + ∫_{0}^{t} g`, by additivity of the integral over `Iic 0` and `Ioc 0 t`.
  have hsplit (t : ℝ) : C t = C (0 : ℝ) + (∫ x : ℝ in 0..t, g x) := by
    have hsub : (∫ x : ℝ in Set.Iic t, g x) - (∫ x : ℝ in Set.Iic (0 : ℝ), g x) = ∫ x : ℝ in 0..t, g x := by
      exact intervalIntegral.integral_Iic_sub_Iic (μ := (volume : Measure ℝ)) (a := (0 : ℝ))
        (b := t) (f := g) (hg_int.integrableOn) (hg_int.integrableOn)
    dsimp [C]
    linarith
  -- FTC-1: the interval-integral primitive has derivative `g`.
  have hPderiv (t : ℝ) : deriv (fun u : ℝ => ∫ x : ℝ in 0..u, g x) t = g t := by
    exact Continuous.deriv_integral g hg_cont 0 t
  -- Hence `deriv C = g > 0`, so `C` is strictly monotone.
  have hderiv_pos : ∀ t : ℝ, 0 < deriv C t := by
    intro t
    have hfun : (fun u : ℝ => C (0 : ℝ) + ∫ x : ℝ in 0..u, g x) = C := by
      funext u
      exact (hsplit u).symm
    rw [← hfun]
    rw [deriv_const_add]
    rw [hPderiv t]
    dsimp [g]
    exact Real.exp_pos _
  have hC_strict : StrictMono C := strictMono_of_deriv_pos hderiv_pos
  -- Unfold the definitions to reach the statement with `{x : ℝ | x ≤ t}`.
  change StrictMono (fun t : ℝ => ∫ x : ℝ in Set.Iic t, g x)
  simpa [C] using hC_strict

end Commons.Analysis.GaussianMeasure