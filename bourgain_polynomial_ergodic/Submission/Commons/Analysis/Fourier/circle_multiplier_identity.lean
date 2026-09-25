import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators

/-- The circle character `θ ↦ e(2πi k θ)` on `ℝ`, written in the form used below
(`e(-2πi k θ)` with the sign pushed to the front). -/
lemma continuous_circle_char (k : ℤ) :
    Continuous (fun θ : ℝ => Complex.exp (-(2*Real.pi*Complex.I*((k:ℤ):ℂ)*(θ:ℂ)))) := by
  apply Complex.continuous_exp.comp
  continuity

/-- A measurable indicator (by a measurable set) of a continuous function is interval
integrable on any bounded interval; here on `[0,1]`. -/
lemma intervalIntegrable_indicator_of_continuous {R : Set ℝ} (hR : MeasurableSet R)
    {g : ℝ → ℂ} (hg : Continuous g) :
    IntervalIntegrable (fun θ => Set.indicator R g θ) volume 0 1 := by
  rw [intervalIntegrable_iff]
  have hfin : volume (Set.uIoc (0:ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono _) (measure_Icc_lt_top (a := (0:ℝ)) (b := 1))
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := g) hg.continuousOn
  refine IntegrableOn.of_bound hfin ?_ C ?_
  · exact (hg.measurable.indicator hR).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    refine le_trans (norm_indicator_le_norm_self g x) ?_
    apply hC
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    exact Set.Ioc_subset_Icc_self hx

/-- Additivity of the exponential turns the product of the `n`-th and `-m`-th characters
into the `(n-m)`-th (equivalently `-(m-n)`-th) character. -/
lemma exp_mul_exp_eq (n m : ℤ) (θ : ℝ) :
    Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)) * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))
      = Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The circle multiplier identity.**  For a measurable set `R ⊆ ℝ`, a finitely supported
`f : ℤ → ℂ` and `m : ℤ`, the discrete convolution of `f` against the Fourier coefficients of
`1_R` equals the integral over `[0,1]` of `1_R` against the product of the trig polynomial of
`f` with the character `e(-2πi m ·)`:

`∑_n f n · (∫_{[0,1]} 1_R(θ) e(-2πi (m-n) θ) dθ) = ∫_{[0,1]} 1_R(θ) · (∑_n f n e(2πi n θ)) ·
e(-2πi m θ) dθ`.

This is the identity that identifies the operator `P f (m) = ∑_n f n K(m-n)` (with
`K(p) = ∫_{[0,1]} 1_R(θ) e(-2πi p θ) dθ`) with the multiplier operator `1_R` on the circle. -/
theorem circle_multiplier_identity (R : Set ℝ) (hR : MeasurableSet R) (f : ℤ → ℂ) (s : Finset ℤ)
    (m : ℤ) :
    (∑ n ∈ s, f n * (∫ θ in (0:ℝ)..1,
        Set.indicator R (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ))
      = ∫ θ in (0:ℝ)..1,
          Set.indicator R (fun θ => (∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
            * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))) θ := by
  -- Step 1: the integrand on the right is pointwise the finite sum of the integrands on the left.
  have hpt : ∀ θ : ℝ,
      Set.indicator R (fun θ => (∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
            * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))) θ
        = ∑ n ∈ s, f n * Set.indicator R (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ := by
    intro θ
    by_cases hθ : θ ∈ R
    · rw [Set.indicator_of_mem hθ, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Set.indicator_of_mem hθ, mul_assoc, exp_mul_exp_eq n m θ]
    · rw [Set.indicator_of_notMem hθ]
      symm
      apply Finset.sum_eq_zero
      intro n hn
      rw [Set.indicator_of_notMem hθ, mul_zero]
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  -- Step 2: pull the finite sum out of the interval integral and commute the constants.
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul]
  · intro n hn
    exact (intervalIntegrable_indicator_of_continuous hR (continuous_circle_char (m - n))).const_mul (f n)

end Commons.Analysis.Fourier