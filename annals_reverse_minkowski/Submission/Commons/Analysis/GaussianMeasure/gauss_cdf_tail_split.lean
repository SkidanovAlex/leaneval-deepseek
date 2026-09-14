import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Commons.Analysis.GaussianMeasure

/-- Splitting the real line at `t` for the one-dimensional Gaussian density
`x ↦ exp (-π x²)` (total mass 1): the mass left of `t` plus the mass right of `t` equals 1:

    ∫ x in Set.Iio t, exp (-π x²) + ∫ x in Set.Ioi t, exp (-π x²) = 1.

(At the single point `t` the density contributes nothing to the Lebesgue integral.)
PROOF OUTLINE: `ℝ = Iio t ∪ {t} ∪ Ioi t` (disjoint, up to the null point `{t}`); use
`integral_gaussian` (`∫ x : ℝ, exp (-π x²) = 1`) and additivity of the set integral over the
disjoint union, or equivalently `intervalIntegral`-style splitting
`∫ x in Iio t, f + ∫ x in Ioi t, f = ∫ x : ℝ, f`. -/
theorem gauss_cdf_tail_split (t : ℝ) :
    (∫ x in Set.Iio t, Real.exp (-Real.pi * x ^ 2)) +
        (∫ x in Set.Ioi t, Real.exp (-Real.pi * x ^ 2)) = 1 := by
  let f : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  -- The density is integrable and integrates to 1 on the whole line.
  have hf_int : Integrable f := by
    dsimp [f]
    exact integrable_exp_neg_mul_sq Real.pi_pos
  have htot : (∫ x : ℝ, f x) = 1 := by
    dsimp [f]
    rw [integral_gaussian]
    have hsq : Real.sqrt (Real.pi / Real.pi) = 1 := by
      rw [div_self (ne_of_gt Real.pi_pos)]
      simp
    exact hsq
  -- The single point `t` carries no Lebesgue mass, so `Iio t` and `Iic t` give equal integrals.
  have hleft : (∫ x in Set.Iic t, f x) = ∫ x in Set.Iio t, f x := by
    exact MeasureTheory.integral_Iic_eq_integral_Iio (μ := (volume : Measure ℝ))
      (x := t) (f := f)
  -- `Ioi t` is the complement of `Iic t`.
  have hcomp_set : (Set.Iic t)ᶜ = Set.Ioi t := by
    ext x
    simp [Set.Ioi]
  have hcompl : (∫ x in Set.Ioi t, f x) = (∫ x : ℝ, f x) - ∫ x in Set.Iic t, f x := by
    rw [← hcomp_set]
    exact MeasureTheory.setIntegral_compl (μ := (volume : Measure ℝ)) measurableSet_Iic hf_int
  -- Conclude: left tail + right tail = full integral = 1.
  have hsplit : (∫ x in Set.Iio t, f x) + (∫ x in Set.Ioi t, f x) = 1 := by
    calc
      (∫ x in Set.Iio t, f x) + (∫ x in Set.Ioi t, f x)
          = (∫ x in Set.Iic t, f x) + (∫ x in Set.Ioi t, f x) := by
              rw [← hleft]
      _ = (∫ x : ℝ, f x) := by
              rw [hcompl]
              abel
      _ = 1 := htot
  simpa [f] using hsplit

end Commons.Analysis.GaussianMeasure
