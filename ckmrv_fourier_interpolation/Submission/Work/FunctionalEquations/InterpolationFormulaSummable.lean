import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs
import Submission.Work.Sampling.summable_norm_mul_pow_samples
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth

/-!
# Summability of the interpolation formula

CKMRV Theorem 3.1 concludes that every radial Schwartz function `f` is the sum of its
samples against the interpolation basis, `f = ∑ᵢ (coeffs f i) • basis i`.  This file
supplies the elementary analytic input: for each `f` and each point `x`, the complex
series

`i ↦ (coeffs n 1 f i) * (basis i) x`

is summable.

The two ingredients are already available in the workspace:

* the samples of a Schwartz function are *rapidly decreasing*
  (`Work.Sampling.rapidlyDecreasing_coeffs`), so that multiplying their norms by any
  polynomial weight keeps them summable
  (`Work.Sampling.summable_norm_mul_pow_samples`);
* the Schwartz seminorms of the basis grow at most polynomially, which bounds the values
  `(basis i) x` by a polynomial in the index
  (`InterpolationSolution.growth_seminorm` together with
  `SchwartzMap.norm_le_seminorm`).

The product of a rapidly decreasing sequence with a polynomially bounded one is
summable, since the decay can be taken to beat any fixed power.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

theorem InterpolationFormulaSummable {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (f : RSch n) (x : E n) :
    Summable fun i : SampleIdx 1 => (coeffs n 1 f.1 i) * (S.basis i).1 x := by
  -- The value of the basis at `x` is bounded by the polynomial growth of its seminorms.
  obtain ⟨C, N, hC, hgrowth⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  have hbasis : ∀ i : SampleIdx 1, ‖(S.basis i).1 x‖ ≤ C * ((i.1.1 : ℝ) + 1) ^ N := fun i =>
    le_trans (SchwartzMap.norm_le_seminorm ℂ (S.basis i).1 x) (hgrowth i.1 i.2)
  -- The rapidly decreasing samples, weighted by the same polynomial, stay summable.
  have hweight : Summable fun i : SampleIdx 1 =>
      ‖coeffs n 1 f.1 i‖ * ((i.1.1 : ℝ) + 1) ^ N :=
    Work.Sampling.summable_norm_mul_pow_samples 1 N (coeffs n 1 f.1)
      (Work.Sampling.rapidlyDecreasing_coeffs n 1 f.1)
  refine Summable.of_norm_bounded (Summable.mul_left C hweight) fun i => ?_
  rw [norm_mul]
  calc ‖coeffs n 1 f.1 i‖ * ‖(S.basis i).1 x‖
      ≤ ‖coeffs n 1 f.1 i‖ * (C * ((i.1.1 : ℝ) + 1) ^ N) :=
        mul_le_mul_of_nonneg_left (hbasis i) (norm_nonneg _)
    _ = C * (‖coeffs n 1 f.1 i‖ * ((i.1.1 : ℝ) + 1) ^ N) := by ring

end Work.FunctionalEquations
