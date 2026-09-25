import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.lr_mixing
import Submission.Work.LT.sqrt_mul_le_half

namespace Work.LT

/-- Mixed pair bound for the right walk: for a mean-zero `b` the bilinear form against the
normalised right walk of `b` is bounded by `μ` times the sum of the two `ℓ²` masses.
This is `lrMixing_cauchy_schwarz` combined with the arithmetic–geometric mean inequality. -/
theorem lr_pair_bound_right {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (μ : ℝ)
    (hμ : 0 ≤ μ) (hB : rightExpander B μ) (a b : G → ℝ) (hb : ∑ g, b g = 0) :
    2 * (∑ g, a g * ((∑ j : Fin Δ, b (g * B j)) / (Δ : ℝ)))
      ≤ μ * ((∑ g, a g ^ 2) + ∑ g, b g ^ 2) := by
  have hsa : 0 ≤ ∑ g, a g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg (a g))
  have hsb : 0 ≤ ∑ g, b g ^ 2 := Finset.sum_nonneg (fun g _ => sq_nonneg (b g))
  have hcs := lrMixing_cauchy_schwarz B μ hμ hB a b hb
  have hsqrt := sqrt_mul_le_half hsa hsb
  have hs0 : 0 ≤ Real.sqrt ((∑ g, a g ^ 2) * (∑ g, b g ^ 2)) := Real.sqrt_nonneg _
  nlinarith [hcs, hsqrt, hμ, hs0, mul_nonneg hμ hs0, mul_nonneg (by linarith : (0:ℝ) ≤ μ) hs0]

end Work.LT
