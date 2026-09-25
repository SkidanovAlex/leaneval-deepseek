import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.SpecialFunctions.Log

open Filter Topology SummationFilter

/-- **The logarithm of an infinite product of positive reals is the sum of the logarithms.**

If `r : ι → ℝ` is a family of positive reals whose finite products converge to a positive real
`L` (`HasProd r L`), then `Real.log L = ∑' i, Real.log (r i)`.  This is the real-valued
counterpart of `EulerProduct.exp_tsum_primes_log_eq_tsum`. -/
theorem log_eq_tsum_log_of_hasProd {ι : Type*} {r : ι → ℝ} {L : ℝ}
    (h : HasProd r L) (hr : ∀ i, 0 < r i) (hL : 0 < L) :
    Real.log L = ∑' i, Real.log (r i) := by
  have hsum : HasSum (fun i => Real.log (r i)) (Real.log L) := by
    have hcomp : Tendsto (Real.log ∘ fun s : Finset ι => ∏ b ∈ s, r b)
        (unconditional ι).filter (𝓝 (Real.log L)) :=
      (Real.continuousAt_log (ne_of_gt hL)).tendsto.comp h
    refine hcomp.congr' ?_
    filter_upwards with s
    rw [Function.comp_apply, Real.log_prod]
    exact fun i _ => ne_of_gt (hr i)
  rw [← hsum.tsum_eq]

end Commons.Analysis.SpecialFunctions.Log