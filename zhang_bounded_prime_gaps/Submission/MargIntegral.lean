import Mathlib
import Submission.MargProfile
import Submission.Commons.MeasureTheory.Integral.marginal_simplex_integral
import Submission.Commons.MeasureTheory.Integral.beta_integral_scaled

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open MeasureTheory Finset
open scoped BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- **The master shifted simplex integral.**

The marginal simplex integral of `(1+ε-Σt)^N` against a product of two labelled monomial sums
over the simplex `(1-ε)·R^k` is Polymath8a's `Ψ`-sum. -/
theorem simplex_integral_lmono_shifted {k : ℕ} {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1)
    (N : ℕ) (β β' : List ℕ) :
    ∫ t in {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
        (1 + eps - ∑ i, t i) ^ N * lmono β k t * lmono β' k t
      = ∑ jj ∈ Finset.range (N + 1), ((N.choose jj : ℕ) : ℝ) * (2 * eps) ^ jj *
          ((1 - eps) ^ (k + (N - jj) + β.sum + β'.sum) * ((N - jj).factorial : ℝ) *
            (Slab β β' k : ℝ) /
              ((((N - jj) + β.sum + β'.sum + k).factorial : ℕ) : ℝ)) := by
  have hc : (0:ℝ) < 1 - eps := by linarith
  have hpt : ∀ t : Fin k → ℝ, (1 + eps - ∑ i, t i) ^ N
      = ∑ jj ∈ Finset.range (N + 1), ((N.choose jj : ℕ) : ℝ) * (2 * eps) ^ jj *
          (1 - eps - ∑ i, t i) ^ (N - jj) := by
    intro t
    rw [show (1 + eps - ∑ i, t i) = (2 * eps) + (1 - eps - ∑ i, t i) from by ring, add_pow]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [mul_pow]
    ring
  have hmono : ∀ jj : ℕ, IntegrableOn (fun t : Fin k → ℝ =>
      (1 - eps - ∑ i, t i) ^ (N - jj) * lmono β k t * lmono β' k t)
      {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps} := by
    intro jj
    refine ((((continuous_const.sub (continuous_finsetSum Finset.univ
      (fun i _ => continuous_apply i))).pow (N - jj)).mul
      (continuous_lmono β k)).mul (continuous_lmono β' k)).continuousOn
      |>.integrableOn_compact (isCompact_simplexC k (1 - eps))
  have hval : ∀ jj ∈ Finset.range (N + 1),
      ∫ t in {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
          (1 - eps - ∑ i, t i) ^ (N - jj) * lmono β k t * lmono β' k t
        = (1 - eps) ^ (k + (N - jj) + β.sum + β'.sum) * ((N - jj).factorial : ℝ) *
            (Slab β β' k : ℝ) /
              ((((N - jj) + β.sum + β'.sum + k).factorial : ℕ) : ℝ) := by
    intro jj _
    exact simplex_integral_lmono k (1 - eps) hc (N - jj) β β'
  rw [show (∫ t in {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
        (1 + eps - ∑ i, t i) ^ N * lmono β k t * lmono β' k t)
      = ∫ t in {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - eps},
        (∑ jj ∈ Finset.range (N + 1), ((N.choose jj : ℕ) : ℝ) * (2 * eps) ^ jj *
          ((1 - eps - ∑ i, t i) ^ (N - jj) * lmono β k t * lmono β' k t)) from by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only []
    rw [hpt t, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun jj hj => ?_)
    rw [MeasureTheory.integral_const_mul, hval jj hj]
  · intro jj _
    exact (hmono jj).const_mul _

end

end Commons.NumberTheory.MaynardSieve
