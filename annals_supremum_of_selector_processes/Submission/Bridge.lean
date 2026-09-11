import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps

/-!
# Bridge between the measure-theoretic statements and finite combinatorics
-/

set_option autoImplicit false
open MeasureTheory Measure ProbabilityTheory unitInterval Finset
open scoped ENNReal NNReal

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Bridge

/-- The mass of a single subset under the binomial set distribution (as ENNReal). -/
lemma setBernoulli_singleton_mass {X : Type*} [Fintype X] (p : I) (s : Set X) :
    binomialSetDistribution X p {s} =
      (toNNReal p : ℝ≥0∞) ^ s.ncard * (toNNReal (σ p) : ℝ≥0∞) ^ (Set.univ \ s).ncard := by
  unfold binomialSetDistribution
  simpa using (ProbabilityTheory.setBernoulli_singleton (p := p) (s := s) (u := Set.univ)
    (by simp) (Set.finite_univ))

/-- The integral of a function w.r.t. the binomial set distribution equals a finite sum. -/
lemma lintegral_binomial_eq_sum {X : Type*} [Fintype X] (p : I)
    (f : Set X → ℝ≥0∞) :
    ∫⁻ s : Set X, f s ∂binomialSetDistribution X p =
      ∑ s : Set X, f s * (toNNReal p : ℝ≥0∞) ^ s.ncard *
        (toNNReal (σ p) : ℝ≥0∞) ^ (Set.univ \ s).ncard := by
  classical
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro s hs
  rw [setBernoulli_singleton_mass p s]
  ring

end Bridge
end Submission
