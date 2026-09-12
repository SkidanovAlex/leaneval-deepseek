import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-- A member `M ∈ 𝓕` contained in `T`, minimal under inclusion. -/
lemma exists_minimal_subset {𝓕 : Set (Set X)} {T : Set X} (hT : T ∈ 𝓕) :
    ∃ M : Set X, M ∈ 𝓕 ∧ M ⊆ T ∧ ∀ ⦃S : Set X⦄, S ∈ 𝓕 → S ⊆ M → S = M := by
  classical
  -- Collect the members of 𝓕 lying inside T; T itself witnesses nonemptiness.
  let C : Finset (Set X) := Finset.univ.filter (fun S : Set X => S ∈ 𝓕 ∧ S ⊆ T)
  have hTC : T ∈ C := by simp [C, hT]
  -- Choose M ∈ C of minimal cardinality.
  obtain ⟨M, hMC, hmin⟩ := Finset.exists_min_image C (fun S : Set X => S.ncard) ⟨T, hTC⟩
  have hM : M ∈ 𝓕 ∧ M ⊆ T := (Finset.mem_filter.mp hMC).2
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro S hS hSM
  -- Any member of 𝓕 contained in M also lies in C (it is contained in T).
  have hSC : S ∈ C := by
    rw [Finset.mem_filter]
    exact ⟨by simp, hS, subset_trans hSM hM.2⟩
  -- Cardinalities are equal, so S = M by finiteness.
  have h1 : M.ncard ≤ S.ncard := hmin S hSC
  exact Set.eq_of_subset_of_ncard_le hSM h1

end FET
end Submission
