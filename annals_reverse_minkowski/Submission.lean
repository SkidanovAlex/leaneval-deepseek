import ChallengeDeps
import Submission.Helpers
import Submission.OneDim
import Submission.Prop72

open ReverseMinkowski
open Module Real Matrix
open scoped Real BigOperators

set_option autoImplicit false
variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Submission

theorem theorem_1_2 (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (h : ∀ ℒ' (_hℒℒ' : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], determinant ℒ' ≥ 1) :
    let t : ℝ := 10 * (log n + 2)
    ρ (1 / t) ℒ ≤ 3 / 2 := by
  by_cases hn : n ≤ 1
  · exact OneDim.theorem_1_2_small hn ℒ hℒ h
  · -- n ≥ 2: the [B] reduction (canonical_mass_bound) plus RM_stable (MainStable).
    exact MainStable.theorem_1_2_large ℒ hℒ h

end Submission
