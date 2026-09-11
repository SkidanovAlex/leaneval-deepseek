import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsT

/-!
# The 5.7''-type deep theorem and its proof (Lemma ML), on nice layered data.
-/

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Nice

open Frame
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-- |U| ≤ n_b for a minimum fragment (from obs.T). -/
lemma obsT_le (N : Sys X) (S : Set X) (W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') :
    (U.ncard : ℝ) ≤ (N.prefixCount S b : ℝ) := by
  have hT := ObsT.theorem_obsT N S W U b hS hB hmin hfr
  -- U = unionBelow S' b \ W ⊆ unionBelow S' b
  have hUsub : U ⊆ N.unionBelow S' b := by
    rw [← hT]
    exact Set.sdiff_subset
  have hcard1 : U.ncard ≤ (N.unionBelow S' b).ncard := Set.ncard_le_ncard hUsub
  have hcard2 : (N.unionBelow S' b).ncard = N.prefixCount S' b :=
    (N.prefixCount_eq_card_below S' b).symm
  have hpc : N.prefixCount S' b = N.prefixCount S b := by
    -- S' ∈ FPartial S b : profile (count) equality on j ≤ b
    unfold Sys.prefixCount
    apply Finset.sum_congr rfl
    intro j hj
    have hprof : N.ProfileEq S S' b := hfr.1.2
    have hcnt : N.sCount S j = N.sCount S' j := hprof j (by simpa using hj)
    rw [hcnt]
  have hle : U.ncard ≤ N.prefixCount S b := by
    calc
      U.ncard ≤ (N.unionBelow S' b).ncard := hcard1
      _ = N.prefixCount S' b := hcard2
      _ = N.prefixCount S b := hpc
  exact_mod_cast hle

end Nice
end Submission
