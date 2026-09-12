import Mathlib
import Submission.Contracts
import Submission.PotentialContinuity

/-!
# Bridge between `PotentialContinuity.muS` and `Contracts.muSerre`

The early-ints / quantile layers work with `PotentialContinuity.muS` (an
`abbrev`), while `Contracts.muSerre` (a `def`) is the measure used by the
Serre-side contracts and the keystone.  Both are definitionally the same
`serreMeasure gSerre aSerre bSerre`; this module records the equalities so
`rw`/`simpa` can move integrals and weight functions between the two names
without unfolding large definitions.

Namespace `Submission.MuBridge`.  Only Mathlib + the two measure modules.
-/

noncomputable section
open MeasureTheory
open scoped Real ENNReal Topology

namespace Submission.MuBridge

open Submission.PotentialContinuity
open Submission.Contracts
open Submission.WeightedNorm

/-- The two measures are definitionally equal. -/
lemma muS_eq_muSerre : muS = muSerre := rfl

/-- The first-moment integral is the same for both names. -/
lemma integral_id_eq : (∫ x : ℝ, x ∂muS) = (∫ x : ℝ, x ∂muSerre) := by
  rw [muS_eq_muSerre]

/-- Any integral of the same function is the same for both names. -/
lemma integral_eq {f : ℝ → ℝ} : (∫ x : ℝ, f x ∂muS) = (∫ x : ℝ, f x ∂muSerre) := by
  rw [muS_eq_muSerre]

/-- The weight function agrees on the two names. -/
lemma weight_eq (x : ℝ) : weight muS x = weight muSerre x := by
  rw [muS_eq_muSerre]

/-- Measures agree on every set. -/
lemma measure_eq (s : Set ℝ) : muS s = muSerre s := by
  rw [muS_eq_muSerre]

end Submission.MuBridge
