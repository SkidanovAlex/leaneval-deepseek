/-
# `Submission.Work.FIArea3.BoxDefs` — the polar-box Finset, so that cardinality statements can be
*stated* without needing a `DecidablePred` instance in the statement itself.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

open Finset Work.FIPlan
open scoped BigOperators

namespace Work.FIArea3

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The `β`-supporting set inside `boxN`: the polar box (5.14).  This is the only set over which
the sums of `CoreBound`/`Area3` actually run (`IsBetaCoeff` forces `β z = 0` off the polar box). -/
def polarBoxFinset (Pa : Work.FITop.Params) (φ : ℝ) : Finset GaussianInt :=
  (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z)

@[simp] theorem mem_polarBoxFinset {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt} :
    z ∈ polarBoxFinset Pa φ ↔ z ∈ Work.FITop.boxN Pa ∧ Work.FITop3.InPolarBox Pa φ z :=
  Finset.mem_filter

theorem polarBoxFinset_subset (Pa : Work.FITop.Params) (φ : ℝ) :
    polarBoxFinset Pa φ ⊆ Work.FITop.boxN Pa := Finset.filter_subset _ _

end

end Work.FIArea3
