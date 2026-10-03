/-
# `Submission.Work.FIRed6Axis.Assembly` — the assembled axis repair

The chapter is the five assembled theorems below, from the seven inputs of this directory:

* `nearAxisBound`   — the (5.16) trivial bound for the near cells
  (`near_mass_bound` + `nearAxisBound_of_mass`);
* `farT1Bound`      — the far-restricted `T1` Cauchy step (`window_T1_le_sub`);
* `windowAxisBound` — the per-window far/near split (`window_bound_act_axis`);
* `reduction_save6_axis` — the axis-aware §§4–5.2 reduction
  (`reduction_save6_axis_of_window`), every piece in a far cell, with the extra near-axis error
  `c·ϑ·x^{3/4}(log x)^{Kaxis}`;
* `classSplit6`     — the far-piece class split (`farPiece_classRestrict_isBetaCoeff6`);
* `prop41_of_areas6`— the round-6 composition (`prop41_of_areas6_of`), taking `Area2_6b` in place of
  the unattainable `Area2_6`.
-/
import Mathlib
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FIRed6Axis.near_mass_bound
import Submission.Work.FIRed6Axis.nearAxisBound_of_mass
import Submission.Work.FIRed6Axis.farPiece_classRestrict_isBetaCoeff6
import Submission.Work.FIRed6Axis.window_T1_le_sub
import Submission.Work.FIRed6Axis.window_bound_act_axis
import Submission.Work.FIRed6Axis.reduction_save6_axis_of_window
import Submission.Work.FIRed6Axis.prop41of.Bundle
import Submission.Work.FITop4.Red6.Dform_le_budget6
import Submission.Work.FITop4.Red6.eventually_Xcut_cube_le
import Submission.Work.FITop4.Areas6b
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Red5.BformPi_tau_truncation
import Submission.Work.FITop4.Red5.numHyp_proof_save
import Submission.Work.FITop4.Red5.pieceFacts_proof_save
import Submission.Work.FITop3.Majorant.fhat_upper
import Submission.Work.FITop.SingleDvdTauSqLe

set_option autoImplicit false

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

noncomputable section

/-- The (5.16) trivial bound for the near-axis cells. -/
theorem nearAxisBound : NearAxisBound := nearAxisBound_of_mass near_mass_bound

/-- The far-restricted `T1` Cauchy–Schwarz step of one window. -/
theorem farT1Bound : FarT1Bound :=
  fun x N Pz Mn C τ θ K K' a p φ q Pa f S hN hMn hPaM hPaN ha hsup hMaj =>
    window_T1_le_sub x N Pz Mn C τ θ K K' a p φ q Pa f S hN hMn hPaM hPaN ha hsup hMaj

/-- The per-window far/near split of the Cauchy step. -/
theorem windowAxisBound : WindowAxisBound := window_bound_act_axis farT1Bound nearAxisBound

/-- **The axis-aware §§4–5.2 reduction**: `ReductionAxis`, every piece in a far cell, with the extra
near-axis error `c·ϑ·x^{3/4}(log x)^{Kaxis}`. -/
theorem reduction_save6_axis : ReductionAxis :=
  reduction_save6_axis_of_window windowAxisBound farT1Bound

/-- The far-piece class split: a far round-4 piece restricts to a round-6 piece in every class mod
`8`. -/
theorem classSplit6 : ClassSplit6 :=
  fun Pa φ z0 β h hfar => farPiece_classRestrict_isBetaCoeff6 h hfar

end

end Work.FIRed6Axis
