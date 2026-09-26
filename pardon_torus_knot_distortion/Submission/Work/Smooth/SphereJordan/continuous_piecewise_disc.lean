import Mathlib
import Submission.Work.Smooth.Jordan.Defs

namespace Work.Smooth.SphereJordan

/-- Pasting lemma for a function on the model disc which coincides with `F` on the closed
half-disc `{‖z‖ ≤ 1/2}` and with `G` off it: continuity follows as soon as `F` and `G` agree on
the switching circle `{‖z‖ = 1/2}`.

This is the general topological fact (`Continuous.if_le`) that replaces `e' z := if ‖z‖ ≤ 1/2 then
cap (2 • z) else out z` being continuous in the cut-and-paste of `Pasting.lean`: the switching set
is the frontier of the closed half-disc `{‖z‖ ≤ 1/2}`, namely the circle `{‖z‖ = 1/2}`. -/
theorem continuous_piecewise_disc (F G : Work.Smooth.Jordan.Disc → LeanEval.KnotTheory.PardonDistortion.R3) (hF : Continuous F) (hG : Continuous G) (hagree : ∀ z : Work.Smooth.Jordan.Disc, ‖((z : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1 / 2 → F z = G z) : Continuous (fun z : Work.Smooth.Jordan.Disc => if ‖((z : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 / 2 then F z else G z) := by
  have hf : Continuous (fun z : Work.Smooth.Jordan.Disc => ‖((z : Work.Smooth.Jordan.Disc) : ℂ)‖) :=
    continuous_norm.comp continuous_subtype_val
  exact Continuous.if_le hF hG hf continuous_const (fun z hz => hagree z hz)

end Work.Smooth.SphereJordan
