import Submission.Work.WilkiesH.Count.all_of
import Submission.Work.WilkiesH.Strat.strat_input_of_parts
import Submission.Work.WilkiesH.Interp.interpPerChart_v2

/-!
# Area H (counting) — the area theorem, under the lead's name

This file is the deliverable of area H: BNZ's point-counting theorem for a sharply o-minimal
structure, in the statement of the lead's hole `WilkiesDesign.H_count`, under the name
`WilkiesDesign.H_count_proved`.  The lead's `Holes.lean` wires it in by replacing the `sorry`
of `H_count` with this declaration.

The statement is *identical* to the hole (`H_count S hcd hder hG F n : CountBound S F n`), and
the proof is the chain of

* `Work.WilkiesH.Count.countBound_of_inputs` (the assembly: interpolation + stratification ⇒
  `CountBound`), with
* `Work.WilkiesH.Strat.strat_input_of_parts` (the stratification input, BNZ §2.3, from
  `SharpCD` — the `SI`-route, whose only geometric input is the thinness of the intersection of
  two distinct cells of a cylindrical decomposition, `Work.WilkiesH.Strat.SI.cellMeetThin`), and
* `Work.WilkiesH.Interp.interpPerChart_v2` (the interpolation step, BNZ Prop. 6.1, from
  `AlgLemma`, in its `v2` form, whose numerical input is `Interp.exists_params_v2`).

The same wiring works with `Work.WilkiesH.Strat.strat_input_of_sharpCD` (the `rft`-route) in
place of `Strat.strat_input_of_parts`, and with the `v1` form
`Work.WilkiesH.Interp.interpPerChart_of_algLemma` in place of `Interp.interpPerChart_v2`;
all four combinations typecheck (see
`Submission/Work/WilkiesH/_ax/WiringCheck.lean`).

`SharpDeriv` is not consumed by area H (it is area G's input for `AlgLemma`); it remains in the
signature because the hole `H_count` has it.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace WilkiesDesign

open WilkiesConjecture

/-- **Area H: BNZ's counting theorem** (`H_count` of the lead's `Holes.lean`). -/
theorem H_count_proved (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hG : ∀ F n : ℕ, AlgLemma S F n) (F n : ℕ) : CountBound S F n :=
  Work.WilkiesH.Count.countBound_of_inputs (S := S) hcd hG
    (Work.WilkiesH.Strat.strat_input_of_parts (S := S) hcd)
    (fun F' n' => Work.WilkiesH.Interp.interpPerChart_v2 (S := S) F' n' (hG F' n'))
    F n

end WilkiesDesign
