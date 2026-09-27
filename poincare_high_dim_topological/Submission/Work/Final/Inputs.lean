import Submission.Work.Final.Defs

/-!
# `Work.Final.FinalInputs`: the holders of the final assembly

The final theorem of this area is proved modulo a single bundle of statements,
`Work.Final.FinalInputs n`.  Everything else in the chain is discharged from the delivered areas
(see `Submission/Work/Final/Assumptions.lean`).

## Remaining holder

* `engulf : Work.Cells.Connell.EngulfForm.{u} n` — Newman's engulfing theorem (`E0`), the
  engulfing theorem of Newman 1966 that the Connell cell-count reduction
  (`Work.Cells.Connell.connell_step`) consumes.  It is owned by the `Submission/Work/Engulf`
  area (`A9`), which currently proves it modulo the four forms
  `SubdivShellForm`, `PlApproxFrozenForm`, `SdFullForm`, `JoinPrismForm`
  (`Work.Engulf.engulf_of_forms`); see `Submission/Work/Final/OfForms.lean` for the reduction of
  `FinalInputs n` to those four.

`Work.Geo.DualStretch`'s `SkeletonData` (`G7`) is **not** a holder: it is discharged by
`Work.Final.skeletonData` (`Submission/Work/Final/Defs.lean`), with the interface repair explained
in the docstring there.
-/

universe u

namespace Work.Final

/-- **The holders of the final assembly.**  A proof of `FinalInputs n` is exactly the missing
piece: Newman's engulfing theorem in the form `Work.Cells.Connell.EngulfForm` consumed by the
Connell cell-count reduction.  Every other hypothesis of the chain is a delivered theorem. -/
structure FinalInputs (n : ℕ) : Prop where
  /-- `E0` (Newman's engulfing theorem), owned by `Submission/Work/Engulf` (`A9`). -/
  engulf : Work.Cells.Connell.EngulfForm.{u} n

/-- The trivial implementation of `FinalInputs n` from the engulfing theorem. -/
theorem FinalInputs.ofEngulf {n : ℕ} (h : Work.Cells.Connell.EngulfForm.{u} n) :
    FinalInputs.{u} n :=
  ⟨h⟩

end Work.Final
