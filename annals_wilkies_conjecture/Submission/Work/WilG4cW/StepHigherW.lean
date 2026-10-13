/-
  WilG4cW / `StepHigherW` — BNZ §5.4 under the corrected Corollary 5.5.

  This is a copy of `Submission/Work/WilG4c/StepHigher.lean` (the §5.4 reduction
  `FLemP (PYLipDef) → FLemP (PYLip)`) with the frozen `F1Affine` replaced by the corrected
  `Work.WilG4a.F1AffineW`: the stage hypothesis is produced by `StepStage_of_axesW`
  (`Submission/Work/WilG4cW/StepStageOfAxesW.lean`) and consumed by `Work.WilG4cW.FLemPOfStageW`
  (`Submission/Work/WilG4cW/FLemPOfStageW.lean`), which uses the W-variants of the five chart
  lemmas instead of the frozen ones.
-/
import Mathlib
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4cW.StepStageOfAxesW
import Submission.Work.WilG4cW.FLemPOfStageW

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ §5.4 — controlling higher derivatives**, with the corrected `n = 1` corollary
`Work.WilG4a.F1AffineW` in place of the frozen `F1Affine`.  From `FLem` for families with unit
`y`-derivatives, `1`-Lipschitz, and all derivative norms `≤ 1` wherever defined (`PYLipDef`),
deduce `FLem` for the `1`-Lipschitz families (`PYLip`).

Same statement as `Work.WilkG4c.StepHigher`; the only change is the type of `h1`. -/
theorem StepHigherW (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, FLem S q n)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (hbdd : Work.WilkG4c.BddDxHyp S)
    (hP2 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n)) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n) :=
  Work.WilG4cW.FLemPOfStageW S n p hn
    (Work.WilkG4c.StepStage_of_axesW S hcd hder p n hn h1 hchoice hbdd) hP2

end Work.WilkG4c
