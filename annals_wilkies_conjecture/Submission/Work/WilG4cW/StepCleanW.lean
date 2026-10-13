/-
  WilG4cW / `StepCleanW` — BNZ §5.5 (the final clean up) under the corrected Corollary 5.5.

  This is a copy of `Submission/Work/WilG4c/StepClean.lean` with the frozen `F1Affine`
  replaced by the corrected `Work.WilG4a.F1AffineW`.  The proof is the same: the `h1` hypothesis
  is never used by the §5.5 engine (`hP3`, `hchoice` and `ih` enter only through
  `Work.WilG4c.FLemPOfFibreCores` and `Work.WilG4c.FibreBadCoresSharp`), see
  `Submission/Work/WilG4c/STEPCLEAN_NOTES.md`.
-/
import Mathlib
import Submission.Work.WilG4c.StepClean
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.FibreBadCoresSharp

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ §5.5 — final clean up**, with the corrected `n = 1` corollary `F1AffineW` in place of
the frozen `F1Affine`.  Same statement as `Work.WilkG4c.StepClean`; the only change is the type
of `h1`. -/
theorem StepCleanW (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, FLem S q n)
    (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hP3 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PSmooth p n)) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n) := by
  exact Work.WilG4c.FLemPOfFibreCores S hcd n p hn ih
    (Work.WilG4c.FibreBadCoresSharp S hcd hder p (n + 1))

end Work.WilkG4c
