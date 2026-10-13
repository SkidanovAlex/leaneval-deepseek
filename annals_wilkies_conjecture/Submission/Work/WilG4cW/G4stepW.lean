/-
  WilG4cW / `G4stepW` — the induction step `G4_step` of BNZ §§5.2–5.5 with the corrected
  Corollary 5.5.

  The frozen `CG.G4_step` (`Submission/Work/WilG4c/G4step.lean`) takes
  `h1 : ∀ p, CG.F1Affine S p`; by the lead's audit
  (`sources/wilkies_g4/wilkies_g4_audit.md`, `wilkies_g4_REVIEW.md`) that statement is FALSE at
  `p = 1`, so it can never be applied.  Area G4a delivers instead
  `h1 : ∀ p, Work.WilG4a.F1AffineW S p` (`Submission/Work/WilG4a/F1AffineW.lean`), the corrected
  Corollary 5.5 in which a chart may be degenerate (`β l = 0`, the constant chart `t ↦ α l`)
  while the cover is still achieved by non-degenerate charts.

  The assembly is the same as `G4step.lean`, with the W-variants of the reductions:

    `StepBase`     : `FLemP (PSmooth)`                       — identity chart (§5.5, `V = ∅`)
    `StepCleanW`   : `FLemP (PSmooth) → FLemP (PYLipDef)`    — §5.5 clean up
    `StepHigherW`  : `FLemP (PYLipDef) → FLemP (PYLip)`      — §5.4 higher derivatives
    `StepLip`      : `FLemP (PYLip) → FLemP (PY)`            — §5.3 (already takes `F1AffineW`)
    `StepYbdd`     : `FLemP (PY) → FLem` (dimension `n+1`)   — §5.2 bounded `y`-derivatives

  (`Work.WilG4c.StepLip` in `Submission/Work/WilG4c/StepLip.lean` is already stated with
  `h1 : ∀ q, F1AffineW S q`, so it is used directly.)
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.StepBase
import Submission.Work.WilG4c.StepYbdd
import Submission.Work.WilG4c.StepLip
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4cW.StepCleanW
import Submission.Work.WilG4cW.StepHigherW

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ §§5.2–5.5 (`CG.G4_step`), corrected**: the induction step of the algebraic lemma.
From `FLem` in dimension `n` deduce `FLem` in dimension `n+1`, for every number `p` of
parameters, using the corrected `n = 1` corollary `Work.WilG4a.F1AffineW`.

Besides `S`, `hcd`, `hder`, `n`, `hn`, `h1`, `ih` this uses two other areas' holes as explicit
hypotheses: `ChoiceHyp S` = `CG.G1_choice S hcd` (definable choice with sharp bounds) and
`BddDxHyp S` = `CG.G4_bdd_dx S hcd hder` (BNY Lemma 16). -/
theorem G4_step_provedW (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ p, Work.WilG4a.F1AffineW S p) (ih : ∀ p, FLem S p n)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (hbdd : Work.WilkG4c.BddDxHyp S) :
    ∀ p, FLem S p (n + 1) := by
  intro p
  -- §5.5, `V = ∅` case: the identity chart.
  have hBase : FLemP S p (n + 1) (PSmooth p n) := StepBase S n p
  -- §5.5: remove the non-smooth locus by cell decomposition and the family algebraic lemma.
  have hClean : FLemP S p (n + 1) (PYLipDef p n) :=
    Work.WilkG4c.StepCleanW S hcd hder n p hn h1 ih hchoice hBase
  -- §5.4: control the higher derivatives along the `Γ_{i,α}` curves.
  have hHigher : FLemP S p (n + 1) (PYLip p n) :=
    Work.WilkG4c.StepHigherW S hcd hder n p hn h1 ih hchoice hbdd hClean
  -- §5.3: reduce to `1`-Lipschitz families by subdividing the `x`-interval.
  have hLip : FLemP S p (n + 1) (PY p n) :=
    Work.WilG4c.StepLip S hcd hder n p hn h1 ih hchoice hbdd hHigher
  -- §5.2: pull back along the inductive `n`-dimensional charts.
  exact StepYbdd S n p hn ih hLip

end Work.WilkG4c
