import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs

/-!
# Cost brackets of the `progTensorB` blocks

The four blocks of `progTensorB` (`pbSetupF`, `pbIterF`, `pbFinal`, `pbClr`) each carry a cost bound
of the shape `Kc * bracket`, where the bracket is the concrete expression spelled out in the
statement of the block.  This file names those four brackets, so that the single arithmetic lemma
`Work.Resample.pbCostArith` bounding their sum by `HvdH.resCost` can refer to them.

Each definition is *syntactically* the bracket of the corresponding block statement, hence
definitionally equal to it.

## Why the brackets are linear

The tables `P j` produced by the one-dimensional word `prep` are *not* compared with a marker
value; instead the round pushes a raw glyph `Work.Layout.gMark` (`= .mk 7`, which never occurs in a
`Val.enc`) on stack 0 just above the marker `M` *before* running `prep`, and drains everything
above it again with `Work.Resample.pbDrainProg` after the slice word has run.  The drain costs one
primitive step per popped glyph, so `O(vsz (P j))`; comparing `vsz` against `vsz M` instead would
cost `O(vsz (P j) * vsz M)` per round, which `HvdH.resCost` cannot absorb
(`vsz M ~ Kb * ts.sum * (p+1)^Kb` is *not* bounded by a constant multiple of `ts.sum`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-- Cost bracket of the setup block (`pbSetupF`). -/
def BrSetup (Kb p : ℕ) (ts : List ℕ) : ℕ :=
  ts.prod * (2 * p + 8) + HvdH.D * (HvdH.D * (p + 1)) * (HvdH.D * (p + 1)) +
    PBTab Kb p ts + 1000 * (HvdH.D * (p + 1)) + 100

/-- Cost bracket of the `D`-fold round iteration (`pbIterF`). -/
def BrIter (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ts : List ℕ) : ℕ :=
  HvdH.D * (Kb * (ts.sum + 1) * (p + 1) ^ Kb)
  + 4 * HvdH.D * ts.prod *
      (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) + Kb * (p + 1) ^ 2)
  + 4 * HvdH.D * ts.prod *
      ((2 * p + 8) + (ts.prod * 2 ^ (p + 1)).size + 1) * ((ts.prod * 2 ^ (p + 1)).size + 1)
  + HvdH.D * (32 * (ts.prod * (2 * p + 8) + 2))
  + HvdH.D * (800 * (HvdH.D * (p + 1)))
  + HvdH.D * (Kb * (ts.sum + 1) * (p + 1) ^ Kb + 1000)
  + HvdH.D * 100

/-- Cost bracket of the epilogue (`pbFinal`). -/
def BrFin (Kb p : ℕ) (ts : List ℕ) (M : Val) : ℕ :=
  ts.prod * (2 * p + 8) + vsz M + HvdH.D * (p + 1) + 10

/-- Cost bracket of the frame cleanup (`pbClr`). -/
def BrClr (p α : ℕ) (ss ts : List ℕ) (M : Val) : ℕ :=
  vsz M + vsz (intList ts) + vsz (intList ss) + vsz (.int ((ss.take HvdH.D).prod)) +
    vsz (.int ((ts.drop HvdH.D).prod)) + vsz (.int p) + vsz (.int α) + 100

end Work.Resample
