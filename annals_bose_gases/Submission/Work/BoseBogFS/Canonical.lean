import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Canonical` — this chapter's `BogOpBoundAtFS` *is* the design's
# `BogOpBoundFS`

Node `D-FS`'s canonical statement (`Submission/Work/BoseBoxFock/Defs.lean`) and this chapter's
`Work.BoseBogFS.BogOpBoundAtFS` are the **same proposition**: both quantify `∃ ε₀ C, 0 < ε₀ ∧
0 ≤ C ∧ ∀ μ, Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ, 0 ≤ ρ → CloseCondFS v μ ρ → ∀ f, …`, over
the shared `KzDatum`/`viewFS`, the shared `KzBogFS`/`dNumOpR`/`RHi` and the shared error bracket
`errBracket v R μ` (the `§11` monomial `fsX² + (R/a)²√dil + errExp`).

Consequently the chapter's capstones

* `bogOpBoundAtFSWith_of_honestRows` (+ `BogOpBoundAtFS_of_with`),
* `bogOpBoundAtFSWith_of_sharpMatchInjL` / `bogOpBoundAtFS_of_sharpMatchInjL`,

deliver the canonical `Work.BoseBoxFock.BogOpBoundFS` — the very hypothesis `hbog` of the
sibling node's `Work.BoseBoxFock.RB67FS_of_pieces` — by definitional conversion, with no
`closeThreshold`/`F9` edit needed (contrast the legacy `Work.BoseBogFS.BogOpBoundFS`, which is
stated at the *corpus* `CloseCond` and needs the `F9` identity;
`FINDING_honest_interface.md` §5 records this).

**Do not** re-state `BogOpBoundFS` in this chapter: import the canonical one.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The chapter's `BogOpBoundAtFS` is the design's canonical `BogOpBoundFS`** (definitional
equality of the two `Prop`s). -/
theorem BogOpBoundAtFS_iff_canonical (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) :
    BogOpBoundAtFS v h R D ↔ Work.BoseBoxFock.BogOpBoundFS v h R D := Iff.rfl

/-- The transport the sibling node consumes: a proof of the chapter's `BogOpBoundAtFS` *is* a
proof of the canonical `BogOpBoundFS`. -/
theorem canonical_of_bogOpBoundAtFS {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ} {D : ℝ → KzDatum}
    (hb : BogOpBoundAtFS v h R D) : Work.BoseBoxFock.BogOpBoundFS v h R D := hb

/-- The converse transport (for completeness). -/
theorem bogOpBoundAtFS_of_canonical {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ} {D : ℝ → KzDatum}
    (hb : Work.BoseBoxFock.BogOpBoundFS v h R D) : BogOpBoundAtFS v h R D := hb

end Work.BoseBogFS
