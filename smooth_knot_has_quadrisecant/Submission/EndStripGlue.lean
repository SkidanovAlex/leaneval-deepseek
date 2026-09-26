import Mathlib
import Submission.OneSidedAttach
import Submission.TerminalAttachment

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S234 — the END-STRIP GLUE and the chain-consumption interface
(module Submission/EndStripGlue.lean)

Per the S233 status the next decision of the interval side is the
chain-consumption design: `attach_cutting_endStrip`/`attach_cutting_realized`
(S232/S233) produce an open arc-charted `V` with `EndStripAttach P V κ`
(the ORIENTATION-NEUTRAL disjunction: `TerminalAttach P V κ s` OR
`InitialAttach P V κ s`) and `V ∖ P ≠ ∅`, while the S207/S208 chain glue
(`glue_of_TerminalAttach`, `chain_step_prefix_interval_of_terminal`) and
the T1-abstract target `OneStepTerminalExtension P κ` are stated for
`TerminalAttach` against a FIXED prefix chart `κ`.  This module fixes the
design decision and verifies the glue interface:

**Design decision (recorded, ROADMAP S234).**  The per-level chain loop
keeps ONLY the pair `(prefix set P, its interval chart)`; at each level
the boundary attach supplies `EndStripAttach P V κ` (either end).  The
next prefix is `P ∪ V` with the chart given by the glue below — for the
INITIAL branch the prefix chart is first reversed
(`revORI.trans κ`, `initialAttach_to_terminal_rev`, S231), which turns
the initial strip `(0,b)` into the terminal strip `(1−b,1)` of the
reversed chart, and then `glue_of_TerminalAttach` (S218, restating S207)
applies.  No per-level orientation bookkeeping is needed: the glued chart
of `P ∪ V` is the fresh chart consumed by the next level's boundary
analysis, whatever end the attach reached.  (`OneStepTerminalExtension P κ`
remains the statement of the T1-abstract target when a terminal attach
against the GIVEN `κ` is contractually required — e.g. after fixing the
convention that the boundary point being attached at lies at the κ-terminal
end — but the chain itself can consume the orientation-neutral data.)

Content (all verified, sorry-free):

1. **`glue_of_endStripAttach`** — THE glue theorem at the
   orientation-neutral level: open arcs `P`, `V` (Hausdorff ambient) with
   interval charts `κ`, `η` and `EndStripAttach P V κ` glue to an open
   interval arc `Nonempty ({x ∈ P ∪ V} ≃ₜ ORI 0 1)` — terminal branch:
   `glue_of_TerminalAttach κ`; initial branch: reverse the prefix chart
   and apply the terminal glue;
2. **`EndStripExtension P κ`** — the per-level EXTENSION record
   (orientation-neutral analogue of `OneStepTerminalExtension`): an open
   arc-charted `V` attaching over an END strip of the prefix coordinate
   with a genuine extension point (`V ∖ P ≠ ∅`);
3. **`glue_step_of_EndStripExtension`** — the chain-step consumption:
   from `IsOpen P` and `EndStripExtension P κ` there is a strict open arc
   prefix `P' ⊃ P` (viz. `P ∪ V`) interval-charted — the per-level step
   of the exhaustion loop (no orientation case-split visible to the
   caller; the next level's chart is the glued chart);
4. **`endStripExtension_of_rawBoundary`** — the attach-cutting output
   normalized to the record: from the raw boundary data of
   `AttachCuttingStatement` (`IsOpen U`, `RightFreeAt`, the finite local
   structure `hF`, `y ∈ closure P`) the extension record
   `EndStripExtension P κ` holds — a re-bundling of
   `attach_cutting_realized` (S233) that the loop consumes uniformly
   (iii-c will supply the `hF` input; the RightFreeAt/closure inputs come
   from the one-sided boundary analysis).

Everything here is verified (no axioms, no `sorry`).
-/

/-- **End-strip glue**: open arcs `P`, `V` (Hausdorff ambient) with
interval charts and an END-STRIP attach (`TerminalAttach` or
`InitialAttach` over the prefix chart `κ`) glue to an open interval arc.
Initial attaches first reverse the prefix chart (`revORI.trans κ`), which
turns the initial strip `(0,b)` into the terminal strip `(1−b,1)` of the
reversed chart (S231), then apply the terminal glue. -/
theorem glue_of_endStripAttach {X : Type*} [TopologicalSpace X] [T2Space X]
    {P V : Set X} (hPopen : IsOpen P) (hVopen : IsOpen V)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (η : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hEnd : EndStripAttach P V κ) :
    Nonempty ({x : X // x ∈ P ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  rcases hEnd with hterm | hinit
  · rcases hterm with ⟨s, hT⟩
    exact glue_of_TerminalAttach hPopen hVopen κ η hT
  · rcases hinit with ⟨b, hInit⟩
    have hT : TerminalAttach P V (revORI.trans κ) (1 - b) :=
      initialAttach_to_terminal_rev P V κ hInit
    exact glue_of_TerminalAttach hPopen hVopen (revORI.trans κ) η hT

/-- **End-strip extension record** (orientation-neutral per-level step):
an open arc-charted `V` attaching over an END strip of the prefix
coordinate (`EndStripAttach P V κ`) and genuinely extending the prefix
(`V \ P ≠ ∅`).  This is the data the boundary attach supplies (S232/S233
`attach_cutting_endStrip`) and the per-level loop consumes (the glue
below); unlike `OneStepTerminalExtension` it does not fix which end of
the prefix coordinate the attach reached. -/
def EndStripExtension {X : Type*} [TopologicalSpace X] (P : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
    EndStripAttach P V κ ∧ (V \ P).Nonempty

/-- **The strictness content of a genuine extension**: if `V \ P` is
nonempty then `P` is a strict subset of `P ∪ V` (witness: the extension
point lies in the union but not in `P`). -/
lemma strict_subset_union_of_diff_nonempty {X : Type*} (P V : Set X)
    (hVdiff : (V \ P).Nonempty) : P ⊂ P ∪ V := by
  rcases hVdiff with ⟨x, hxV, hxPc⟩
  constructor
  · exact Set.subset_union_left
  · intro hsub
    exact hxPc (hsub (Or.inr hxV))

/-- **Chain-step consumption of the extension record**: from an open
prefix `P` (chart `κ`) with `EndStripExtension P κ`, there is a STRICT
open arc prefix `P' ⊃ P` interval-charted — the per-level step of the
exhaustion loop.  The next level's prefix is `P' = P ∪ V` and its chart
is the glued chart of `glue_of_endStripAttach` (no orientation
bookkeeping: whichever end the attach reached, the glued chart is a
fresh chart for the next level's boundary analysis). -/
theorem glue_step_of_EndStripExtension {X : Type*} [TopologicalSpace X] [T2Space X]
    {P : Set X} (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (hPopen : IsOpen P) (hExt : EndStripExtension P κ) :
    ∃ P' : Set X, IsOpen P' ∧ P ⊂ P' ∧
      Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P'}) := by
  rcases hExt with ⟨V, hVopen, hVchart, hEnd, hVdiff⟩
  rcases hVchart with ⟨η⟩
  have hstrict : P ⊂ P ∪ V := strict_subset_union_of_diff_nonempty P V hVdiff
  have hglue : Nonempty ({x : X // x ∈ P ∪ V} ≃ₜ OpenRealInterval 0 1) :=
    glue_of_endStripAttach hPopen hVopen κ η hEnd
  rcases hglue with ⟨e⟩
  exact ⟨P ∪ V, hPopen.union hVopen, hstrict, ⟨e.symm⟩⟩

/-- **The attach-cutting output as an extension record**: from the raw
boundary data of `AttachCuttingStatement` — the open arc-chart `ψ` of
the boundary point `y` (`y ∈ U`, `y ∉ P`), the overlap-coordinate set
`Sℝ` right-free at `c₀` (one-sidedness), the finite local structure
`hF` (iii-c supplies it), and the bridge input `y ∈ closure P` (S220) —
the extension record `EndStripExtension P κ` holds: a re-bundling of
`attach_cutting_realized` (S233) into the interface the per-level loop
consumes. -/
theorem endStripExtension_of_rawBoundary {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyPc : y ∉ P)
    (hUopen : IsOpen U)
    (hfree : RightFreeAt (((↑) : OpenRealInterval 0 1 → ℝ) ''
        {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P})
        ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ))
    (hF : ∃ F : Finset (ℝ × ℝ),
      (((↑) : OpenRealInterval 0 1 → ℝ) ''
        {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) ∩ Set.Iio
          ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ) =
        ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
      ∀ p ∈ F, p.2 ≤ ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ))
    (hclP : y ∈ closure P) :
    EndStripExtension P κ := by
  dsimp [EndStripExtension]
  exact attach_cutting_realized P U κ ψ hyU hyPc hUopen hfree hF hclP

end LeanEval.KnotTheory.Quadrisecant
