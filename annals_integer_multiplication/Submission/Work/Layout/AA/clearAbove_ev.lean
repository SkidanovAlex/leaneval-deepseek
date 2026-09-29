import Mathlib
import Submission.Work.Layout.AA.clearTo_ev
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.Base

/-!
# `clearAbove`: `Ev`-level specification

`Work.Layout.clearAbove k rr rf` is the `clearTo` loop *without* the final pop: it removes
everything above the boundary marker `gMark = Glyph.mk 7` on stack `k` but keeps the marker
itself, so it is safe to use in the middle of a run where `clearTo` would destroy the marker.

The proof is the same as that of `clearTo_ev` in `Submission/Work/Layout/AA/clearTo_ev.lean`,
reusing `clearTo_loop`; only the budget (one step less) and the final state (marker retained)
differ.
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH
open Work.Layout

/-- `clearAbove` touches only stack `k`. -/
theorem cmdTouches_clearAbove (k : Stk) (rr rf : Reg) : cmdTouches (clearAbove k rr rf) = {k} := by
  simp only [clearAbove, clearBody, seqs, cmdTouches]
  ext j
  simp

/-- **Main specification.**  `clearAbove k rr rf` strips stack `k` down to the first boundary
marker `gMark`, keeping the marker, in time `5 * D.length + 6`, where `D` is the part above the
marker; every other stack is untouched. -/
theorem clearAbove_ev (main : HvdH.Cmd) (k : HvdH.Stk) (rr rf : HvdH.Reg) (hrr : rr ≠ rf)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (D B : List HvdH.Glyph)
    (hD : Work.Layout.gMark ∉ D) (hk : X k = D ++ Work.Layout.gMark :: B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.clearAbove k rr rf) ⟨g, X⟩ s' n ∧
      n ≤ 5 * D.length + 10 ∧ s'.stk k = Work.Layout.gMark :: B ∧
      (∀ j, j ≠ k → s'.stk j = X j) := by
  have hD' : gMark ∉ D := hD
  have hk' : X k = D ++ gMark :: B := hk
  have hset : Ev main (.set rf Glyph.cons) ⟨g, X⟩ ⟨Function.update g rf Glyph.cons, X⟩ 1 :=
    ev_set' main rf Glyph.cons g X
  obtain ⟨s₁, hrun, hk₁, hr₁⟩ :=
    clearTo_loop (main := main) k rr rf D B (Function.update g rf Glyph.cons) X hD' (by simp) hk'
  have hloop : Ev main (.loop rf Glyph.cons (clearBody k rr rf))
      ⟨Function.update g rf Glyph.cons, X⟩ s₁ (5 * D.length + 5) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have htot : Ev main (clearAbove k rr rf) ⟨g, X⟩ s₁ (5 * D.length + 6) := by
    unfold clearAbove
    show Ev main (.seq (.set rf Glyph.cons) (.loop rf Glyph.cons (clearBody k rr rf))) _ _ _
    exact Ev.seq' hset hloop (by omega)
  refine ⟨s₁, _, htot, by omega, hk₁, ?_⟩
  intro j hj
  have hframe := Ev.frame htot (S := {k}) (by rw [cmdTouches_clearAbove]) (by simpa using hj)
  simpa using hframe

end Work.Layout.AA
