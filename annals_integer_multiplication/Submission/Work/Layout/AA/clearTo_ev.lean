import Mathlib
import Submission.Work.Layout.AA.Defs

/-!
# `clearTo`: `Ev`-level specification

`Work.Layout.clearTo k rr rf` removes everything above the boundary marker `gMark = Glyph.mk 7`
on stack `k`, together with the marker itself.  Here we prove its `Ev` specification: starting
from a state whose stack `k` is `D ++ gMark :: B` with `gMark ∉ D` (so that the marker is the
first one met), the program ends with stack `k = B`, leaves every other stack alone, and costs
at most `5 * D.length + 9` steps (the exact cost is `5 * D.length + 7`).

The proof follows the shape of `mvB_ev` (`Submission/Work/Layout/Move.lean`): the loop body is
analysed in the two cases "marker on top" (stop) and "other glyph on top" (pop and continue),
and the two are glued with `loopRuns`.
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH
open Work.Layout

/-! ## The two cases of the loop body -/

/-- `clearBody` with the boundary marker on top: the flag is cleared and nothing is popped. -/
theorem clearBody_hit {main : Cmd} {k : Stk} {rr rf : Reg}
    {g : Reg → Glyph} {X : Stk → List Glyph} {C : List Glyph} (hc : X k = gMark :: C) :
    ∃ s' n, Ev main (clearBody k rr rf) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk k = gMark :: C ∧ s'.reg rf = Glyph.eos := by
  have h1 : Ev main (.peek k rr) ⟨g, X⟩
      ⟨Function.update g rr ((X k).headD Glyph.eos), X⟩ 1 := ev_peek' main k rr g X
  have h2 : Ev main (.ite rr gMark (.set rf Glyph.eos) (seqs [.pop k rr, .set rf Glyph.cons]))
      ⟨Function.update g rr ((X k).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rr ((X k).headD Glyph.eos)) rf Glyph.eos, X⟩ 2 :=
    Ev.iteT (by simp [hc]) (ev_set' main rf Glyph.eos _ _)
  have h3 : Ev main (clearBody k rr rf) ⟨g, X⟩
      ⟨Function.update (Function.update g rr ((X k).headD Glyph.eos)) rf Glyph.eos, X⟩ 3 := by
    unfold clearBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  exact ⟨_, _, h3, by omega, by simp [hc], by simp⟩

/-- `clearBody` on a glyph different from the marker: pop it and keep the flag set. -/
theorem clearBody_miss {main : Cmd} {k : Stk} {rr rf : Reg}
    {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph} {G C : List Glyph}
    (hh : h ≠ gMark) (hc : X k = h :: (G ++ gMark :: C)) :
    ∃ s' n, Ev main (clearBody k rr rf) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk k = G ++ gMark :: C ∧ s'.reg rf = Glyph.cons := by
  have h1 : Ev main (.peek k rr) ⟨g, X⟩
      ⟨Function.update g rr ((X k).headD Glyph.eos), X⟩ 1 := ev_peek' main k rr g X
  have hbr : Ev main (seqs [.pop k rr, .set rf Glyph.cons])
      ⟨Function.update g rr ((X k).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update (Function.update g rr ((X k).headD Glyph.eos)) rr
          ((X k).headD Glyph.eos)) rf Glyph.cons,
        Function.update X k (X k).tail⟩ 2 := by
    show Ev main (.seq (.pop k rr) (.set rf Glyph.cons)) _ _ 2
    exact Ev.seq' (ev_pop' main k rr _ _) (ev_set' main rf Glyph.cons _ _) (by omega)
  have h2 : Ev main (.ite rr gMark (.set rf Glyph.eos) (seqs [.pop k rr, .set rf Glyph.cons]))
      ⟨Function.update g rr ((X k).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update (Function.update g rr ((X k).headD Glyph.eos)) rr
          ((X k).headD Glyph.eos)) rf Glyph.cons,
        Function.update X k (X k).tail⟩ 3 :=
    Ev.iteF (by simp [hc, hh]) hbr
  have h3 : Ev main (clearBody k rr rf) ⟨g, X⟩
      ⟨Function.update (Function.update (Function.update g rr ((X k).headD Glyph.eos)) rr
          ((X k).headD Glyph.eos)) rf Glyph.cons,
        Function.update X k (X k).tail⟩ 4 := by
    unfold clearBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, _, h3, by omega, ?_, ?_⟩
  · simp [hc]
  · simp

/-! ## The loop, and the whole program -/

/-- The `clearTo` loop: consume `D` and then the boundary marker.
`D.length + 1` iterations, cost `5 * D.length + 4` (tests included). -/
theorem clearTo_loop {main : Cmd} (k : Stk) (rr rf : Reg) :
    ∀ (D : List Glyph) (B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ D → g rf = Glyph.cons → X k = D ++ gMark :: B →
      ∃ s', loopRuns main rf Glyph.cons (clearBody k rr rf) (D.length + 1) ⟨g, X⟩ s'
          (5 * D.length + 4) ∧
        s'.stk k = gMark :: B ∧ s'.reg rf = Glyph.eos := by
  intro D
  induction D with
  | nil =>
      intro B g X _ hreg hc
      obtain ⟨s', n, hev, hn, hsk, hsr⟩ :=
        clearBody_hit (main := main) (k := k) (rr := rr) (rf := rf) (g := g) (X := X)
          (C := B) (by simpa using hc)
      have h4 : loopRuns main rf Glyph.cons (clearBody k rr rf) 1 ⟨g, X⟩ s' 4 :=
        loopRuns.mono (le_refl 1) (loopRuns.one hreg (hev.mono hn)) (by omega)
      exact ⟨s', by simpa using h4, by simpa using hsk, hsr⟩
  | cons h D' ih =>
      intro B g X hmem hreg hc
      have hh : h ≠ gMark := fun hh => hmem (hh ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ D' := fun hx => hmem (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, hk₁, hr₁⟩ :=
        clearBody_miss (main := main) (k := k) (rr := rr) (rf := rf) (g := g) (X := X)
          (h := h) (G := D') (C := B) hh (by simpa using hc)
      obtain ⟨s₂, hrun₂, hk₂, hr₂⟩ := ih B s₁.reg s₁.stk hmem' hr₁ hk₁
      have h1 : loopRuns main rf Glyph.cons (clearBody k rr rf) 1 ⟨g, X⟩ s₁ 5 :=
        loopRuns.mono (le_refl 1) (loopRuns.one hreg (hev₁.mono hn₁)) (by omega)
      have hcat := loopRuns.concat (D'.length + 1) h1 hrun₂
      refine ⟨s₂, loopRuns.congr ?_ ?_ hcat, hk₂, hr₂⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

/-- `clearTo` touches only stack `k`. -/
theorem cmdTouches_clearTo (k : Stk) (rr rf : Reg) : cmdTouches (clearTo k rr rf) = {k} := by
  simp only [clearTo, clearBody, seqs, cmdTouches]
  ext j
  simp

/-- **Main specification.**  `clearTo k rr rf` strips stack `k` down to (and including) the
first boundary marker `gMark`, in time `5 * D.length + 7`, where `D` is the part above the
marker; every other stack is untouched. -/
theorem clearTo_ev (main : HvdH.Cmd) (k : HvdH.Stk) (rr rf : HvdH.Reg) (hrr : rr ≠ rf)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (D B : List HvdH.Glyph)
    (hD : HvdH.Glyph.mk 7 ∉ D) (hk : X k = D ++ HvdH.Glyph.mk 7 :: B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.clearTo k rr rf) ⟨g, X⟩ s' n ∧
      n ≤ 5 * D.length + 9 ∧ s'.stk k = B ∧ (∀ j, j ≠ k → s'.stk j = X j) := by
  have hD' : gMark ∉ D := hD
  have hk' : X k = D ++ gMark :: B := hk
  have hset : Ev main (.set rf Glyph.cons) ⟨g, X⟩ ⟨Function.update g rf Glyph.cons, X⟩ 1 :=
    ev_set' main rf Glyph.cons g X
  obtain ⟨s₁, hrun, hk₁, hr₁⟩ :=
    clearTo_loop (main := main) k rr rf D B (Function.update g rf Glyph.cons) X hD' (by simp) hk'
  have hloop : Ev main (.loop rf Glyph.cons (clearBody k rr rf))
      ⟨Function.update g rf Glyph.cons, X⟩ s₁ (5 * D.length + 5) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hpop : Ev main (.pop k rr) s₁
      ⟨Function.update s₁.reg rr ((s₁.stk k).headD Glyph.eos),
        Function.update s₁.stk k (s₁.stk k).tail⟩ 1 := ev_pop main k rr s₁
  have hrest : Ev main (seqs [.loop rf Glyph.cons (clearBody k rr rf), .pop k rr])
      ⟨Function.update g rf Glyph.cons, X⟩
      ⟨Function.update s₁.reg rr ((s₁.stk k).headD Glyph.eos),
        Function.update s₁.stk k (s₁.stk k).tail⟩ (5 * D.length + 6) := by
    show Ev main (.seq (.loop rf Glyph.cons (clearBody k rr rf)) (.pop k rr)) _ _ _
    exact Ev.seq' hloop hpop (by omega)
  have htot : Ev main (clearTo k rr rf) ⟨g, X⟩
      ⟨Function.update s₁.reg rr ((s₁.stk k).headD Glyph.eos),
        Function.update s₁.stk k (s₁.stk k).tail⟩ (5 * D.length + 7) := by
    unfold clearTo
    show Ev main (.seq (.set rf Glyph.cons)
      (seqs [.loop rf Glyph.cons (clearBody k rr rf), .pop k rr])) _ _ _
    exact Ev.seq' hset hrest (by omega)
  refine ⟨_, _, htot, by omega, ?_, ?_⟩
  · simp [hk₁]
  · intro j hj
    have hframe := Ev.frame htot (S := {k}) (by rw [cmdTouches_clearTo]) (by simpa using hj)
    simpa using hframe

end Work.Layout.AA
