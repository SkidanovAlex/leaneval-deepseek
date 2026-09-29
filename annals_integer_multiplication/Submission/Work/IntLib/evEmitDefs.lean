import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.IntLib.stripFalses_map_bit
import Submission.Work.Layout.Base
import Submission.Work.IntLib.dropZeros
import Submission.Work.IntLib.drainUntilEval
import Submission.Work.IntLib.clearAllsEv
import Submission.Work.IntLib.encodeNatBridge

/-!
# `IntLib` / `evEmit`: definitions and raw toolkit

The `evEmit` word takes the *window* `W` (stack `aW`, least significant bit on top), the
*finalised low bits* `LO` (stack `aO`, most significant bit on top, below the sign `pos`) and
emits the encoding of `V = ofBits LO + 2^(LO.length) * ofBits W` on stack 0, restoring every
other stack (i.e. removing the frame markers `Shift.gmk k`, and discarding the junk regions
`Vr`, `Rcb`, `Rcw` sitting above the markers of `aV`, `aCB`, `aCW`).

The program is

* `Shift.clearAll` every stack of `evL1` (the junk regions on `aV`, `aCB`, `aCW` and the bare
  markers of the ten unused stacks) -- this is the `evEmit_clean` step;
* push `iend` on stack 0;
* `evValProg`: push `pos` on `evS2`; drain the `aO` region (up to the sign `pos`) onto `evS1`;
  drop the marker of `aO`; drain `evS1` onto `evS2` (so `evS2` holds the bits of `V` most
  significant first, below the sign); drain `aW` onto `evS2`; strip the leading (most
  significant) `bit false` glyphs;
* drain `evS2` (up to its marker) onto stack 0.

The order of the pushes is what makes the final list come out right: pushing `pos`, then the
bits of `LO` least-significant-first, then the bits of `W` least-significant-first, leaves
`(bits of V reversed) ++ pos` on `evS2`, whose reverse, above the `iend` pushed on stack 0, is
exactly `Val.enc (.int V)`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Registers and scratch stacks -/

/-- working register of the `evEmit` word -/
def evR : Reg := 0
/-- flag register of the `evEmit` word -/
def evRF : Reg := 1
/-- first scratch stack of the `evEmit` word -/
def evS1 : Stk := 12
/-- second scratch stack of the `evEmit` word -/
def evS2 : Stk := 13

theorem evRF_ne_evR : evRF ≠ evR := by decide

/-! ## The stacks cleared before the value is emitted -/

/-- The stacks whose regions are cleared up front: the junk regions above the markers of `aV`,
`aCB`, `aCW`, and the bare markers of the ten stacks unused by the value phase. -/
def evL1 : List Stk := [aV, aCB, aCW, 2, 4, 5, 8, 9, 10, 14, 15]

/-- The region above the frame marker of the stacks of `evL1`. -/
def evRegs (Vr Rcb Rcw : List Glyph) : Stk → List Glyph := fun k =>
  if k = aV then Vr else if k = aCB then Rcb else if k = aCW then Rcw else []

theorem evL1_nodup : evL1.Nodup := by decide

theorem mem_evL1 (k : Stk) :
    k ∈ evL1 ↔ (k = aV ∨ k = aCB ∨ k = aCW ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 14 ∨ k = 15) := by
  fin_cases k <;> decide

theorem evL1_length : evL1.length = 11 := by decide

theorem evRegs_aV (Vr Rcb Rcw : List Glyph) : evRegs Vr Rcb Rcw aV = Vr := by
  unfold evRegs
  rw [if_pos rfl]

theorem evRegs_aCB (Vr Rcb Rcw : List Glyph) : evRegs Vr Rcb Rcw aCB = Rcb := by
  unfold evRegs
  rw [if_neg (by decide : ¬ (aCB = aV)), if_pos rfl]

theorem evRegs_aCW (Vr Rcb Rcw : List Glyph) : evRegs Vr Rcb Rcw aCW = Rcw := by
  unfold evRegs
  rw [if_neg (by decide : ¬ (aCW = aV)), if_neg (by decide : ¬ (aCW = aCB)), if_pos rfl]

theorem evRegs_other (Vr Rcb Rcw : List Glyph) {k : Stk} (h1 : k ≠ aV) (h2 : k ≠ aCB)
    (h3 : k ≠ aCW) : evRegs Vr Rcb Rcw k = [] := by
  unfold evRegs
  rw [if_neg h1, if_neg h2, if_neg h3]

/-! ## The programs -/

/-- The value phase: turn the window `W` (on `aW`) and the finalised low bits `LO` (on `aO`)
into `(bits of V reversed) ++ [pos]` above the marker of `evS2`. -/
def evValProg : Cmd := Work.Layout.seqs [
    pushConst evS2 Glyph.pos evR,
    drainUntil aO evS1 Glyph.pos evR,
    .pop aO evR,
    drainUntil evS1 evS2 (Shift.gmk evS1) evR,
    drainUntil aW evS2 (Shift.gmk aW) evR,
    dropZerosProg evS2 evR ]

/-- The whole `evEmit` word. -/
def evEmitProg : Cmd := Work.Layout.seqs [
    Work.Layout.seqs (evL1.map (fun k => Shift.clearAll k evR evRF)),
    pushConst 0 Glyph.iend evR,
    evValProg,
    drainUntil evS2 0 (Shift.gmk evS2) evR ]

/-! ## Raw toolkit wrappers -/

/-- `pushConst k c r` pushes `c` on stack `k`. -/
theorem ev_pushConst (main : Cmd) (k : Stk) (c : Glyph) (r : Reg) (s : State) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main (pushConst k c r) s s' n ∧ n ≤ 2 ∧
      s'.stk k = c :: s.stk k ∧ (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨⟨Function.update s.reg r c, Function.update s.stk k (c :: s.stk k)⟩, 2, ?_, by norm_num,
    ?_, ?_⟩
  · unfold pushConst
    have hset := Shift.ev_set' main r c s.reg s.stk
    have hpush : Shift.Ev main (.push k r) ⟨Function.update s.reg r c, s.stk⟩
        ⟨Function.update s.reg r c, Function.update s.stk k (c :: s.stk k)⟩ 1 := by
      have h := Shift.ev_push' main k r (Function.update s.reg r c) s.stk
      simpa [Function.update_self] using h
    exact (Work.Layout.Ev.seq hset hpush).mono (by norm_num)
  · simp
  · intro j hj; simp [Function.update_of_ne hj]

/-- `pop k r` removes the top glyph of stack `k`. -/
theorem ev_popHead (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main (.pop k r) s s' n ∧ n ≤ 1 ∧
      s'.stk k = (s.stk k).tail ∧ (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨⟨Function.update s.reg r ((s.stk k).headD .eos), Function.update s.stk k
    (s.stk k).tail⟩, 1, ?_, le_rfl, ?_, ?_⟩
  · exact ⟨1, Eval.pop k r s, le_rfl⟩
  · simp
  · intro j hj; simp [Function.update_of_ne hj]

/-- `drainUntil k k' T r`: move the region above the marker `T` of stack `k` onto stack `k'`
(reversed), dropping `T`. -/
theorem ev_drainUntil (main : Cmd) {k k' : Stk} (hkk : k ≠ k') (T : Glyph) (r : Reg)
    (gs below : List Glyph) (s : State) (hne : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main (drainUntil k k' T r) s s' n ∧
      n ≤ 5 * gs.length + 6 ∧ s'.stk k = below ∧ s'.stk k' = gs.reverse ++ s.stk k' ∧
      (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  obtain ⟨s', n, hn, he, h1, h2, h3, h4⟩ :=
    drainUntilEval main k k' hkk T r gs below s hne hstk
  exact ⟨s', n, ⟨n, he, le_rfl⟩, hn, h1, h2, h4⟩

/-- `dropZerosProg k r`: strip the leading run of `bit false` glyphs of stack `k`. -/
theorem ev_dropZeros (main : Cmd) (k : Stk) (r : Reg) {M : Glyph} (hM : M ≠ Glyph.bit false)
    (l A : List Glyph) (s : State) (hX : s.stk k = l.reverse ++ M :: A) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main (dropZerosProg k r) s s' n ∧
      n ≤ 3 * (l.length + 1) + 1 ∧ s'.stk k = (stripFalses l).reverse ++ M :: A ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  obtain ⟨s', n, he, hn, h1, h2⟩ := dropZeros main k r hM l A s.reg s.stk hX
  exact ⟨s', n, he, hn, h1, h2⟩

/-- The stacks of `evL1` are not touched by the rest of the program (the value phase and the
final drain), so their content after the whole program is the one produced by the clearing. -/
theorem evL1_not_mem_touches (k : Stk) (hk : k ∈ evL1) :
    k ∉ Work.Layout.cmdTouches (Work.Layout.seqs [pushConst 0 Glyph.iend evR, evValProg,
      drainUntil evS2 0 (Shift.gmk evS2) evR]) := by
  rw [mem_evL1] at hk
  rcases hk with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-! ## The clearing phase -/

/-- Clearing the regions `Vr`, `Rcb`, `Rcw` and the bare markers of the ten unused stacks. -/
theorem evEmit_clean (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (Vr Rcb Rcw : List Glyph) (Y : Stk → List Glyph)
    (hVr : ∀ h ∈ Vr, h ≠ Shift.gmk aV) (hRcb : ∀ h ∈ Rcb, h ≠ Shift.gmk aCB)
    (hRcw : ∀ h ∈ Rcw, h ≠ Shift.gmk aCW)
    (hV : X aV = Vr ++ Shift.gmk aV :: Y aV)
    (hCB : X aCB = Rcb ++ Shift.gmk aCB :: Y aCB)
    (hCW : X aCW = Rcw ++ Shift.gmk aCW :: Y aCW)
    (hOther : ∀ k : Stk, k ≠ 0 → k ≠ aW → k ≠ aO → k ≠ aV → k ≠ aCB → k ≠ aCW →
      X k = Shift.gmk k :: Y k) :
    ∃ (s' : State) (n : ℕ),
      Work.Layout.Ev main (Work.Layout.seqs (evL1.map (fun k => Shift.clearAll k evR evRF))) ⟨g, X⟩ s' n ∧
      n ≤ 5 * (Vr.length + Rcb.length + Rcw.length + 11) + 110 ∧
      (∀ k ∈ evL1, s'.stk k = Y k) ∧ (∀ k ∉ evL1, s'.stk k = X k) := by
  have hsafe : ∀ k ∈ evL1, ∀ h ∈ evRegs Vr Rcb Rcw k, h ≠ Shift.gmk k := by
    intro k hk h hh
    rw [mem_evL1] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    · subst hk; rw [evRegs_aV] at hh; exact hVr h hh
    · subst hk; rw [evRegs_aCB] at hh; exact hRcb h hh
    · subst hk; rw [evRegs_aCW] at hh; exact hRcw h hh
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 2) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 4) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 5) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 8) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 9) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 10) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 14) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 15) (by decide) (by decide) (by decide)] at hh
      exact absurd hh (by simp)
  have hZ : ∀ k ∈ evL1, X k = evRegs Vr Rcb Rcw k ++ Shift.gmk k :: Y k := by
    intro k hk
    rw [mem_evL1] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    · subst hk; rw [evRegs_aV]; exact hV
    · subst hk; rw [evRegs_aCB]; exact hCB
    · subst hk; rw [evRegs_aCW]; exact hCW
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 2) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 4) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 5) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 8) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 9) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 10) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 14) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst hk
      rw [evRegs_other Vr Rcb Rcw (k := 15) (by decide) (by decide) (by decide), List.nil_append]
      exact hOther 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s', n, he, hn, h1, h2⟩ :=
    clearAllsEv main evL1 evR evRF X Y g (evRegs Vr Rcb Rcw) evL1_nodup hsafe hZ
  have hsum : (evL1.map fun k => (evRegs Vr Rcb Rcw k).length).sum
      = Vr.length + Rcb.length + Rcw.length := by
    simp only [evL1, evRegs_aV, evRegs_aCB, evRegs_aCW, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.length_cons]
    rw [evRegs_other Vr Rcb Rcw (k := 2) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 4) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 5) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 8) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 9) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 10) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 14) (by decide) (by decide) (by decide),
      evRegs_other Vr Rcb Rcw (k := 15) (by decide) (by decide) (by decide)]
    simp only [List.length_nil, List.sum_nil]
    omega
  refine ⟨s', n, he, ?_, h1, h2⟩
  rw [hsum, evL1_length] at hn
  omega

end Work.IntLib
