import Mathlib
import Submission.Work.Layout.appendDefs

/-!
# Layout area: phase 2 of the `appendWord` list word

Phase 2 (`Work.Layout.p2`) drains the element stack 1 onto stack 0: while the element stack carries
one of its `gMark` markers on top, it pops the marker, moves the value behind it onto stack 0 (via
`mvVal 1 0 3 4`) and prepends a `cons` glyph, consing the value onto the top value of stack 0.  The
loop ends when the sentinel `gSent` (pushed by phase 0) becomes visible, and stops the loop by
setting the flag register `rFl` to `eos`.

This file proves `Work.Layout.appendPhase2`: with stack 0 holding `ofList (p ++ ys) :: rest` and
stack 1 holding the elements `mzs` (front element on top, followed by the sentinel), phase 2 ends
with stack 0 holding `ofList (mzs.reverse ++ p ++ ys) :: rest` and stack 1 reduced to the sentinel,
in cost `≤ 40 * (vsz (ofList mzs) + 1) + 2`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## Elementary steps -/

/-- `pushG k c` pushes the constant glyph `c` on stack `k`, touching no other stack. -/
theorem pushG_ev {main : Cmd} {k : Stk} {c : Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} :
    Ev main (pushG k c) ⟨g, X⟩ ⟨Function.update g rB c, Function.update X k (c :: X k)⟩ 2 := by
  unfold pushG
  simp only [seqs]
  exact Ev.seq' (ev_set' main rB c g X) (ev_push' main k rB (Function.update g rB c) X)
    (by omega)

/-- The tail of one phase-2 iteration for a present element `v`: move the value from stack 1 to
stack 0, cons it onto the top value, and re-arm the loop flag. -/
theorem p2Tail_ev {main : Cmd} {v : Val} {A B C3 C4 : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (ha : X 1 = v.enc ++ A) (hb : X 0 = B)
    (h3 : X 3 = C3) (h4 : X 4 = C4) :
    ∃ s' n, Ev main (seqs [mvVal 1 0 3 4, pushG 0 Glyph.cons, Cmd.set rFl gMark]) ⟨g, X⟩ s' n ∧
      n ≤ 19 + 16 * vsz v ∧
      s'.stk 0 = Glyph.cons :: (v.enc ++ B) ∧ s'.stk 1 = A ∧ s'.stk 3 = C3 ∧ s'.stk 4 = C4 ∧
      s'.reg rFl = gMark := by
  obtain ⟨s₁, n₁, he₁, hn₁, h11, h01, h31, h41, _⟩ :=
    mvVal_ev_all (main := main) (a := 1) (b := 0) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g) (X := X) (v := v) (A := A) (B := B) ha hb
  have hpush : Ev main (pushG 0 Glyph.cons) s₁
      ⟨Function.update s₁.reg rB Glyph.cons, Function.update s₁.stk 0 (Glyph.cons :: s₁.stk 0)⟩ 2 :=
    pushG_ev (main := main) (k := 0) (c := Glyph.cons) (g := s₁.reg) (X := s₁.stk)
  have hset : Ev main (Cmd.set rFl gMark)
      ⟨Function.update s₁.reg rB Glyph.cons, Function.update s₁.stk 0 (Glyph.cons :: s₁.stk 0)⟩
      ⟨Function.update (Function.update s₁.reg rB Glyph.cons) rFl gMark,
        Function.update s₁.stk 0 (Glyph.cons :: s₁.stk 0)⟩ 1 :=
    ev_set' main rFl gMark _ _
  have hrest : Ev main (seqs [pushG 0 Glyph.cons, Cmd.set rFl gMark]) s₁
      ⟨Function.update (Function.update s₁.reg rB Glyph.cons) rFl gMark,
        Function.update s₁.stk 0 (Glyph.cons :: s₁.stk 0)⟩ (2 + 1) := by
    simp only [seqs]
    exact Ev.seq' hpush hset (by omega)
  have hmain : Ev main (seqs [mvVal 1 0 3 4, pushG 0 Glyph.cons, Cmd.set rFl gMark]) ⟨g, X⟩
      ⟨Function.update (Function.update s₁.reg rB Glyph.cons) rFl gMark,
        Function.update s₁.stk 0 (Glyph.cons :: s₁.stk 0)⟩ (n₁ + 3) := by
    simp only [seqs]
    exact Ev.seq' he₁ hrest (by omega)
  refine ⟨_, n₁ + 3, hmain, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h01]
  · simp only [Function.update_of_ne (by decide : (1 : Stk) ≠ 0)]; exact h11
  · simp only [Function.update_of_ne (by decide : (3 : Stk) ≠ 0), h31]; exact h3
  · simp only [Function.update_of_ne (by decide : (4 : Stk) ≠ 0), h41]; exact h4
  · simp [Function.update_self]

/-! ## One iteration of the phase-2 loop -/

/-- One phase-2 iteration when an element `v` is present: stack 1 starts with the marker and `v.enc`,
stack 0 holds `lstEnc W ++ C0`.  The value is consed onto stack 0's top value and the loop flag is
re-armed. -/
theorem p2Body_hit {main : Cmd} {v : Val} {zs W : List Val} {C0 C1 C3 C4 : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (h0 : X 0 = lstEnc W ++ C0) (h1 : X 1 = elsEnc (v :: zs) (gSent :: C1))
    (h3 : X 3 = C3) (h4 : X 4 = C4) :
    ∃ s' n, Ev main p2Body ⟨g, X⟩ s' n ∧ n ≤ 22 + 16 * vsz v ∧
      s'.stk 0 = lstEnc (v :: W) ++ C0 ∧ s'.stk 1 = elsEnc zs (gSent :: C1) ∧
      s'.stk 3 = C3 ∧ s'.stk 4 = C4 ∧ s'.reg rFl = gMark := by
  have hhead : (X 1).headD Glyph.eos = gMark := by rw [h1, elsEnc_cons_append]; rfl
  have htail : (X 1).tail = v.enc ++ elsEnc zs (gSent :: C1) := by rw [h1, elsEnc_cons_append]; rfl
  have hregA : (Function.update g rA ((X 1).headD Glyph.eos)) rA = gMark := by
    rw [Function.update_self]; exact hhead
  have hpeek : Ev main (Cmd.peek 1 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ 1 := ev_peek' main 1 rA g X
  have hpop : Ev main (Cmd.pop 1 rA) ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rA ((X 1).headD Glyph.eos),
        Function.update X 1 (X 1).tail⟩ 1 := ev_pop' main 1 rA _ _
  obtain ⟨s₂, n₂, he₂, hn₂, h02, h12, h32, h42, hr₂⟩ :=
    p2Tail_ev (main := main) (v := v) (A := elsEnc zs (gSent :: C1)) (B := lstEnc W ++ C0)
      (C3 := C3) (C4 := C4)
      (g := Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rA ((X 1).headD Glyph.eos))
      (X := Function.update X 1 (X 1).tail)
      (by simp only [Function.update_self]; exact htail)
      (by simp only [Function.update_of_ne (by decide : (0 : Stk) ≠ 1)]; exact h0)
      (by simp only [Function.update_of_ne (by decide : (3 : Stk) ≠ 1)]; exact h3)
      (by simp only [Function.update_of_ne (by decide : (4 : Stk) ≠ 1)]; exact h4)
  have hbranch : Ev main (seqs [Cmd.pop 1 rA, mvVal 1 0 3 4, pushG 0 Glyph.cons, Cmd.set rFl gMark])
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ s₂ (1 + n₂) := by
    simp only [seqs]
    exact Ev.seq hpop he₂
  have hite : Ev main (Cmd.ite rA gMark
        (seqs [Cmd.pop 1 rA, mvVal 1 0 3 4, pushG 0 Glyph.cons, Cmd.set rFl gMark])
        (Cmd.set rFl Glyph.eos))
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ s₂ (1 + n₂ + 1) :=
    Ev.iteT hregA hbranch
  have hbody : Ev main p2Body ⟨g, X⟩ s₂ (1 + (1 + n₂ + 1)) := by
    unfold p2Body
    simp only [seqs]
    exact Ev.seq hpeek hite
  refine ⟨s₂, 1 + (1 + n₂ + 1), hbody, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h02, lstEnc_cons]; simp [List.append_assoc, List.cons_append]
  · exact h12
  · exact h32
  · exact h42
  · exact hr₂

/-- One phase-2 iteration when no element is left: the element stack shows the sentinel, so the
loop flag is set to `eos` and every stack is left alone. -/
theorem p2Body_miss {main : Cmd} {W : List Val} {C0 C1 C3 C4 : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (h0 : X 0 = lstEnc W ++ C0) (h1 : X 1 = gSent :: C1)
    (h3 : X 3 = C3) (h4 : X 4 = C4) :
    ∃ s' n, Ev main p2Body ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 0 = lstEnc W ++ C0 ∧ s'.stk 1 = gSent :: C1 ∧
      s'.stk 3 = C3 ∧ s'.stk 4 = C4 ∧ s'.reg rFl = Glyph.eos := by
  have hhead : (X 1).headD Glyph.eos = gSent := by rw [h1]; rfl
  have hregA : (Function.update g rA ((X 1).headD Glyph.eos)) rA = gSent := by
    rw [Function.update_self]; exact hhead
  have hne : (Function.update g rA ((X 1).headD Glyph.eos)) rA ≠ gMark := by rw [hregA]; decide
  have hpeek : Ev main (Cmd.peek 1 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩ 1 := ev_peek' main 1 rA g X
  have hset : Ev main (Cmd.set rFl Glyph.eos)
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rFl Glyph.eos, X⟩ 1 :=
    ev_set' main rFl Glyph.eos _ _
  have hite : Ev main (Cmd.ite rA gMark
        (seqs [Cmd.pop 1 rA, mvVal 1 0 3 4, pushG 0 Glyph.cons, Cmd.set rFl gMark])
        (Cmd.set rFl Glyph.eos))
      ⟨Function.update g rA ((X 1).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rFl Glyph.eos, X⟩ 2 :=
    Ev.iteF hne hset
  have hbody : Ev main p2Body ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X 1).headD Glyph.eos)) rFl Glyph.eos, X⟩ 3 := by
    unfold p2Body
    simp only [seqs]
    exact Ev.seq' hpeek hite (by omega)
  refine ⟨_, 3, hbody, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h0
  · simpa using h1
  · simpa using h3
  · simpa using h4
  · simp [Function.update_self]

/-! ## The phase-2 loop -/

/-- The phase-2 loop run: exactly `mzs.length + 1` iterations, the last one (seeing the sentinel)
stopping the loop.  Every element of `mzs` is consed onto stack 0's top value in turn, so that stack
0 ends with `ofList (mzs.reverse ++ W) :: rest`; the loop flag ends at `eos`.  Cost
`23 * mzs.length + 16 * (mzs.map vsz).sum + 4`. -/
theorem p2Loop_run (main : Cmd) :
    ∀ (mzs : List Val) (W : List Val) (C0 C1 C3 C4 : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      g rFl = gMark → X 0 = lstEnc W ++ C0 → X 1 = elsEnc mzs (gSent :: C1) →
      X 3 = C3 → X 4 = C4 →
      ∃ s', loopRuns main rFl gMark p2Body (mzs.length + 1) ⟨g, X⟩ s'
          (23 * mzs.length + 16 * (mzs.map vsz).sum + 4) ∧
        s'.stk 0 = lstEnc (mzs.reverse ++ W) ++ C0 ∧ s'.stk 1 = gSent :: C1 ∧
        s'.stk 3 = C3 ∧ s'.stk 4 = C4 ∧ s'.reg rFl = Glyph.eos := by
  intro mzs
  induction mzs with
  | nil =>
      intro W C0 C1 C3 C4 g X hg h0 h1 h3 h4
      obtain ⟨s', n', hev, hn', h0', h1', h3', h4', hr'⟩ :=
        p2Body_miss (main := main) (W := W) (C0 := C0) (C1 := C1) (C3 := C3) (C4 := C4)
          (g := g) (X := X) h0 h1 h3 h4
      refine ⟨s', loopRuns.one hg (hev.mono hn'), ?_, ?_, ?_, ?_, hr'⟩
      · simpa using h0'
      · simpa using h1'
      · simpa using h3'
      · simpa using h4'
  | cons v zs ih =>
      intro W C0 C1 C3 C4 g X hg h0 h1 h3 h4
      obtain ⟨s₁, n₁, hev₁, hn₁, h01, h11, h31, h41, hr₁⟩ :=
        p2Body_hit (main := main) (v := v) (zs := zs) (W := W) (C0 := C0) (C1 := C1)
          (C3 := C3) (C4 := C4) (g := g) (X := X) h0 h1 h3 h4
      obtain ⟨s₂, hrun₂, h02, h12, h32, h42, hr₂⟩ :=
        ih (v :: W) C0 C1 C3 C4 s₁.reg s₁.stk hr₁ h01 h11 h31 h41
      have hcat : loopRuns main rFl gMark p2Body (1 + (zs.length + 1)) ⟨g, X⟩ s₂
          ((22 + 16 * vsz v) + 1 + (23 * zs.length + 16 * (zs.map vsz).sum + 4)) :=
        loopRuns.concat (zs.length + 1) (loopRuns.one hg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, hr₂⟩
      · refine loopRuns.cast ?_ (loopRuns.mono ?_ hcat ?_)
        · simp only [List.length_cons]; omega
        · omega
        · simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
      · rw [h02]; simp only [List.reverse_cons, List.singleton_append, List.append_assoc]
      · exact h12
      · exact h32
      · exact h42

theorem appendPhase2 {main : HvdH.Cmd} (mzs p ys : List HvdH.Val) (C0 C1 C3 C4 : List HvdH.Glyph)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = Work.Layout.lstEnc (p ++ ys) ++ C0)
    (h1 : X 1 = Work.Layout.elsEnc mzs (Work.Layout.gSent :: C1))
    (h3 : X 3 = C3) (h4 : X 4 = C4) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.p2 ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.vsz (HvdH.ofList mzs) + 1) + 2 ∧
      s'.stk 0 = Work.Layout.lstEnc (mzs.reverse ++ p ++ ys) ++ C0 ∧
      s'.stk 1 = Work.Layout.gSent :: C1 ∧
      s'.stk 3 = C3 ∧ s'.stk 4 = C4 ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → k ≠ 3 → k ≠ 4 → s'.stk k = X k) := by
  have hset : Ev main (Cmd.set rFl gMark) ⟨g, X⟩ ⟨Function.update g rFl gMark, X⟩ 1 :=
    ev_set' main rFl gMark g X
  obtain ⟨s₁, hrun, h01, h11, h31, h41, hr₁⟩ :=
    p2Loop_run main mzs (p ++ ys) C0 C1 C3 C4 (Function.update g rFl gMark) X
      (by simp) h0 h1 h3 h4
  have hev : Ev main p2Loop ⟨Function.update g rFl gMark, X⟩ s₁
      (23 * mzs.length + 16 * (mzs.map vsz).sum + 4 + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hmain : Ev main p2 ⟨g, X⟩ s₁ (40 * (vsz (ofList mzs) + 1) + 2) := by
    unfold p2
    refine Ev.seq' hset hev ?_
    rw [vsz_ofList]
    omega
  refine ⟨s₁, 40 * (vsz (ofList mzs) + 1) + 2, hmain, le_rfl, ?_, h11, h31, h41, ?_⟩
  · rw [h01, List.append_assoc]
  · intro k hk0 hk1 hk3 hk4
    exact Ev.frame hmain cmdTouches_p2 (notMem_0134 hk0 hk1 hk3 hk4)

end Work.Layout
