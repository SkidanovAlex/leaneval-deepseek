import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.encodeNatBridge

/-!
# `Work.Transform.Pw`: a self-contained copy of the raw glyph toolkit

A private, self-contained copy of the reusable raw StackLang machinery of
`Submission/Work/IntLib/cmpWord.lean` (that file is edited concurrently, so importing it is unsafe
here).  Over the marker glyph `Pw.gM` it provides `tLoop` (move the glyphs above a marker to another
stack, reversed), `tLoop2` (to two stacks), `dLoop` (discard), `storeMag`, `revMarked`, `dropMarked`,
`copyMarked2`, plus the bit-string comparison machinery `NatFlag`, `two_pow_pred_le_ofBits`,
`ofBits_lt_of_length_lt`.  All declarations here are proved outright.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel
open Work.IntLib


/-- Frame marker used on every scratch stack. -/
def gM : Glyph := .mk 5


/-- Second frame marker (used by `copyMarked`). -/
def gM2 : Glyph := .mk 10

/-- `reg rCont` value that stops the scan loop. -/
def gStop : Glyph := .mk 6

/-- `reg rFlag` value: "less". -/
def gLt : Glyph := .mk 7

/-- `reg rFlag` value: "greater". -/
def gGt : Glyph := .mk 8

/-- `reg rFlag` value: "equal". -/
def gEq : Glyph := .mk 9


/-- `NatFlag f x y` says that the glyph `f` records the comparison of the naturals `x` and `y`. -/
def NatFlag (f : Glyph) (x y : ℕ) : Prop :=
  (f = gLt ∧ x < y) ∨ (f = gEq ∧ x = y) ∨ (f = gGt ∧ y < x)

/-- `IntFlag f a b` says that the glyph `f` records the comparison of the integers `a` and `b`. -/
def IntFlag (f : Glyph) (a b : ℤ) : Prop :=
  (f = gLt ∧ a < b) ∨ (f = gEq ∧ a = b) ∨ (f = gGt ∧ b < a)

/-- Extensionality for `HvdH.State`, in the `∀`-component form. -/
theorem State.ext' {s t : State} (h1 : ∀ r, s.reg r = t.reg r) (h2 : ∀ k, s.stk k = t.stk k) :
    s = t := by
  cases s with
  | mk a b =>
    cases t with
    | mk c d => simp only [State.mk.injEq]; exact ⟨funext h1, funext h2⟩

/-- Stack content after a `tPop`. -/
theorem tPop_stk (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPop s k r).stk j = if j = k then (s.stk k).tail else s.stk j := by
  simp only [State.tPop, State.updStk, State.updReg, Function.update_apply]

/-- Register content after a `tPop`. -/
theorem tPop_reg (s : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPop s k r).reg r' = if r' = r then (s.stk k).headD Glyph.eos else s.reg r' := by
  simp only [State.tPop, State.updStk, State.updReg, Function.update_apply]

/-- Stack content after a `tPush`. -/
theorem tPush_stk (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPush s k r).stk j = if j = k then s.reg r :: s.stk j else s.stk j := by
  simp only [State.tPush, State.updStk, State.updReg, Function.update_apply]
  by_cases h : j = k <;> simp [h]

/-- Register content after a `tPush`. -/
theorem tPush_reg (s : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPush s k r).reg r' = s.reg r' := rfl

/-- Stack content after a `tSet`. -/
theorem tSet_stk (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet s r g).stk j = s.stk j := rfl

/-- Register content after a `tSet`. -/
theorem tSet_reg (s : State) (r : Reg) (g : Glyph) (r' : Reg) :
    (State.tSet s r g).reg r' = if r' = r then g else s.reg r' := by
  simp only [State.tSet, State.updReg, Function.update_apply]

/-! ## The transfer loop `tLoop`

`tLoop k tg dst r` pops glyphs from stack `k` into register `r`, pushing every glyph different from
`tg` onto stack `dst`; when it meets `tg` it pushes it back onto `k` and stops.  It is the basic
"reversal move": the glyphs arrive on `dst` in reverse order.
-/


theorem gM_ne_iend : gM ≠ Glyph.iend := by decide

theorem gM_ne_eos : gM ≠ Glyph.eos := by decide

theorem gM_ne_bit (b : Bool) : gM ≠ Glyph.bit b := by
  intro h; exact nomatch h

theorem gM_ne_pos : gM ≠ Glyph.pos := by decide

theorem gM_ne_neg : gM ≠ Glyph.neg := by decide

theorem iend_ne_gM : Glyph.iend ≠ gM := gM_ne_iend.symm

theorem gStop_ne_eos : gStop ≠ Glyph.eos := by decide

theorem gLt_ne_eos : gLt ≠ Glyph.eos := by decide

theorem gGt_ne_eos : gGt ≠ Glyph.eos := by decide

theorem gEq_ne_eos : gEq ≠ Glyph.eos := by decide

theorem gM2_ne_eos : gM2 ≠ Glyph.eos := by decide

theorem gM2_ne_gM : gM2 ≠ gM := by decide

theorem gM_ne_gM2 : gM ≠ gM2 := gM2_ne_gM.symm

theorem bit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := by intro h; exact nomatch h

theorem iend_ne_eos : Glyph.iend ≠ Glyph.eos := by decide

theorem iend_ne_bit (b : Bool) : Glyph.iend ≠ Glyph.bit b := fun h => bit_ne_iend b h.symm

theorem gM2_ne_bit (b : Bool) : gM2 ≠ Glyph.bit b := by intro h; cases h


/-- One step of `tLoop`. -/
def tBody (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) : Cmd :=
  .seq (.pop k r) (.ite r tg (.seq (.push k r) (.set r tg)) (.seq (.push dst r) (.set r Glyph.eos)))

/-- `tBody` iterated up to the frame marker `tg`. -/
def tLoop (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) : Cmd :=
  .seq (.set r Glyph.eos) (.loop r Glyph.eos (tBody k tg dst r))

/-- Result state of `tLoop k tg dst r` on input `gs ++ tg :: below` (with `dst ≠ k`). -/
def tSt (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) (gs below : List Glyph) (s : State) : State :=
  ((s.updReg r tg).updStk k (tg :: below)).updStk dst (gs.reverse ++ s.stk dst)

@[simp] theorem tSt_reg (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (r' : Reg) :
    (tSt k tg dst r gs below s).reg r' = if r' = r then tg else s.reg r' := by
  simp only [tSt, State.updStk, State.updReg, State.updStk_reg, State.updReg_stk,
    Function.update_apply]

@[simp] theorem tSt_stk_k (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (hkd : dst ≠ k) : (tSt k tg dst r gs below s).stk k = tg :: below := by
  rw [tSt, State.updStk_ne _ _ (Ne.symm hkd), State.updStk_same]

@[simp] theorem tSt_stk_dst (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) : (tSt k tg dst r gs below s).stk dst = gs.reverse ++ s.stk dst := by
  rw [tSt, State.updStk_same]

theorem tSt_stk_ne (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) {j : Stk} (h1 : j ≠ k) (h2 : j ≠ dst) :
    (tSt k tg dst r gs below s).stk j = s.stk j := by
  rw [tSt, State.updStk_ne _ _ h2, State.updStk_ne _ _ h1, State.updReg_stk]

@[simp] theorem tSt_stk_ne' (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) {j : Stk} (h1 : j ≠ k) (h2 : j ≠ dst) :
    (tSt k tg dst r gs below s).stk j = s.stk j :=
  tSt_stk_ne k tg dst r gs below s h1 h2

/-- Main loop lemma for `tLoop`: from `s.stk k = gs ++ tg :: below` (all `gs` different from `tg`,
`reg r = eos`) the loop ends on `tSt k tg dst r gs below s`, at cost `5 * gs.length + 6`. -/
theorem tLoopAux (main : Cmd) (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg)
    (hkd : dst ≠ k) (htg : tg ≠ Glyph.eos) :
    ∀ (gs : List Glyph) (below : List Glyph) (s : State), s.stk k = gs ++ tg :: below →
      (∀ g ∈ gs, g ≠ tg) → s.reg r = Glyph.eos →
      Eval main (.loop r Glyph.eos (tBody k tg dst r)) s (tSt k tg dst r gs below s)
        (5 * gs.length + 6) := by
  have hk : k ≠ dst := fun h => hkd h.symm
  intro gs
  induction gs with
  | nil =>
    intro below s hstk _ hr
    have hsk : s.stk k = tg :: below := by simpa using hstk
    let s2 : State := (s.updStk k below).updReg r tg
    let s3 : State := s2.updStk k (tg :: below)
    let s4 : State := s3.updReg r tg
    have hpop : State.tPop s k r = s2 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [s2, State.tPop, State.updStk, State.updReg, hsk, hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [s2, State.tPop, State.updStk, State.updReg, hsk]
        · simp [s2, State.tPop, State.updStk, State.updReg, hsk, hqk]
    have e1 : Eval main (.pop k r) s s2 1 := by rw [← hpop]; exact eval_pop main k r s
    have hr2 : s2.reg r = tg := by simp [s2, State.updStk, State.updReg]
    have hpush : State.tPush s2 k r = s3 := by
      apply State.ext'
      · intro q; simp [s3, State.tPush, State.updStk, State.updReg]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [s3, s2, State.tPush, State.updStk, State.updReg, hr2]
        · simp [s3, s2, State.tPush, State.updStk, State.updReg, hqk]
    have e2 : Eval main (.push k r) s2 s3 1 := by rw [← hpush]; exact eval_push main k r s2
    have e3 : Eval main (.set r tg) s3 s4 1 := by
      rw [show s4 = State.tSet s3 r tg from rfl]; exact eval_set main r tg s3
    have e23 : Eval main (.seq (.push k r) (.set r tg)) s2 s4 2 := Eval.seq e2 e3
    have eite : Eval main (.ite r tg (.seq (.push k r) (.set r tg))
        (.seq (.push dst r) (.set r Glyph.eos))) s2 s4 3 := Eval.iteT hr2 e23
    have ebody : Eval main (tBody k tg dst r) s s4 4 := Eval.seq e1 eite
    have hr4 : s4.reg r ≠ Glyph.eos := by
      have h : s4.reg r = tg := by simp [s4, s3, s2, State.updStk, State.updReg]
      rw [h]; exact htg
    have hloop : Eval main (.loop r Glyph.eos (tBody k tg dst r)) s4 s4 1 := Eval.loopF hr4
    have hmain : Eval main (.loop r Glyph.eos (tBody k tg dst r)) s s4 6 :=
      Eval.loopT (r := r) (c := Glyph.eos) hr ebody hloop
    have hstate : tSt k tg dst r [] below s = s4 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [tSt, s4, s3, s2, State.updStk, State.updReg, hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk
          by_cases hqd : q = dst
          · exact absurd hqd.symm hkd
          · simp [tSt, s4, s3, s2, State.updStk, State.updReg, hsk, hqd, hk]
        · by_cases hqd : q = dst
          · subst hqd; simp [tSt, s4, s3, s2, State.updStk, State.updReg, hqk]
          · simp [tSt, s4, s3, s2, State.updStk, State.updReg, hqk, hqd]
    rw [hstate]
    exact hmain
  | cons g gs' ih =>
    intro below s hstk hT hr
    have hgT : g ≠ tg := hT g (by simp)
    have hgs' : ∀ g' ∈ gs', g' ≠ tg := fun g' h' => hT g' (List.mem_cons_of_mem g h')
    have hstk' : s.stk k = g :: (gs' ++ tg :: below) := by simpa using hstk
    let s2 : State := (s.updStk k (gs' ++ tg :: below)).updReg r g
    let s3 : State := s2.updStk dst (g :: s2.stk dst)
    let s4 : State := s3.updReg r Glyph.eos
    have hpop : State.tPop s k r = s2 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [s2, State.tPop, State.updStk, State.updReg, hstk', hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [s2, State.tPop, State.updStk, State.updReg, hstk']
        · simp [s2, State.tPop, State.updStk, State.updReg, hstk', hqk]
    have e1 : Eval main (.pop k r) s s2 1 := by rw [← hpop]; exact eval_pop main k r s
    have hr2 : ¬ (s2.reg r = tg) := by
      have h : s2.reg r = g := by simp [s2, State.updStk, State.updReg]
      rw [h]; exact hgT
    have hpush : State.tPush s2 dst r = s3 := by
      apply State.ext'
      · intro q; simp [s3, State.tPush, State.updStk, State.updReg]
      · intro q
        by_cases hqd : q = dst
        · subst hqd; simp [s3, s2, State.tPush, State.updStk, State.updReg]
        · simp [s3, s2, State.tPush, State.updStk, State.updReg, hqd]
    have e2 : Eval main (.push dst r) s2 s3 1 := by rw [← hpush]; exact eval_push main dst r s2
    have e3 : Eval main (.set r Glyph.eos) s3 s4 1 := by
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl]; exact eval_set main r Glyph.eos s3
    have e23 : Eval main (.seq (.push dst r) (.set r Glyph.eos)) s2 s4 2 := Eval.seq e2 e3
    have eite : Eval main (.ite r tg (.seq (.push k r) (.set r tg))
        (.seq (.push dst r) (.set r Glyph.eos))) s2 s4 3 := Eval.iteF hr2 e23
    have ebody : Eval main (tBody k tg dst r) s s4 4 := Eval.seq e1 eite
    have hr4 : s4.reg r = Glyph.eos := by simp [s4, State.updStk, State.updReg]
    have hstk4 : s4.stk k = gs' ++ tg :: below := by
      simp only [s4, s3, s2, State.updReg_stk, State.updStk_apply]
      rw [if_neg hk]; simp
    have hrec := ih below s4 hstk4 hgs' hr4
    have hmain : Eval main (.loop r Glyph.eos (tBody k tg dst r)) s
        (tSt k tg dst r gs' below s4) (4 + (5 * gs'.length + 6) + 1) :=
      Eval.loopT (r := r) (c := Glyph.eos) hr ebody hrec
    have hstate : tSt k tg dst r (g :: gs') below s = tSt k tg dst r gs' below s4 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [tSt, s4, s3, s2, State.updStk, State.updReg, hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk
          by_cases hqd : q = dst
          · exact absurd hqd.symm hkd
          · simp [tSt, s4, s3, s2, State.updStk, State.updReg, hstk', hqd, hk]
        · by_cases hqd : q = dst
          · subst hqd; simp [tSt, s4, s3, s2, State.updStk, State.updReg, hqk]
          · simp [tSt, s4, s3, s2, State.updStk, State.updReg, hqk, hqd]
    rw [hstate]
    have hcost : 4 + (5 * gs'.length + 6) + 1 = 5 * (g :: gs').length + 6 := by simp; ring
    rwa [hcost] at hmain

/-- `tLoop` from an arbitrary state (cost of the initial `set` included). -/
theorem tLoop_eval (main : Cmd) (k : Stk) (tg : Glyph) (dst : Stk) (r : Reg)
    (hkd : dst ≠ k) (htg : tg ≠ Glyph.eos)
    (gs below : List Glyph) (s : State) (hstk : s.stk k = gs ++ tg :: below)
    (hT : ∀ g ∈ gs, g ≠ tg) :
    Eval main (tLoop k tg dst r) s (tSt k tg dst r gs below s) (5 * gs.length + 7) := by
  have h1 : Eval main (.set r Glyph.eos) s (s.updReg r Glyph.eos) 1 := eval_set main r Glyph.eos s
  have h2 : Eval main (.loop r Glyph.eos (tBody k tg dst r)) (s.updReg r Glyph.eos)
      (tSt k tg dst r gs below (s.updReg r Glyph.eos)) (5 * gs.length + 6) :=
    tLoopAux main k tg dst r hkd htg gs below (s.updReg r Glyph.eos) (by simpa using hstk) hT
      (by simp [State.updReg])
  have h3 : tSt k tg dst r gs below (s.updReg r Glyph.eos) = tSt k tg dst r gs below s := by
    apply State.ext' <;> intro q
    · by_cases hq : q = r <;> simp [tSt, State.updStk, State.updReg, hq]
    · by_cases hqk : q = k
      · subst hqk
        by_cases hqd : q = dst
        · exact absurd hqd.symm hkd
        · simp [tSt, State.updStk, State.updReg, hqd, fun (h : q = dst) => hkd h.symm]
      · by_cases hqd : q = dst
        · subst hqd; simp [tSt, State.updStk, State.updReg, hqk]
        · simp [tSt, State.updStk, State.updReg, hqk, hqd]
  rw [h3] at h2
  have h4 : Eval main (tLoop k tg dst r) s (tSt k tg dst r gs below s) (1 + (5 * gs.length + 6)) :=
    Eval.seq h1 h2
  have h5 : 1 + (5 * gs.length + 6) = 5 * gs.length + 7 := by ring
  rwa [h5] at h4

/-! ## The discard loop `dLoop`

`dLoop k tg r` pops glyphs of stack `k` (dropping them) until it meets `tg`, which it pushes back. -/


/-- One step of `dLoop`. -/
def dBody (k : Stk) (tg : Glyph) (r : Reg) : Cmd :=
  .seq (.pop k r) (.ite r tg (.seq (.push k r) (.set r tg)) (.set r Glyph.eos))

/-- `dBody` iterated up to the frame marker `tg`. -/
def dLoop (k : Stk) (tg : Glyph) (r : Reg) : Cmd :=
  .seq (.set r Glyph.eos) (.loop r Glyph.eos (dBody k tg r))

/-- Result state of `dLoop k tg r` on input `gs ++ tg :: below`. -/
def dSt (k : Stk) (tg : Glyph) (r : Reg) (below : List Glyph) (s : State) : State :=
  (s.updReg r tg).updStk k (tg :: below)

@[simp] theorem dSt_reg (k : Stk) (tg : Glyph) (r : Reg) (below : List Glyph) (s : State)
    (r' : Reg) : (dSt k tg r below s).reg r' = if r' = r then tg else s.reg r' := by
  simp only [dSt, State.updStk, State.updReg, State.updStk_reg, State.updReg_stk,
    Function.update_apply]

@[simp] theorem dSt_stk_k (k : Stk) (tg : Glyph) (r : Reg) (below : List Glyph) (s : State) :
    (dSt k tg r below s).stk k = tg :: below := by rw [dSt, State.updStk_same]

theorem dSt_stk_ne (k : Stk) (tg : Glyph) (r : Reg) (below : List Glyph) (s : State) {j : Stk}
    (h : j ≠ k) : (dSt k tg r below s).stk j = s.stk j := by
  rw [dSt, State.updStk_ne _ _ h, State.updReg_stk]

@[simp] theorem dSt_stk_ne' (k : Stk) (tg : Glyph) (r : Reg) (below : List Glyph) (s : State)
    {j : Stk} (h : j ≠ k) : (dSt k tg r below s).stk j = s.stk j := dSt_stk_ne k tg r below s h

/-- Loop lemma for `dLoop`. -/
theorem dLoopAux (main : Cmd) (k : Stk) (tg : Glyph) (r : Reg) (htg : tg ≠ Glyph.eos) :
    ∀ (gs : List Glyph) (below : List Glyph) (s : State), s.stk k = gs ++ tg :: below →
      (∀ g ∈ gs, g ≠ tg) → s.reg r = Glyph.eos →
      Eval main (.loop r Glyph.eos (dBody k tg r)) s (dSt k tg r below s) (4 * gs.length + 6) := by
  intro gs
  induction gs with
  | nil =>
    intro below s hstk _ hr
    have hsk : s.stk k = tg :: below := by simpa using hstk
    let s2 : State := (s.updStk k below).updReg r tg
    let s3 : State := s2.updStk k (tg :: below)
    let s4 : State := s3.updReg r tg
    have hpop : State.tPop s k r = s2 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [s2, State.tPop, State.updStk, State.updReg, hsk, hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [s2, State.tPop, State.updStk, State.updReg, hsk]
        · simp [s2, State.tPop, State.updStk, State.updReg, hsk, hqk]
    have e1 : Eval main (.pop k r) s s2 1 := by rw [← hpop]; exact eval_pop main k r s
    have hr2 : s2.reg r = tg := by simp [s2, State.updStk, State.updReg]
    have hpush : State.tPush s2 k r = s3 := by
      apply State.ext'
      · intro q; simp [s3, State.tPush, State.updStk, State.updReg]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [s3, s2, State.tPush, State.updStk, State.updReg, hr2]
        · simp [s3, s2, State.tPush, State.updStk, State.updReg, hqk]
    have e2 : Eval main (.push k r) s2 s3 1 := by rw [← hpush]; exact eval_push main k r s2
    have e3 : Eval main (.set r tg) s3 s4 1 := by
      rw [show s4 = State.tSet s3 r tg from rfl]; exact eval_set main r tg s3
    have e23 : Eval main (.seq (.push k r) (.set r tg)) s2 s4 2 := Eval.seq e2 e3
    have eite : Eval main (.ite r tg (.seq (.push k r) (.set r tg)) (.set r Glyph.eos)) s2 s4 3 :=
      Eval.iteT hr2 e23
    have ebody : Eval main (dBody k tg r) s s4 4 := Eval.seq e1 eite
    have hr4 : s4.reg r ≠ Glyph.eos := by
      have h : s4.reg r = tg := by simp [s4, s3, s2, State.updStk, State.updReg]
      rw [h]; exact htg
    have hloop : Eval main (.loop r Glyph.eos (dBody k tg r)) s4 s4 1 := Eval.loopF hr4
    have hmain : Eval main (.loop r Glyph.eos (dBody k tg r)) s s4 6 :=
      Eval.loopT (r := r) (c := Glyph.eos) hr ebody hloop
    have hstate : dSt k tg r below s = s4 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [dSt, s4, s3, s2, State.updStk, State.updReg, hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [dSt, s4, s3, s2, State.updStk, State.updReg, hsk]
        · simp [dSt, s4, s3, s2, State.updStk, State.updReg, hsk, hqk]
    rw [hstate]
    exact hmain
  | cons g gs' ih =>
    intro below s hstk hT hr
    have hgT : g ≠ tg := hT g (by simp)
    have hgs' : ∀ g' ∈ gs', g' ≠ tg := fun g' h' => hT g' (List.mem_cons_of_mem g h')
    have hstk' : s.stk k = g :: (gs' ++ tg :: below) := by simpa using hstk
    let s2 : State := (s.updStk k (gs' ++ tg :: below)).updReg r g
    let s3 : State := s2.updReg r Glyph.eos
    have hpop : State.tPop s k r = s2 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [s2, State.tPop, State.updStk, State.updReg, hstk', hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [s2, State.tPop, State.updStk, State.updReg, hstk']
        · simp [s2, State.tPop, State.updStk, State.updReg, hstk', hqk]
    have e1 : Eval main (.pop k r) s s2 1 := by rw [← hpop]; exact eval_pop main k r s
    have hr2 : ¬ (s2.reg r = tg) := by
      have h : s2.reg r = g := by simp [s2, State.updStk, State.updReg]
      rw [h]; exact hgT
    have e3 : Eval main (.set r Glyph.eos) s2 s3 1 := by
      rw [show s3 = State.tSet s2 r Glyph.eos from rfl]; exact eval_set main r Glyph.eos s2
    have eite : Eval main (.ite r tg (.seq (.push k r) (.set r tg)) (.set r Glyph.eos)) s2 s3 2 :=
      Eval.iteF hr2 e3
    have ebody : Eval main (dBody k tg r) s s3 3 := Eval.seq e1 eite
    have hr3 : s3.reg r = Glyph.eos := by simp [s3, State.updStk, State.updReg]
    have hstk3 : s3.stk k = gs' ++ tg :: below := by
      simp only [s3, s2, State.updReg_stk, State.updStk_apply]
      simp
    have hrec := ih below s3 hstk3 hgs' hr3
    have hmain : Eval main (.loop r Glyph.eos (dBody k tg r)) s
        (dSt k tg r below s3) (3 + (4 * gs'.length + 6) + 1) :=
      Eval.loopT (r := r) (c := Glyph.eos) hr ebody hrec
    have hstate : dSt k tg r below s = dSt k tg r below s3 := by
      apply State.ext'
      · intro q
        by_cases hq : q = r <;> simp [dSt, s3, s2, State.updStk, State.updReg, hq]
      · intro q
        by_cases hqk : q = k
        · subst hqk; simp [dSt, s3, s2, State.updStk, State.updReg, hstk']
        · simp [dSt, s3, s2, State.updStk, State.updReg, hstk', hqk]
    rw [hstate]
    have hcost : 3 + (4 * gs'.length + 6) + 1 = 4 * (g :: gs').length + 6 := by simp; ring
    rwa [hcost] at hmain

/-- `dLoop` from an arbitrary state. -/
theorem dLoop_eval (main : Cmd) (k : Stk) (tg : Glyph) (r : Reg) (htg : tg ≠ Glyph.eos)
    (gs below : List Glyph) (s : State) (hstk : s.stk k = gs ++ tg :: below)
    (hT : ∀ g ∈ gs, g ≠ tg) :
    Eval main (dLoop k tg r) s (dSt k tg r below s) (4 * gs.length + 7) := by
  have h1 : Eval main (.set r Glyph.eos) s (s.updReg r Glyph.eos) 1 := eval_set main r Glyph.eos s
  have h2 : Eval main (.loop r Glyph.eos (dBody k tg r)) (s.updReg r Glyph.eos)
      (dSt k tg r below (s.updReg r Glyph.eos)) (4 * gs.length + 6) :=
    dLoopAux main k tg r htg gs below (s.updReg r Glyph.eos) (by simpa using hstk) hT
      (by simp [State.updReg])
  have h3 : dSt k tg r below (s.updReg r Glyph.eos) = dSt k tg r below s := by
    apply State.ext' <;> intro q
    · by_cases hq : q = r <;> simp [dSt, State.updStk, State.updReg, hq]
    · by_cases hqk : q = k <;> simp [dSt, State.updStk, State.updReg, hqk]
  rw [h3] at h2
  have h4 : Eval main (dLoop k tg r) s (dSt k tg r below s) (1 + (4 * gs.length + 6)) := Eval.seq h1 h2
  have h5 : 1 + (4 * gs.length + 6) = 4 * gs.length + 7 := by ring
  rwa [h5] at h4


/-! ## Value-level moves -/


/-- One step of `tLoop2`: as `tBody`, but the popped glyph is pushed onto two stacks. -/
def tBody2 (k : Stk) (tg : Glyph) (d1 d2 : Stk) (r : Reg) : Cmd :=
  .seq (.pop k r)
    (.ite r tg (.seq (.push k r) (.set r tg))
      (.seq (.seq (.push d1 r) (.push d2 r)) (.set r Glyph.eos)))

/-- `tBody2` iterated up to the frame marker `tg`. -/
def tLoop2 (k : Stk) (tg : Glyph) (d1 d2 : Stk) (r : Reg) : Cmd :=
  .seq (.set r Glyph.eos) (.loop r Glyph.eos (tBody2 k tg d1 d2 r))

/-- Loop lemma for `tLoop2`. -/
theorem tLoop2Aux (main : Cmd) (k : Stk) (tg : Glyph) (d1 d2 : Stk) (r : Reg)
    (h1 : d1 ≠ k) (h2 : d2 ≠ k) (h3 : d1 ≠ d2) (htg : tg ≠ Glyph.eos) :
    ∀ (gs below : List Glyph) (s : State), s.stk k = gs ++ tg :: below →
      (∀ g ∈ gs, g ≠ tg) → s.reg r = Glyph.eos →
      ∃ s' n, Eval main (.loop r Glyph.eos (tBody2 k tg d1 d2 r)) s s' n ∧ n ≤ 7 * gs.length + 7 ∧
        s'.stk k = tg :: below ∧ s'.stk d1 = gs.reverse ++ s.stk d1 ∧
        s'.stk d2 = gs.reverse ++ s.stk d2 ∧ s'.reg r = tg ∧
        (∀ j, j ≠ k → j ≠ d1 → j ≠ d2 → s'.stk j = s.stk j) := by
  intro gs
  induction gs with
  | nil =>
    intro below s hstk _ hr
    have hsk : s.stk k = tg :: below := by simpa using hstk
    let s1 : State := State.tPop s k r
    let s2 : State := State.tPush s1 k r
    let s3 : State := State.tSet s2 r tg
    have e1 : Eval main (.pop k r) s s1 1 := by
      rw [show s1 = State.tPop s k r from rfl]; exact eval_pop main k r s
    have hr1 : s1.reg r = tg := by
      rw [show s1 = State.tPop s k r from rfl, tPop_reg, if_pos rfl]; simp [hsk]
    have e2 : Eval main (.push k r) s1 s2 1 := by
      rw [show s2 = State.tPush s1 k r from rfl]; exact eval_push main k r s1
    have e3 : Eval main (.set r tg) s2 s3 1 := by
      rw [show s3 = State.tSet s2 r tg from rfl]; exact eval_set main r tg s2
    have e23 : Eval main (.seq (.push k r) (.set r tg)) s1 s3 2 := Eval.seq e2 e3
    have eit : Eval main (.ite r tg (.seq (.push k r) (.set r tg))
        (.seq (.seq (.push d1 r) (.push d2 r)) (.set r Glyph.eos))) s1 s3 3 :=
      Eval.iteT hr1 e23
    have ebody : Eval main (tBody2 k tg d1 d2 r) s s3 4 := Eval.seq e1 eit
    have hr3 : s3.reg r ≠ Glyph.eos := by
      rw [show s3 = State.tSet s2 r tg from rfl, tSet_reg, if_pos rfl]; exact htg
    have hmain : Eval main (.loop r Glyph.eos (tBody2 k tg d1 d2 r)) s s3 6 :=
      Eval.loopT hr ebody (Eval.loopF hr3)
    refine ⟨s3, 6, hmain, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show s3 = State.tSet s2 r tg from rfl, tSet_stk,
        show s2 = State.tPush s1 k r from rfl, tPush_stk, if_pos rfl]
      rw [hr1, show s1 = State.tPop s k r from rfl, tPop_stk, if_pos rfl]
      simp [hsk]
    · rw [show s3 = State.tSet s2 r tg from rfl, tSet_stk,
        show s2 = State.tPush s1 k r from rfl, tPush_stk, if_neg h1]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_neg h1]
      simp
    · rw [show s3 = State.tSet s2 r tg from rfl, tSet_stk,
        show s2 = State.tPush s1 k r from rfl, tPush_stk, if_neg h2]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_neg h2]
      simp
    · rw [show s3 = State.tSet s2 r tg from rfl, tSet_reg, if_pos rfl]
    · intro j hj1 hj2 hj3
      rw [show s3 = State.tSet s2 r tg from rfl, tSet_stk,
        show s2 = State.tPush s1 k r from rfl, tPush_stk, if_neg hj1]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_neg hj1]
  | cons g gs' ih =>
    intro below s hstk hT hr
    have hgT : g ≠ tg := hT g (by simp)
    have hgs' : ∀ g' ∈ gs', g' ≠ tg := fun g' h' => hT g' (List.mem_cons_of_mem g h')
    have hstk' : s.stk k = g :: (gs' ++ tg :: below) := by simpa using hstk
    let s1 : State := State.tPop s k r
    let s2 : State := State.tPush s1 d1 r
    let s3 : State := State.tPush s2 d2 r
    let s4 : State := State.tSet s3 r Glyph.eos
    have e1 : Eval main (.pop k r) s s1 1 := by
      rw [show s1 = State.tPop s k r from rfl]; exact eval_pop main k r s
    have hr1 : s1.reg r = g := by
      rw [show s1 = State.tPop s k r from rfl, tPop_reg, if_pos rfl]; simp [hstk']
    have e2 : Eval main (.push d1 r) s1 s2 1 := by
      rw [show s2 = State.tPush s1 d1 r from rfl]; exact eval_push main d1 r s1
    have hr2 : s2.reg r = g := by
      rw [show s2 = State.tPush s1 d1 r from rfl, tPush_reg]; exact hr1
    have e3 : Eval main (.push d2 r) s2 s3 1 := by
      rw [show s3 = State.tPush s2 d2 r from rfl]; exact eval_push main d2 r s2
    have e4 : Eval main (.set r Glyph.eos) s3 s4 1 := by
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl]; exact eval_set main r Glyph.eos s3
    have e23 : Eval main (.seq (.push d1 r) (.push d2 r)) s1 s3 2 := Eval.seq e2 e3
    have e234 : Eval main (.seq (.seq (.push d1 r) (.push d2 r)) (.set r Glyph.eos)) s1 s4 3 :=
      Eval.seq e23 e4
    have hgT' : ¬ (s1.reg r = tg) := by rw [hr1]; exact hgT
    have eit : Eval main (.ite r tg (.seq (.push k r) (.set r tg))
        (.seq (.seq (.push d1 r) (.push d2 r)) (.set r Glyph.eos))) s1 s4 4 :=
      Eval.iteF hgT' e234
    have ebody : Eval main (tBody2 k tg d1 d2 r) s s4 5 := Eval.seq e1 eit
    have hr4 : s4.reg r = Glyph.eos := by
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl, tSet_reg, if_pos rfl]
    have hstk4 : s4.stk k = gs' ++ tg :: below := by
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl, tSet_stk,
        show s3 = State.tPush s2 d2 r from rfl, tPush_stk, if_neg (Ne.symm h2),
        show s2 = State.tPush s1 d1 r from rfl, tPush_stk, if_neg (Ne.symm h1)]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_pos rfl]
      simp [hstk']
    obtain ⟨s', n, hev, hn, hk', hd1, hd2, hr', hoth⟩ := ih below s4 hstk4 hgs' hr4
    have hmain : Eval main (.loop r Glyph.eos (tBody2 k tg d1 d2 r)) s s' (5 + n + 1) :=
      Eval.loopT hr ebody hev
    refine ⟨s', 5 + n + 1, hmain, ?_, hk', ?_, ?_, hr', ?_⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · rw [hd1]
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl, tSet_stk,
        show s3 = State.tPush s2 d2 r from rfl, tPush_stk, if_neg h3,
        show s2 = State.tPush s1 d1 r from rfl, tPush_stk, if_pos rfl]
      rw [hr1]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_neg h1]
      rw [List.reverse_cons, List.append_assoc]
      simp
    · rw [hd2]
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl, tSet_stk,
        show s3 = State.tPush s2 d2 r from rfl, tPush_stk, if_pos rfl]
      rw [hr2]
      rw [show s2 = State.tPush s1 d1 r from rfl, tPush_stk, if_neg (Ne.symm h3)]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_neg h2]
      rw [List.reverse_cons, List.append_assoc]
      simp
    · intro j hj1 hj2 hj3
      rw [hoth j hj1 hj2 hj3]
      rw [show s4 = State.tSet s3 r Glyph.eos from rfl, tSet_stk,
        show s3 = State.tPush s2 d2 r from rfl, tPush_stk, if_neg hj3,
        show s2 = State.tPush s1 d1 r from rfl, tPush_stk, if_neg hj2]
      rw [show s1 = State.tPop s k r from rfl, tPop_stk, if_neg hj1]

/-- `tLoop2` from an arbitrary state (cost of the initial `set` included). -/
theorem tLoop2_eval (main : Cmd) (k : Stk) (tg : Glyph) (d1 d2 : Stk) (r : Reg)
    (h1 : d1 ≠ k) (h2 : d2 ≠ k) (h3 : d1 ≠ d2) (htg : tg ≠ Glyph.eos)
    (gs below : List Glyph) (s : State) (hstk : s.stk k = gs ++ tg :: below)
    (hT : ∀ g ∈ gs, g ≠ tg) :
    ∃ s' n, Eval main (tLoop2 k tg d1 d2 r) s s' n ∧ n ≤ 7 * gs.length + 8 ∧
      s'.stk k = tg :: below ∧ s'.stk d1 = gs.reverse ++ s.stk d1 ∧
      s'.stk d2 = gs.reverse ++ s.stk d2 ∧
      (∀ j, j ≠ k → j ≠ d1 → j ≠ d2 → s'.stk j = s.stk j) := by
  obtain ⟨s', n, hev, hn, hk, hd1, hd2, hr, hoth⟩ :=
    tLoop2Aux main k tg d1 d2 r h1 h2 h3 htg gs below (s.updReg r Glyph.eos)
      (by simpa using hstk) hT (by simp [State.updReg])
  refine ⟨s', 1 + n, ?_, by omega, hk, ?_, ?_, ?_⟩
  · exact Eval.seq (eval_set main r Glyph.eos s) hev
  · simpa using hd1
  · simpa using hd2
  · intro j hj1 hj2 hj3; exact hoth j hj1 hj2 hj3

/-- `storeMag src dst sgn rA rB` pops the sign glyph of the integer value on top of `src` and pushes
it onto `sgn`, then moves the bits of `|z|` to `dst` in reverse order (most significant first) above
the frame marker `gM`, then drops the `iend`. -/
def storeMag (src dst sgn : Stk) (rA rB : Reg) : Cmd :=
  .seq (.pop src rA)
   (.seq (.push sgn rA)
    (.seq (.set rB gM)
     (.seq (.push dst rB)
      (.seq (tLoop src Glyph.iend dst rB) (.pop src rA)))))

theorem storeMag_eval (main : Cmd) (src dst sgn : Stk) (rA rB : Reg)
    (h1 : dst ≠ src) (h2 : sgn ≠ src) (h3 : sgn ≠ dst)
    (sign : Glyph) (bits : List Bool) (below : List Glyph) (s : State)
    (hstk : s.stk src = sign :: (bits.map Glyph.bit ++ Glyph.iend :: below)) :
    ∃ s' n, Eval main (storeMag src dst sgn rA rB) s s' n ∧ n ≤ 5 * bits.length + 14 ∧
      s'.stk src = below ∧ s'.stk dst = bits.reverse.map Glyph.bit ++ gM :: s.stk dst ∧
      s'.stk sgn = sign :: s.stk sgn ∧
      (∀ j, j ≠ src → j ≠ dst → j ≠ sgn → s'.stk j = s.stk j) := by
  have h1' : dst ≠ src := h1
  have h2' : sgn ≠ src := h2
  have h3' : dst ≠ sgn := fun h => h3 h.symm
  have h1a : src ≠ dst := Ne.symm h1'
  have h2a : src ≠ sgn := Ne.symm h2'
  let s1 : State := State.tPop s src rA
  have e1 : Eval main (.pop src rA) s s1 1 := by
    rw [show s1 = State.tPop s src rA from rfl]; exact eval_pop main src rA s
  let s2 : State := State.tPush s1 sgn rA
  have e2 : Eval main (.push sgn rA) s1 s2 1 := by
    rw [show s2 = State.tPush s1 sgn rA from rfl]; exact eval_push main sgn rA s1
  let s3 : State := State.tSet s2 rB gM
  have e3 : Eval main (.set rB gM) s2 s3 1 := by
    rw [show s3 = State.tSet s2 rB gM from rfl]; exact eval_set main rB gM s2
  let s4 : State := State.tPush s3 dst rB
  have e4 : Eval main (.push dst rB) s3 s4 1 := by
    rw [show s4 = State.tPush s3 dst rB from rfl]; exact eval_push main dst rB s3
  have h4dst : s4.stk dst = gM :: s.stk dst := by
    rw [show s4 = State.tPush s3 dst rB from rfl, tPush_stk, if_pos rfl]
    have hg : s3.reg rB = gM := by
      rw [show s3 = State.tSet s2 rB gM from rfl, tSet_reg, if_pos rfl]
    rw [hg]
    congr 1
    rw [show s3 = State.tSet s2 rB gM from rfl, tSet_stk]
    rw [show s2 = State.tPush s1 sgn rA from rfl, tPush_stk, if_neg h3']
    rw [show s1 = State.tPop s src rA from rfl, tPop_stk, if_neg h1']
  have h4src : s4.stk src = bits.map Glyph.bit ++ Glyph.iend :: below := by
    rw [show s4 = State.tPush s3 dst rB from rfl, tPush_stk, if_neg h1a]
    rw [show s3 = State.tSet s2 rB gM from rfl, tSet_stk]
    rw [show s2 = State.tPush s1 sgn rA from rfl, tPush_stk, if_neg h2a]
    rw [show s1 = State.tPop s src rA from rfl, tPop_stk, if_pos rfl]
    simp [hstk]
  have hbits : ∀ g ∈ bits.map Glyph.bit, g ≠ Glyph.iend := by
    intro g hg
    obtain ⟨b, -, hb⟩ := List.mem_map.mp hg
    rw [← hb]; exact bit_ne_iend b
  let s5 : State := tSt src Glyph.iend dst rB (bits.map Glyph.bit) below s4
  have e5 : Eval main (tLoop src Glyph.iend dst rB) s4 s5 (5 * (bits.map Glyph.bit).length + 7) := by
    rw [show s5 = tSt src Glyph.iend dst rB (bits.map Glyph.bit) below s4 from rfl]
    exact tLoop_eval main src Glyph.iend dst rB h1 iend_ne_eos _ _ s4 h4src hbits
  let s6 : State := State.tPop s5 src rA
  have e6 : Eval main (.pop src rA) s5 s6 1 := by
    rw [show s6 = State.tPop s5 src rA from rfl]; exact eval_pop main src rA s5
  have eall : Eval main (storeMag src dst sgn rA rB) s s6
      (1 + (1 + (1 + (1 + ((5 * (bits.map Glyph.bit).length + 7) + 1))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))
  have hsrc : s6.stk src = below := by
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_pos rfl]
    rw [show s5 = tSt src Glyph.iend dst rB (bits.map Glyph.bit) below s4 from rfl]
    rw [tSt_stk_k _ _ _ _ _ _ _ h1']
    simp
  have hdst : s6.stk dst = bits.reverse.map Glyph.bit ++ gM :: s.stk dst := by
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_neg h1']
    rw [show s5 = tSt src Glyph.iend dst rB (bits.map Glyph.bit) below s4 from rfl, tSt_stk_dst]
    rw [List.map_reverse, h4dst]
  have hsgn : s6.stk sgn = sign :: s.stk sgn := by
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_neg h2']
    rw [show s5 = tSt src Glyph.iend dst rB (bits.map Glyph.bit) below s4 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ h2' h3]
    rw [show s4 = State.tPush s3 dst rB from rfl, tPush_stk, if_neg h3, tSet_stk]
    rw [show s2 = State.tPush s1 sgn rA from rfl, tPush_stk, if_pos rfl]
    congr 1
    · rw [show s1 = State.tPop s src rA from rfl, tPop_reg, if_pos rfl]
      simp [hstk]
    · rw [show s1 = State.tPop s src rA from rfl, tPop_stk, if_neg h2']
  have hother : ∀ j, j ≠ src → j ≠ dst → j ≠ sgn → s6.stk j = s.stk j := by
    intro j hj1 hj2 hj3
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_neg hj1]
    rw [show s5 = tSt src Glyph.iend dst rB (bits.map Glyph.bit) below s4 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ hj1 hj2]
    rw [show s4 = State.tPush s3 dst rB from rfl, tPush_stk, if_neg hj2, tSet_stk]
    rw [show s2 = State.tPush s1 sgn rA from rfl, tPush_stk, if_neg hj3]
    rw [show s1 = State.tPop s src rA from rfl, tPop_stk, if_neg hj1]
  refine ⟨s6, _, eall, ?_, hsrc, hdst, hsgn, hother⟩
  simp only [List.length_map]; omega

/-- `revMarked src dst rA rB` reverses the content above the frame marker `gM` of `src` onto `dst`
(the marker is kept on both stacks). -/
def revMarked (src dst : Stk) (rA rB : Reg) : Cmd :=
  .seq (.set rA gM) (.seq (.push dst rA) (.seq (tLoop src gM dst rB) (.pop src rA)))

theorem revMarked_eval (main : Cmd) (src dst : Stk) (rA rB : Reg) (h1 : dst ≠ src)
    (gs below : List Glyph) (hgs : ∀ g ∈ gs, g ≠ gM) (s : State)
    (hstk : s.stk src = gs ++ gM :: below) :
    ∃ s' n, Eval main (revMarked src dst rA rB) s s' n ∧ n ≤ 5 * gs.length + 13 ∧
      s'.stk src = below ∧ s'.stk dst = gs.reverse ++ gM :: s.stk dst ∧
      (∀ j, j ≠ src → j ≠ dst → s'.stk j = s.stk j) := by
  have h1a : src ≠ dst := Ne.symm h1
  let s1 : State := State.tSet s rA gM
  have e1 : Eval main (.set rA gM) s s1 1 := by
    rw [show s1 = State.tSet s rA gM from rfl]; exact eval_set main rA gM s
  let s2 : State := State.tPush s1 dst rA
  have e2 : Eval main (.push dst rA) s1 s2 1 := by
    rw [show s2 = State.tPush s1 dst rA from rfl]; exact eval_push main dst rA s1
  have h2dst : s2.stk dst = gM :: s.stk dst := by
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_pos rfl]
    have hg : s1.reg rA = gM := by
      rw [show s1 = State.tSet s rA gM from rfl, tSet_reg, if_pos rfl]
    rw [hg, show s1 = State.tSet s rA gM from rfl, tSet_stk]
  have h2src : s2.stk src = gs ++ gM :: below := by
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg h1a]
    rw [show s1 = State.tSet s rA gM from rfl, tSet_stk]
    exact hstk
  let s3 : State := tSt src gM dst rB gs below s2
  have e3 : Eval main (tLoop src gM dst rB) s2 s3 (5 * gs.length + 7) := by
    rw [show s3 = tSt src gM dst rB gs below s2 from rfl]
    exact tLoop_eval main src gM dst rB h1 gM_ne_eos _ _ s2 h2src hgs
  let s4 : State := State.tPop s3 src rA
  have e4 : Eval main (.pop src rA) s3 s4 1 := by
    rw [show s4 = State.tPop s3 src rA from rfl]; exact eval_pop main src rA s3
  have eall : Eval main (revMarked src dst rA rB) s s4 (1 + (1 + ((5 * gs.length + 7) + 1))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  have hsrc : s4.stk src = below := by
    rw [show s4 = State.tPop s3 src rA from rfl, tPop_stk, if_pos rfl]
    rw [show s3 = tSt src gM dst rB gs below s2 from rfl, tSt_stk_k _ _ _ _ _ _ _ h1]
    simp
  have hdst : s4.stk dst = gs.reverse ++ gM :: s.stk dst := by
    rw [show s4 = State.tPop s3 src rA from rfl, tPop_stk, if_neg h1]
    rw [show s3 = tSt src gM dst rB gs below s2 from rfl, tSt_stk_dst, h2dst]
  have hother : ∀ j, j ≠ src → j ≠ dst → s4.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s4 = State.tPop s3 src rA from rfl, tPop_stk, if_neg hj1]
    rw [show s3 = tSt src gM dst rB gs below s2 from rfl, tSt_stk_ne' _ _ _ _ _ _ _ hj1 hj2]
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg hj2]
    rw [show s1 = State.tSet s rA gM from rfl, tSet_stk]
  exact ⟨s4, _, eall, by omega, hsrc, hdst, hother⟩

/-- `dropMarked src rA rB` removes the content above the frame marker `gM` of `src`. -/
def dropMarked (src : Stk) (rA rB : Reg) : Cmd := .seq (dLoop src gM rB) (.pop src rA)

theorem dropMarked_eval (main : Cmd) (src : Stk) (rA rB : Reg)
    (gs below : List Glyph) (hgs : ∀ g ∈ gs, g ≠ gM) (s : State)
    (hstk : s.stk src = gs ++ gM :: below) :
    ∃ s' n, Eval main (dropMarked src rA rB) s s' n ∧ n ≤ 4 * gs.length + 9 ∧
      s'.stk src = below ∧ (∀ j, j ≠ src → s'.stk j = s.stk j) ∧
      (∀ r, r ≠ rA → r ≠ rB → s'.reg r = s.reg r) := by
  let s1 : State := dSt src gM rB below s
  have e1 : Eval main (dLoop src gM rB) s s1 (4 * gs.length + 7) := by
    rw [show s1 = dSt src gM rB below s from rfl]
    exact dLoop_eval main src gM rB gM_ne_eos gs below s hstk hgs
  let s2 : State := State.tPop s1 src rA
  have e2 : Eval main (.pop src rA) s1 s2 1 := by
    rw [show s2 = State.tPop s1 src rA from rfl]; exact eval_pop main src rA s1
  have eall : Eval main (dropMarked src rA rB) s s2 ((4 * gs.length + 7) + 1) := Eval.seq e1 e2
  have hsrc : s2.stk src = below := by
    rw [show s2 = State.tPop s1 src rA from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = dSt src gM rB below s from rfl, dSt_stk_k]
    simp
  have hother : ∀ j, j ≠ src → s2.stk j = s.stk j := by
    intro j hj
    rw [show s2 = State.tPop s1 src rA from rfl, tPop_stk, if_neg hj]
    rw [show s1 = dSt src gM rB below s from rfl, dSt_stk_ne' _ _ _ _ _ hj]
  have hreg : ∀ r, r ≠ rA → r ≠ rB → s2.reg r = s.reg r := by
    intro r hr1 hr2
    rw [show s2 = State.tPop s1 src rA from rfl, tPop_reg, if_neg hr1]
    rw [show s1 = dSt src gM rB below s from rfl, dSt_reg, if_neg hr2]
  exact ⟨s2, _, eall, by omega, hsrc, hother, hreg⟩


/-! ## The comparison flag -/

/-- Non-destructive copy: `src = gs ++ gM :: below` becomes `gs ++ gM :: src`; `dst` receives
`gs ++ gM :: dst` and `tmp` is restored. -/
def copyMarked2 (src dst tmp : Stk) (rA rB : Reg) : Cmd :=
  .seq (.set rA gM2) (.seq (.push tmp rA)
   (.seq (tLoop src gM tmp rB)
    (.seq (.set rA gM) (.seq (.push dst rA)
     (.seq (tLoop2 tmp gM2 src dst rB) (.pop tmp rA))))))

theorem copyMarked2_eval (main : Cmd) (src dst tmp : Stk) (rA rB : Reg)
    (h1 : dst ≠ src) (h2 : tmp ≠ src) (h3 : tmp ≠ dst) (h4 : src ≠ dst)
    (gs below : List Glyph) (hgs : ∀ g ∈ gs, g ≠ gM) (hgs2 : ∀ g ∈ gs, g ≠ gM2)
    (s : State) (hstk : s.stk src = gs ++ gM :: below) :
    ∃ s' n, Eval main (copyMarked2 src dst tmp rA rB) s s' n ∧ n ≤ 12 * gs.length + 24 ∧
      s'.stk src = gs ++ gM :: below ∧ s'.stk dst = gs ++ gM :: s.stk dst ∧
      s'.stk tmp = s.stk tmp ∧
      (∀ j, j ≠ src → j ≠ dst → j ≠ tmp → s'.stk j = s.stk j) := by
  have h2a : src ≠ tmp := Ne.symm h2
  let s1 : State := State.tSet s rA gM2
  have e1 : Eval main (.set rA gM2) s s1 1 := by
    rw [show s1 = State.tSet s rA gM2 from rfl]; exact eval_set main rA gM2 s
  let s2 : State := State.tPush s1 tmp rA
  have e2 : Eval main (.push tmp rA) s1 s2 1 := by
    rw [show s2 = State.tPush s1 tmp rA from rfl]; exact eval_push main tmp rA s1
  have h2tmp : s2.stk tmp = gM2 :: s.stk tmp := by
    rw [show s2 = State.tPush s1 tmp rA from rfl, tPush_stk, if_pos rfl]
    congr 1
    rw [show s1 = State.tSet s rA gM2 from rfl, tSet_reg, if_pos rfl]
  have h2src : s2.stk src = gs ++ gM :: below := by
    rw [show s2 = State.tPush s1 tmp rA from rfl, tPush_stk, if_neg h2a,
      show s1 = State.tSet s rA gM2 from rfl, tSet_stk]
    exact hstk
  have hev3 : Eval main (tLoop src gM tmp rB) s2 (tSt src gM tmp rB gs below s2)
      (5 * gs.length + 7) := tLoop_eval main src gM tmp rB h2 gM_ne_eos gs below s2 h2src hgs
  let s3 : State := tSt src gM tmp rB gs below s2
  have h3src : s3.stk src = gM :: below := by
    rw [show s3 = tSt src gM tmp rB gs below s2 from rfl, tSt_stk_k _ _ _ _ _ _ _ h2]
  have h3tmp : s3.stk tmp = gs.reverse ++ s2.stk tmp := by
    rw [show s3 = tSt src gM tmp rB gs below s2 from rfl, tSt_stk_dst]
  have hoth3 : ∀ j, j ≠ src → j ≠ tmp → s3.stk j = s2.stk j := by
    intro j hj1 hj2
    rw [show s3 = tSt src gM tmp rB gs below s2 from rfl, tSt_stk_ne' _ _ _ _ _ _ _ hj1 hj2]
  let s4 : State := State.tSet s3 rA gM
  have e4 : Eval main (.set rA gM) s3 s4 1 := by
    rw [show s4 = State.tSet s3 rA gM from rfl]; exact eval_set main rA gM s3
  let s5 : State := State.tPush s4 dst rA
  have e5 : Eval main (.push dst rA) s4 s5 1 := by
    rw [show s5 = State.tPush s4 dst rA from rfl]; exact eval_push main dst rA s4
  have h5dst : s5.stk dst = gM :: s.stk dst := by
    rw [show s5 = State.tPush s4 dst rA from rfl, tPush_stk, if_pos rfl]
    congr 1
    · rw [show s4 = State.tSet s3 rA gM from rfl, tSet_reg, if_pos rfl]
    · rw [show s4 = State.tSet s3 rA gM from rfl, tSet_stk,
        show s3 = tSt src gM tmp rB gs below s2 from rfl,
        tSt_stk_ne' _ _ _ _ _ _ _ (Ne.symm h4) (Ne.symm h3)]
      rw [show s2 = State.tPush s1 tmp rA from rfl, tPush_stk, if_neg (Ne.symm h3),
        show s1 = State.tSet s rA gM2 from rfl, tSet_stk]
  have h5tmp : s5.stk tmp = gs.reverse ++ gM2 :: s.stk tmp := by
    rw [show s5 = State.tPush s4 dst rA from rfl, tPush_stk, if_neg h3,
      show s4 = State.tSet s3 rA gM from rfl, tSet_stk, h3tmp, h2tmp]
  have h5src : s5.stk src = gM :: below := by
    rw [show s5 = State.tPush s4 dst rA from rfl, tPush_stk, if_neg h4,
      show s4 = State.tSet s3 rA gM from rfl, tSet_stk, h3src]
  have hgsM2 : ∀ g ∈ gs.reverse, g ≠ gM2 := by
    intro g hg; exact hgs2 g (by simpa using List.mem_reverse.mp hg)
  have hgsM : ∀ g ∈ gs.reverse, g ≠ gM := by
    intro g hg; exact hgs g (by simpa using List.mem_reverse.mp hg)
  obtain ⟨s6, n6, hev6, hn6, h6tmp, h6src, h6dst, hoth6⟩ :=
    tLoop2_eval main tmp gM2 src dst rB h2a (Ne.symm h3) h4 gM2_ne_eos
      gs.reverse (s.stk tmp) s5 h5tmp hgsM2
  let s7 : State := State.tPop s6 tmp rA
  have e7 : Eval main (.pop tmp rA) s6 s7 1 := by
    rw [show s7 = State.tPop s6 tmp rA from rfl]; exact eval_pop main tmp rA s6
  have eall : Eval main (copyMarked2 src dst tmp rA rB) s s7
      (1 + (1 + ((5 * gs.length + 7) + (1 + (1 + (n6 + 1)))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq hev3 (Eval.seq e4 (Eval.seq e5 (Eval.seq hev6 e7)))))
  have hsrc : s7.stk src = gs ++ gM :: below := by
    rw [show s7 = State.tPop s6 tmp rA from rfl, tPop_stk, if_neg h2a]
    rw [h6src]
    rw [h5src, List.reverse_reverse]
  have hdst : s7.stk dst = gs ++ gM :: s.stk dst := by
    rw [show s7 = State.tPop s6 tmp rA from rfl, tPop_stk, if_neg (Ne.symm h3)]
    rw [h6dst, h5dst, List.reverse_reverse]
  have htmp : s7.stk tmp = s.stk tmp := by
    rw [show s7 = State.tPop s6 tmp rA from rfl, tPop_stk, if_pos rfl]
    rw [h6tmp]
    simp
  have hother : ∀ j, j ≠ src → j ≠ dst → j ≠ tmp → s7.stk j = s.stk j := by
    intro j hj1 hj2 hj3
    rw [show s7 = State.tPop s6 tmp rA from rfl, tPop_stk, if_neg hj3]
    rw [hoth6 j hj3 hj1 hj2]
    rw [show s5 = State.tPush s4 dst rA from rfl, tPush_stk, if_neg hj2,
      show s4 = State.tSet s3 rA gM from rfl, tSet_stk]
    rw [hoth3 j hj1 hj3]
    rw [show s2 = State.tPush s1 tmp rA from rfl, tPush_stk, if_neg hj3,
      show s1 = State.tSet s rA gM2 from rfl, tSet_stk]
  refine ⟨s7, _, eall, ?_, hsrc, hdst, htmp, hother⟩
  have hn6' : n6 ≤ 7 * gs.length + 8 := by
    have := hn6; simp only [List.length_reverse] at this; exact this
  omega


/-! ## The sign-combining step -/

theorem natFlag_add (f : Glyph) (x y c : ℕ) (h : NatFlag f x y) :
    NatFlag f (x + c) (y + c) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by omega⟩
  · exact Or.inr (Or.inl ⟨h1, by omega⟩)
  · exact Or.inr (Or.inr ⟨h1, by omega⟩)

/-- In a canonical bit string of positive length the leading bit is `true`, so the value is at
least `2 ^ (length - 1)`. -/
theorem two_pow_pred_le_ofBits : ∀ (ys : List Bool), ys ≠ [] → IsBits ys →
    2 ^ (ys.length - 1) ≤ ofBits ys := by
  intro ys
  induction ys with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _ hb
    cases t with
    | nil =>
      rcases hb with h | h
      · exact absurd h (by simp)
      · simp only [List.length_cons, List.length_nil, List.getLast?_cons, List.nil_append] at h
        rw [Option.some.injEq] at h
        subst h
        norm_num [ofBits, List.foldr]
    | cons b t' =>
      have hb' : IsBits (b :: t') := by
        rcases hb with h | h
        · exact absurd h (by simp)
        · exact Or.inr (by simpa [List.getLast?_cons] using h)
      have h1 := ih (by simp) hb'
      have h2 : 2 ^ (List.length (a :: b :: t') - 1) = 2 * 2 ^ (List.length (b :: t') - 1) := by
        have e : List.length (a :: b :: t') - 1 = List.length (b :: t') := by simp
        have e2 : List.length (b :: t') - 1 = t'.length := by simp
        rw [e, e2]
        simp only [List.length_cons]
        rw [pow_succ]
        ring
      rw [h2]
      have h3 : (a :: b :: t').foldr (fun b r => b.toNat + 2 * r) 0
          = a.toNat + 2 * ((b :: t').foldr (fun b r => b.toNat + 2 * r) 0) := rfl
      rw [show ofBits (a :: b :: t') = a.toNat + 2 * ofBits (b :: t') from h3]
      have := Nat.zero_le a.toNat
      nlinarith [h1, this]

/-- Comparing canonical bit strings: the shorter one is the smaller number. -/
theorem ofBits_lt_of_length_lt {xs ys : List Bool} (hx : IsBits xs) (hy : IsBits ys)
    (h : xs.length < ys.length) : ofBits xs < ofBits ys := by
  have hyne : ys ≠ [] := by intro h'; simp [h'] at h
  have h1 : ofBits xs < 2 ^ xs.length := ofBits_lt_two_pow xs
  have h2 : 2 ^ xs.length ≤ 2 ^ (ys.length - 1) := by
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have h3 : 2 ^ (ys.length - 1) ≤ ofBits ys := two_pow_pred_le_ofBits ys hyne hy
  omega

theorem natFlag_of_not_lt {f : Glyph} {x y : ℕ} (hx : ¬ x < y) (hy : ¬ x = y) :
    NatFlag f x y → f = gGt := by
  intro h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h2 hx
  · exact absurd h2 hy
  · exact h1

/-! ## The parallel scan -/

theorem map_bit_ne_gM (l : List Bool) : ∀ x ∈ l.map Glyph.bit, x ≠ gM := by
  intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact fun h => gM_ne_bit b h.symm

theorem map_bit_ne_gM2 (l : List Bool) : ∀ x ∈ l.map Glyph.bit, x ≠ gM2 := by
  intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact fun h => gM2_ne_bit b h.symm


/-- Register holding the loop control of the scan (`eos` = continue). -/
def rCont : Reg := 3

/-- Register holding the comparison flag of the scan. -/
def rFlag : Reg := 4

end Work.Transform.Pw
