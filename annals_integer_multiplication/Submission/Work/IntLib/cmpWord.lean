import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.ofBits_bits

/-!
# `Work.IntLib.cmpWord`: negation, `max`, `<`, `=` on integer values

Raw StackLang programs (with `Eval` specifications and linear costs) implementing the four
integer words `neg`, `max`, `lt`, `eq` of `HvdH.IntLib` (see `Submission/HvdH/Interfaces.lean`).

The integer on top of the value stack 0 is encoded as
`[pos|neg] ++ (encodeNat |z|).map bit ++ [iend]`, least significant bit first.

Strategy.  Every binary word

* stores the two magnitudes on scratch stacks (`storeMag`): the glyphs are *reversed*, so that the
  stored bit string is most-significant-first, which is exactly the order in which it must be
  re-emitted to rebuild the encoding (`loadMarked`);
* copies them (`copyMarked`) and compares the copies (`revMarked` puts a copy back into
  least-significant-first order, `scanLoop` walks the two strings in parallel, keeping in a
  register the comparison of the prefixes read so far -- in LSB order the *last* difference is the
  most significant one);
* combines the sign glyphs with the magnitude comparison (`combine`), and finally either emits the
  constant `0`/`1` (`lt`/`eq`) or emits the larger of the two stored values (`max`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib


/-!
STATUS: COMPLETE.
==================
This file proves `Work.IntLib.cmpWord`, i.e. the four integer words of `HvdH.IntLib`
(negation, `max`, `<`, `=`) on the value stack, all with linear-in-`isz` costs.  Every declaration
below is proved outright (no gaps, no extra axioms).

All the reusable machinery lives in `namespace Work.IntLib.Cmp`:

* `tLoop`/`tLoopAux`/`tLoop_eval` (`tSt`): move the glyphs above a frame marker `tg` from one stack
  to another, reversing them, at cost `6 * len + 7`.  `dLoop`/`dLoopAux`/`dLoop_eval` (`dSt`):
  the same, discarding.  `tLoop2`/`tLoop2Aux`/`tLoop2_eval`: push each glyph onto *two* stacks.
* `storeMag_eval`: integer value on stack 0 -> magnitude (bits, reversed) on a scratch stack plus
  its sign glyph on another.  `revMarked_eval`: reverse a marked bit list.  `copyMarked_eval`
  (destructive) and `copyMarked2_eval` (non-destructive) copies.  `loadMarked_eval`: rebuild
  `(Val.int z).enc` from a stored magnitude plus a sign register.  `dropMarked_eval`: discard.
* `scanBody_*` (one step, all seven cases) + `scanAux` + `scanLoop_eval`: the parallel LSB-first scan
  of two marked bit strings, keeping the comparison of the prefixes read so far in `reg rFlag`;
  it stops at the first end-of-magnitude and is correct by `ofBits_lt_of_length_lt`
  (`two_pow_pred_le_ofBits`) and by overwriting the flag on every difference.  `scanLoop_eval` also
  records the length of the leftover glyphs above the frame markers, which is what makes the cost
  of the draining tails small.
* `cFlag`, `combineProg`, `combine_eval`, `combine_flag`: turn the two sign glyphs plus the
  magnitude comparison into `IntFlag (reg rRes) a b` (the `NatFlag` -> `IntFlag` case analysis).
* `storeMag_frame`: wrapper of `storeMag_eval` with the cost in terms of `isz`.
* `core_eval`: the common leading part of the four binary words (`coreProg`), composed with
  `Eval.seq` from `storeMag sPA/sSA` -> `storeMag sPB/sSB` -> `copyMarked2 sPA sCA sTA` ->
  `copyMarked2 sPB sCB sTB` -> `revMarked sCA sRA` -> `revMarked sCB sRB` -> `set rFlag gEq` ->
  `set rCont eos` -> `scanLoop` -> `pop sSA rSA` -> `pop sSB rSB` -> `combineProg`.  It leaves the
  comparison in `reg rRes` (`IntFlag`), the sign glyphs in `rSA`/`rSB` (`sg a`/`sg b`), and the two
  magnitudes (most significant first, above a frame marker) on `sPA`/`sPB`; the copies are drained
  by the tails.
* `cmpTailEval`: drain `sRA`, `sRB`, `sPA`, `sPB` and push `int 1`/`int 0` according to
  `reg rRes = g` (used with `g = gLt` for `<` and `g = gEq` for `=`).
* `maxTailEval`: drain `sRA`, `sRB`, load the larger of the two magnitudes from `sPB` (when
  `rRes = gLt`) or from `sPA`, and drop the other.
* `negProg_eval`: pop the sign glyph, `peek` the next one; `neg` -> `pos`; `pos` followed by `iend`
  (i.e. `a = 0`) -> `pos`; otherwise -> `neg`; cost `<= 6 <= 4 * isz a`.
* `negWord`, `ltWord`, `eqWord`, `maxWord`: the four `UnOp`/`BinOp` statements with cost
  `4 * isz a` resp. `200 * (isz a + isz b)`, each obtained by composing `core_eval` with the
  matching tail and re-reading the answer with `IntFlag.lt_iff`/`IntFlag.eq_iff`.

The final theorem `Work.IntLib.cmpWord` (outside `Cmp`, so that it lands in this file's namespace)
is `⟨negWord, maxWord, ltWord, eqWord⟩`.
-/

namespace Cmp

open HvdH
open Work.Kernel

/-! ## Glyphs, stacks, registers -/

/-- Frame marker used on every scratch stack. -/
def gM : Glyph := .mk 5
/-- `reg rCont` value that stops the scan loop. -/
def gStop : Glyph := .mk 6
/-- `reg rFlag` value: "less". -/
def gLt : Glyph := .mk 7
/-- `reg rFlag` value: "greater". -/
def gGt : Glyph := .mk 8
/-- `reg rFlag` value: "equal". -/
def gEq : Glyph := .mk 9

/-- Scratch stack holding the magnitude of the top value. -/
def sPA : Stk := 1
/-- Scratch stack holding the magnitude of the second value. -/
def sPB : Stk := 2
/-- Scratch stack holding the sign glyph of the top value. -/
def sSA : Stk := 3
/-- Scratch stack holding the sign glyph of the second value. -/
def sSB : Stk := 4
/-- Copy of `sPA` (consumed by the scan). -/
def sCA : Stk := 5
/-- Copy of `sPB` (consumed by the scan). -/
def sCB : Stk := 6
/-- LSB-first copy of `sPA` (consumed by the scan). -/
def sRA : Stk := 7
/-- LSB-first copy of `sPB` (consumed by the scan). -/
def sRB : Stk := 8
/-- Temporary stack of `copyMarked`. -/
def sTA : Stk := 9
/-- Temporary stack of `copyMarked`. -/
def sTB : Stk := 10

def rA : Reg := 0
def rB : Reg := 1
def rC : Reg := 2
def rCont : Reg := 3
def rFlag : Reg := 4
def rRes : Reg := 5
def rSA : Reg := 6
def rSB : Reg := 7
def rT : Reg := 8

/-! ## Basic glyph facts -/

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

/-- Second frame marker (used by `copyMarked`). -/
def gM2 : Glyph := .mk 10

theorem gM2_ne_eos : gM2 ≠ Glyph.eos := by decide
theorem gM2_ne_gM : gM2 ≠ gM := by decide
theorem gM_ne_gM2 : gM ≠ gM2 := gM2_ne_gM.symm
theorem bit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := by intro h; exact nomatch h
theorem iend_ne_eos : Glyph.iend ≠ Glyph.eos := by decide
theorem iend_ne_bit (b : Bool) : Glyph.iend ≠ Glyph.bit b := fun h => bit_ne_iend b h.symm

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

/-- `copyMarked src dst tmp rA rB rC`: `src = gs ++ gM :: below`; afterwards `src` is `below`,
`dst` is `gs ++ gM :: dst` (a copy, same orientation) and `tmp` is restored. -/
def copyMarked (src dst tmp : Stk) (rA rB rC : Reg) : Cmd :=
  .seq (.set rA gM) (.seq (.push dst rA)
   (.seq (.set rA gM2) (.seq (.push tmp rA)
    (.seq (tLoop src gM tmp rB) (.seq (.pop src rA)
      (.seq (tLoop tmp gM2 dst rC) (.pop tmp rA)))))))

theorem copyMarked_eval (main : Cmd) (src dst tmp : Stk) (rA rB rC : Reg)
    (h1 : dst ≠ src) (h2 : tmp ≠ src) (h3 : tmp ≠ dst)
    (gs below : List Glyph) (hgs : ∀ g ∈ gs, g ≠ gM) (hgs2 : ∀ g ∈ gs, g ≠ gM2) (s : State)
    (hstk : s.stk src = gs ++ gM :: below) :
    ∃ s' n, Eval main (copyMarked src dst tmp rA rB rC) s s' n ∧ n ≤ 10 * gs.length + 22 ∧
      s'.stk src = below ∧ s'.stk dst = gs ++ gM :: s.stk dst ∧ s'.stk tmp = s.stk tmp ∧
      (∀ j, j ≠ src → j ≠ dst → j ≠ tmp → s'.stk j = s.stk j) := by
  have h1a : src ≠ dst := Ne.symm h1
  have h2a : src ≠ tmp := Ne.symm h2
  have h3a : dst ≠ tmp := Ne.symm h3
  let s1 : State := State.tSet s rA gM
  have e1 : Eval main (.set rA gM) s s1 1 := by
    rw [show s1 = State.tSet s rA gM from rfl]; exact eval_set main rA gM s
  let s2 : State := State.tPush s1 dst rA
  have e2 : Eval main (.push dst rA) s1 s2 1 := by
    rw [show s2 = State.tPush s1 dst rA from rfl]; exact eval_push main dst rA s1
  let s3 : State := State.tSet s2 rA gM2
  have e3 : Eval main (.set rA gM2) s2 s3 1 := by
    rw [show s3 = State.tSet s2 rA gM2 from rfl]; exact eval_set main rA gM2 s2
  let s4 : State := State.tPush s3 tmp rA
  have e4 : Eval main (.push tmp rA) s3 s4 1 := by
    rw [show s4 = State.tPush s3 tmp rA from rfl]; exact eval_push main tmp rA s3
  have h4dst : s4.stk dst = gM :: s.stk dst := by
    rw [show s4 = State.tPush s3 tmp rA from rfl, tPush_stk, if_neg h3a]
    rw [show s3 = State.tSet s2 rA gM2 from rfl, tSet_stk]
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_pos rfl]
    congr 1
    rw [show s1 = State.tSet s rA gM from rfl, tSet_reg, if_pos rfl]
  have h4tmp : s4.stk tmp = gM2 :: s.stk tmp := by
    rw [show s4 = State.tPush s3 tmp rA from rfl, tPush_stk, if_pos rfl]
    congr 1
    · rw [show s3 = State.tSet s2 rA gM2 from rfl, tSet_reg, if_pos rfl]
    · rw [show s3 = State.tSet s2 rA gM2 from rfl, tSet_stk]
      rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg h3]
      rw [show s1 = State.tSet s rA gM from rfl, tSet_stk]
  have h4src : s4.stk src = gs ++ gM :: below := by
    rw [show s4 = State.tPush s3 tmp rA from rfl, tPush_stk, if_neg h2a]
    rw [show s3 = State.tSet s2 rA gM2 from rfl, tSet_stk]
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg h1a]
    rw [show s1 = State.tSet s rA gM from rfl, tSet_stk]
    exact hstk
  let s5 : State := tSt src gM tmp rB gs below s4
  have e5 : Eval main (tLoop src gM tmp rB) s4 s5 (5 * gs.length + 7) := by
    rw [show s5 = tSt src gM tmp rB gs below s4 from rfl]
    exact tLoop_eval main src gM tmp rB h2 gM_ne_eos _ _ s4 h4src hgs
  let s6 : State := State.tPop s5 src rA
  have e6 : Eval main (.pop src rA) s5 s6 1 := by
    rw [show s6 = State.tPop s5 src rA from rfl]; exact eval_pop main src rA s5
  have h6tmp : s6.stk tmp = gs.reverse ++ gM2 :: s.stk tmp := by
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_neg h2]
    rw [show s5 = tSt src gM tmp rB gs below s4 from rfl, tSt_stk_dst]
    rw [h4tmp]
  have hgsM2 : ∀ g ∈ gs.reverse, g ≠ gM2 := by
    intro g hg; exact hgs2 g (by simpa using List.mem_reverse.mp hg)
  let s7 : State := tSt tmp gM2 dst rC gs.reverse (s.stk tmp) s6
  have e7 : Eval main (tLoop tmp gM2 dst rC) s6 s7 (5 * gs.reverse.length + 7) := by
    rw [show s7 = tSt tmp gM2 dst rC gs.reverse (s.stk tmp) s6 from rfl]
    exact tLoop_eval main tmp gM2 dst rC h3a gM2_ne_eos _ _ s6 h6tmp hgsM2
  let s8 : State := State.tPop s7 tmp rA
  have e8 : Eval main (.pop tmp rA) s7 s8 1 := by
    rw [show s8 = State.tPop s7 tmp rA from rfl]; exact eval_pop main tmp rA s7
  have eall : Eval main (copyMarked src dst tmp rA rB rC) s s8
      (1 + (1 + (1 + (1 + ((5 * gs.length + 7) + (1 + ((5 * gs.reverse.length + 7) + 1))))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 (Eval.seq e7 e8))))))
  have hsrc : s8.stk src = below := by
    rw [show s8 = State.tPop s7 tmp rA from rfl, tPop_stk, if_neg h2a]
    rw [show s7 = tSt tmp gM2 dst rC gs.reverse (s.stk tmp) s6 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ h2a h1a]
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_pos rfl]
    rw [show s5 = tSt src gM tmp rB gs below s4 from rfl, tSt_stk_k _ _ _ _ _ _ _ h2]
    simp
  have hdst : s8.stk dst = gs ++ gM :: s.stk dst := by
    rw [show s8 = State.tPop s7 tmp rA from rfl, tPop_stk, if_neg h3a]
    rw [show s7 = tSt tmp gM2 dst rC gs.reverse (s.stk tmp) s6 from rfl, tSt_stk_dst]
    rw [List.reverse_reverse]
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_neg h1]
    rw [show s5 = tSt src gM tmp rB gs below s4 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ h1 h3a]
    rw [h4dst]
  have htmp : s8.stk tmp = s.stk tmp := by
    rw [show s8 = State.tPop s7 tmp rA from rfl, tPop_stk, if_pos rfl]
    rw [show s7 = tSt tmp gM2 dst rC gs.reverse (s.stk tmp) s6 from rfl,
      tSt_stk_k _ _ _ _ _ _ _ h3a]
    simp
  have hother : ∀ j, j ≠ src → j ≠ dst → j ≠ tmp → s8.stk j = s.stk j := by
    intro j hj1 hj2 hj3
    rw [show s8 = State.tPop s7 tmp rA from rfl, tPop_stk, if_neg hj3]
    rw [show s7 = tSt tmp gM2 dst rC gs.reverse (s.stk tmp) s6 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ hj3 hj2]
    rw [show s6 = State.tPop s5 src rA from rfl, tPop_stk, if_neg hj1]
    rw [show s5 = tSt src gM tmp rB gs below s4 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ hj1 hj3]
    rw [show s4 = State.tPush s3 tmp rA from rfl, tPush_stk, if_neg hj3]
    rw [show s3 = State.tSet s2 rA gM2 from rfl, tSet_stk]
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg hj2]
    rw [show s1 = State.tSet s rA gM from rfl, tSet_stk]
  refine ⟨s8, _, eall, ?_, hsrc, hdst, htmp, hother⟩
  simp only [List.length_reverse]; omega

/-- `loadMarked src dst sgn rA rB` rebuilds, on `dst`, the encoding of the integer whose bits are
stored (most significant first) above the frame marker of `src`, with sign glyph `reg sgn`. -/
def loadMarked (src dst : Stk) (sgn : Reg) (rA rB : Reg) : Cmd :=
  .seq (.set rA Glyph.iend) (.seq (.push dst rA)
   (.seq (tLoop src gM dst rB) (.seq (.pop src rA) (.push dst sgn))))

theorem loadMarked_eval (main : Cmd) (src dst : Stk) (sgn : Reg) (rA rB : Reg) (h1 : dst ≠ src)
    (h4r : sgn ≠ rA) (h5r : sgn ≠ rB)
    (z : ℤ) (bits : List Bool) (below : List Glyph) (s : State)
    (hsgn : s.reg sgn = (if z < 0 then Glyph.neg else Glyph.pos))
    (hstk : s.stk src = bits.reverse.map Glyph.bit ++ gM :: below)
    (hbits : bits = Computability.encodeNat z.natAbs) :
    ∃ s' n, Eval main (loadMarked src dst sgn rA rB) s s' n ∧ n ≤ 5 * bits.length + 12 ∧
      s'.stk src = below ∧ s'.stk dst = (Val.int z).enc ++ s.stk dst ∧
      (∀ j, j ≠ src → j ≠ dst → s'.stk j = s.stk j) := by
  have h1a : src ≠ dst := Ne.symm h1
  let s1 : State := State.tSet s rA Glyph.iend
  have e1 : Eval main (.set rA Glyph.iend) s s1 1 := by
    rw [show s1 = State.tSet s rA Glyph.iend from rfl]; exact eval_set main rA Glyph.iend s
  let s2 : State := State.tPush s1 dst rA
  have e2 : Eval main (.push dst rA) s1 s2 1 := by
    rw [show s2 = State.tPush s1 dst rA from rfl]; exact eval_push main dst rA s1
  have h2dst : s2.stk dst = Glyph.iend :: s.stk dst := by
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_pos rfl]
    congr 1
    rw [show s1 = State.tSet s rA Glyph.iend from rfl, tSet_reg, if_pos rfl]
  have h2src : s2.stk src = bits.reverse.map Glyph.bit ++ gM :: below := by
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg h1a]
    rw [show s1 = State.tSet s rA Glyph.iend from rfl, tSet_stk]
    exact hstk
  have hbitsM : ∀ g ∈ bits.reverse.map Glyph.bit, g ≠ gM := by
    intro g hg
    obtain ⟨b, -, hb⟩ := List.mem_map.mp hg
    rw [← hb]; exact fun h => gM_ne_bit b h.symm
  let s3 : State := tSt src gM dst rB (bits.reverse.map Glyph.bit) below s2
  have e3 : Eval main (tLoop src gM dst rB) s2 s3 (5 * (bits.reverse.map Glyph.bit).length + 7) := by
    rw [show s3 = tSt src gM dst rB (bits.reverse.map Glyph.bit) below s2 from rfl]
    exact tLoop_eval main src gM dst rB h1 gM_ne_eos _ _ s2 h2src hbitsM
  let s4 : State := State.tPop s3 src rA
  have e4 : Eval main (.pop src rA) s3 s4 1 := by
    rw [show s4 = State.tPop s3 src rA from rfl]; exact eval_pop main src rA s3
  let s5 : State := State.tPush s4 dst sgn
  have e5 : Eval main (.push dst sgn) s4 s5 1 := by
    rw [show s5 = State.tPush s4 dst sgn from rfl]; exact eval_push main dst sgn s4
  have eall : Eval main (loadMarked src dst sgn rA rB) s s5
      (1 + (1 + ((5 * (bits.reverse.map Glyph.bit).length + 7) + (1 + 1)))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))
  have hsrc : s5.stk src = below := by
    rw [show s5 = State.tPush s4 dst sgn from rfl, tPush_stk, if_neg h1a]
    rw [show s4 = State.tPop s3 src rA from rfl, tPop_stk, if_pos rfl]
    rw [show s3 = tSt src gM dst rB (bits.reverse.map Glyph.bit) below s2 from rfl,
      tSt_stk_k _ _ _ _ _ _ _ h1]
    simp
  have hdst : s5.stk dst = (Val.int z).enc ++ s.stk dst := by
    rw [show s5 = State.tPush s4 dst sgn from rfl, tPush_stk, if_pos rfl]
    congr 1
    · rw [show s4 = State.tPop s3 src rA from rfl, tPop_reg, if_neg h4r]
      rw [show s3 = tSt src gM dst rB (bits.reverse.map Glyph.bit) below s2 from rfl,
        tSt_reg, if_neg h5r]
      rw [show s2 = State.tPush s1 dst rA from rfl, tPush_reg]
      rw [show s1 = State.tSet s rA Glyph.iend from rfl, tSet_reg, if_neg h4r]
      exact hsgn
    · rw [show s4 = State.tPop s3 src rA from rfl, tPop_stk, if_neg h1]
      rw [show s3 = tSt src gM dst rB (bits.reverse.map Glyph.bit) below s2 from rfl, tSt_stk_dst]
      rw [List.map_reverse]
      rw [h2dst]
      rw [List.reverse_reverse]
      rw [hbits]
      simp [Val.enc]
  have hother : ∀ j, j ≠ src → j ≠ dst → s5.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s5 = State.tPush s4 dst sgn from rfl, tPush_stk, if_neg hj2]
    rw [show s4 = State.tPop s3 src rA from rfl, tPop_stk, if_neg hj1]
    rw [show s3 = tSt src gM dst rB (bits.reverse.map Glyph.bit) below s2 from rfl,
      tSt_stk_ne' _ _ _ _ _ _ _ hj1 hj2]
    rw [show s2 = State.tPush s1 dst rA from rfl, tPush_stk, if_neg hj2]
    rw [show s1 = State.tSet s rA Glyph.iend from rfl, tSet_stk]
  refine ⟨s5, _, eall, ?_, hsrc, hdst, hother⟩
  simp only [List.length_map, List.length_reverse]; omega

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

/-- `NatFlag f x y` says that the glyph `f` records the comparison of the naturals `x` and `y`. -/
def NatFlag (f : Glyph) (x y : ℕ) : Prop :=
  (f = gLt ∧ x < y) ∨ (f = gEq ∧ x = y) ∨ (f = gGt ∧ y < x)

/-- `IntFlag f a b` says that the glyph `f` records the comparison of the integers `a` and `b`. -/
def IntFlag (f : Glyph) (a b : ℤ) : Prop :=
  (f = gLt ∧ a < b) ∨ (f = gEq ∧ a = b) ∨ (f = gGt ∧ b < a)

theorem ofBits_nil : ofBits ([] : List Bool) = 0 := rfl

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

/-- One step of the comparison scan. -/
def scanBody : Cmd :=
  .seq (.pop sRA rA)
   (.seq (.pop sRB rB)
     (.ite rA gM
       (.ite rB gM
          (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
          (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
       (.ite rB gM
          (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
          (.ite rA (Glyph.bit true)
             (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
                (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
             (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
                (.set rCont Glyph.eos))))))

/-- The comparison scan, iterated until `reg rCont ≠ eos`. -/
def scanLoop : Cmd := .loop rCont Glyph.eos scanBody

theorem rA_ne_rB : rA ≠ rB := by decide
theorem rA_ne_rCont : rA ≠ rCont := by decide
theorem rB_ne_rCont : rB ≠ rCont := by decide
theorem rFlag_ne_rA : rFlag ≠ rA := by decide
theorem rFlag_ne_rB : rFlag ≠ rB := by decide
theorem rFlag_ne_rCont : rFlag ≠ rCont := by decide
theorem rA_ne_rFlag : rA ≠ rFlag := by decide
theorem rB_ne_rFlag : rB ≠ rFlag := by decide
theorem rCont_ne_rA : rCont ≠ rA := by decide
theorem rCont_ne_rB : rCont ≠ rB := by decide
theorem sRA_ne_sRB : sRA ≠ sRB := by decide
theorem sRB_ne_sRA : sRB ≠ sRA := by decide

/-- One body step, case `rA = rB = gM` (both magnitudes exhausted). -/
theorem scanBody_mm (main : Cmd) (RA0 RB0 : List Glyph) (s : State)
    (hA : s.stk sRA = gM :: RA0) (hB : s.stk sRB = gM :: RB0) :
    ∃ s' n, Eval main scanBody s s' n ∧ n ≤ 9 ∧
      s'.stk sRA = gM :: RA0 ∧ s'.stk sRB = gM :: RB0 ∧
      s'.reg rCont = gStop ∧ s'.reg rFlag = s.reg rFlag ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sRA rA
  have e1 : Eval main (.pop sRA rA) s s1 1 := by
    rw [show s1 = State.tPop s sRA rA from rfl]; exact eval_pop main sRA rA s
  let s2 : State := State.tPop s1 sRB rB
  have e2 : Eval main (.pop sRB rB) s1 s2 1 := by
    rw [show s2 = State.tPop s1 sRB rB from rfl]; exact eval_pop main sRB rB s1
  have h2A : s2.reg rA = gM := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rA_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_pos rfl]
    simp [hA]
  have h2B : s2.reg rB = gM := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  let t1 : State := State.tPush s2 sRA rA
  let s3 : State := State.tPush t1 sRB rB
  let s4 : State := State.tSet s3 rCont gStop
  have e3 : Eval main (.push sRA rA) s2 t1 1 := by
    rw [show t1 = State.tPush s2 sRA rA from rfl]; exact eval_push main sRA rA s2
  have e4 : Eval main (.push sRB rB) t1 s3 1 := by
    rw [show s3 = State.tPush t1 sRB rB from rfl]; exact eval_push main sRB rB t1
  have e5 : Eval main (.set rCont gStop) s3 s4 1 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl]; exact eval_set main rCont gStop s3
  have e45 : Eval main (.seq (.push sRB rB) (.set rCont gStop)) t1 s4 2 := Eval.seq e4 e5
  have e345 : Eval main (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop))) s2 s4 3 :=
    Eval.seq e3 e45
  have eitB : Eval main (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
      (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop)))) s2 s4 4 :=
    Eval.iteT h2B e345
  have ebig : Eval main (.ite rA gM
      (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
        (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
      (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
        (.ite rA (Glyph.bit true)
          (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
            (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
          (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
            (.set rCont Glyph.eos))))) s2 s4 5 :=
    Eval.iteT h2A eitB
  have ebody : Eval main scanBody s s4 7 := Eval.seq e1 (Eval.seq e2 ebig)
  have h4A : s4.stk sRA = gM :: RA0 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk]
    rw [show s3 = State.tPush t1 sRB rB from rfl, tPush_stk, if_neg sRA_ne_sRB]
    rw [show t1 = State.tPush s2 sRA rA from rfl, tPush_stk, if_pos rfl]
    have h : s2.reg rA = gM := h2A
    rw [h]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg sRA_ne_sRB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_pos rfl]
    simp [hA]
  have h4B : s4.stk sRB = gM :: RB0 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk]
    rw [show s3 = State.tPush t1 sRB rB from rfl, tPush_stk, if_pos rfl]
    have h : t1.reg rB = gM := by
      rw [show t1 = State.tPush s2 sRA rA from rfl, tPush_reg]
      exact h2B
    rw [h]
    rw [show t1 = State.tPush s2 sRA rA from rfl, tPush_stk, if_neg sRB_ne_sRA]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h4cont : s4.reg rCont = gStop := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_reg, if_pos rfl]
  have h4flag : s4.reg rFlag = s.reg rFlag := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_reg, if_neg rFlag_ne_rCont]
    rw [show s3 = State.tPush t1 sRB rB from rfl, tPush_reg]
    rw [show t1 = State.tPush s2 sRA rA from rfl, tPush_reg]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rFlag_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_neg rFlag_ne_rA]
  have h4other : ∀ j, j ≠ sRA → j ≠ sRB → s4.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tPush t1 sRB rB from rfl, tPush_stk, if_neg hj2,
      show t1 = State.tPush s2 sRA rA from rfl, tPush_stk, if_neg hj1,
      show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg hj2,
      show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg hj1]
  exact ⟨s4, 7, ebody, by omega, h4A, h4B, h4cont, h4flag, h4other⟩

/-- One body step, case `rA = gM`, `rB` a bit: the A-magnitude is exhausted. -/
theorem scanBody_mb (main : Cmd) (bB : Bool) (tB : List Bool) (RA0 RB0 : List Glyph) (s : State)
    (hA : s.stk sRA = gM :: RA0)
    (hB : s.stk sRB = Glyph.bit bB :: tB.map Glyph.bit ++ gM :: RB0) :
    ∃ s' n, Eval main scanBody s s' n ∧ n ≤ 9 ∧
      s'.stk sRA = gM :: RA0 ∧ s'.stk sRB = tB.map Glyph.bit ++ gM :: RB0 ∧
      s'.reg rCont = gStop ∧ s'.reg rFlag = gLt ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sRA rA
  have e1 : Eval main (.pop sRA rA) s s1 1 := by
    rw [show s1 = State.tPop s sRA rA from rfl]; exact eval_pop main sRA rA s
  let s2 : State := State.tPop s1 sRB rB
  have e2 : Eval main (.pop sRB rB) s1 s2 1 := by
    rw [show s2 = State.tPop s1 sRB rB from rfl]; exact eval_pop main sRB rB s1
  have h2A : s2.reg rA = gM := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rA_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_pos rfl]
    simp [hA]
  have h2B : ¬ (s2.reg rB = gM) := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp only [hB, List.headD_cons]
    exact fun h => gM_ne_bit bB h.symm
  let t1 : State := State.tPush s2 sRA rA
  let s3 : State := State.tSet t1 rFlag gLt
  let s4 : State := State.tSet s3 rCont gStop
  have e3 : Eval main (.push sRA rA) s2 t1 1 := by
    rw [show t1 = State.tPush s2 sRA rA from rfl]; exact eval_push main sRA rA s2
  have e4 : Eval main (.set rFlag gLt) t1 s3 1 := by
    rw [show s3 = State.tSet t1 rFlag gLt from rfl]; exact eval_set main rFlag gLt t1
  have e5 : Eval main (.set rCont gStop) s3 s4 1 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl]; exact eval_set main rCont gStop s3
  have e45 : Eval main (.seq (.set rFlag gLt) (.set rCont gStop)) t1 s4 2 := Eval.seq e4 e5
  have e345 : Eval main (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))) s2 s4 3 :=
    Eval.seq e3 e45
  have eitB : Eval main (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
      (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop)))) s2 s4 4 :=
    Eval.iteF h2B e345
  have ebig : Eval main (.ite rA gM
      (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
        (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
      (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
        (.ite rA (Glyph.bit true)
          (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
            (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
          (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
            (.set rCont Glyph.eos))))) s2 s4 5 :=
    Eval.iteT h2A eitB
  have ebody : Eval main scanBody s s4 7 := Eval.seq e1 (Eval.seq e2 ebig)
  have h4A : s4.stk sRA = gM :: RA0 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tSet t1 rFlag gLt from rfl, tSet_stk]
    rw [show t1 = State.tPush s2 sRA rA from rfl, tPush_stk, if_pos rfl]
    rw [h2A]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg sRA_ne_sRB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_pos rfl]
    simp [hA]
  have h4B : s4.stk sRB = tB.map Glyph.bit ++ gM :: RB0 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tSet t1 rFlag gLt from rfl, tSet_stk]
    rw [show t1 = State.tPush s2 sRA rA from rfl, tPush_stk, if_neg sRB_ne_sRA]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h4cont : s4.reg rCont = gStop := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_reg, if_pos rfl]
  have h4flag : s4.reg rFlag = gLt := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_reg, if_neg rFlag_ne_rCont]
    rw [show s3 = State.tSet t1 rFlag gLt from rfl, tSet_reg, if_pos rfl]
  have h4other : ∀ j, j ≠ sRA → j ≠ sRB → s4.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tSet t1 rFlag gLt from rfl, tSet_stk,
      show t1 = State.tPush s2 sRA rA from rfl, tPush_stk, if_neg hj1,
      show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg hj2,
      show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg hj1]
  exact ⟨s4, 7, ebody, by omega, h4A, h4B, h4cont, h4flag, h4other⟩

/-- One body step, case `rB = gM`, `rA` a bit: the B-magnitude is exhausted. -/
theorem scanBody_bm (main : Cmd) (bA : Bool) (tA : List Bool) (RA0 RB0 : List Glyph) (s : State)
    (hA : s.stk sRA = Glyph.bit bA :: tA.map Glyph.bit ++ gM :: RA0)
    (hB : s.stk sRB = gM :: RB0) :
    ∃ s' n, Eval main scanBody s s' n ∧ n ≤ 9 ∧
      s'.stk sRA = tA.map Glyph.bit ++ gM :: RA0 ∧ s'.stk sRB = gM :: RB0 ∧
      s'.reg rCont = gStop ∧ s'.reg rFlag = gGt ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sRA rA
  have e1 : Eval main (.pop sRA rA) s s1 1 := by
    rw [show s1 = State.tPop s sRA rA from rfl]; exact eval_pop main sRA rA s
  let s2 : State := State.tPop s1 sRB rB
  have e2 : Eval main (.pop sRB rB) s1 s2 1 := by
    rw [show s2 = State.tPop s1 sRB rB from rfl]; exact eval_pop main sRB rB s1
  have h2A : ¬ (s2.reg rA = gM) := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rA_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_pos rfl]
    simp only [hA, List.headD_cons]
    exact fun h => gM_ne_bit bA h.symm
  have h2B : s2.reg rB = gM := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  let t1 : State := State.tPush s2 sRB rB
  let s3 : State := State.tSet t1 rFlag gGt
  let s4 : State := State.tSet s3 rCont gStop
  have e3 : Eval main (.push sRB rB) s2 t1 1 := by
    rw [show t1 = State.tPush s2 sRB rB from rfl]; exact eval_push main sRB rB s2
  have e4 : Eval main (.set rFlag gGt) t1 s3 1 := by
    rw [show s3 = State.tSet t1 rFlag gGt from rfl]; exact eval_set main rFlag gGt t1
  have e5 : Eval main (.set rCont gStop) s3 s4 1 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl]; exact eval_set main rCont gStop s3
  have e45 : Eval main (.seq (.set rFlag gGt) (.set rCont gStop)) t1 s4 2 := Eval.seq e4 e5
  have e345 : Eval main (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop))) s2 s4 3 :=
    Eval.seq e3 e45
  have eitB : Eval main (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
      (.ite rA (Glyph.bit true)
        (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
          (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
        (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
          (.set rCont Glyph.eos)))) s2 s4 4 :=
    Eval.iteT h2B e345
  have ebig : Eval main (.ite rA gM
      (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
        (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
      (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
        (.ite rA (Glyph.bit true)
          (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
            (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
          (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
            (.set rCont Glyph.eos))))) s2 s4 5 :=
    Eval.iteF h2A eitB
  have ebody : Eval main scanBody s s4 7 := Eval.seq e1 (Eval.seq e2 ebig)
  have h4A : s4.stk sRA = tA.map Glyph.bit ++ gM :: RA0 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tSet t1 rFlag gGt from rfl, tSet_stk]
    rw [show t1 = State.tPush s2 sRB rB from rfl, tPush_stk, if_neg sRA_ne_sRB]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg sRA_ne_sRB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_pos rfl]
    simp [hA]
  have h4B : s4.stk sRB = gM :: RB0 := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tSet t1 rFlag gGt from rfl, tSet_stk]
    rw [show t1 = State.tPush s2 sRB rB from rfl, tPush_stk, if_pos rfl]
    rw [h2B]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h4cont : s4.reg rCont = gStop := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_reg, if_pos rfl]
  have h4flag : s4.reg rFlag = gGt := by
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_reg, if_neg rFlag_ne_rCont]
    rw [show s3 = State.tSet t1 rFlag gGt from rfl, tSet_reg, if_pos rfl]
  have h4other : ∀ j, j ≠ sRA → j ≠ sRB → s4.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s4 = State.tSet s3 rCont gStop from rfl, tSet_stk,
      show s3 = State.tSet t1 rFlag gGt from rfl, tSet_stk,
      show t1 = State.tPush s2 sRB rB from rfl, tPush_stk, if_neg hj2,
      show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg hj2,
      show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg hj1]
  exact ⟨s4, 7, ebody, by omega, h4A, h4B, h4cont, h4flag, h4other⟩

/-- One body step, both sides have a bit and they are equal: keep the flag, continue. -/
theorem scanBody_ee (main : Cmd) (b : Bool) (tA tB : List Bool) (RA0 RB0 : List Glyph)
    (s : State)
    (hA : s.stk sRA = Glyph.bit b :: tA.map Glyph.bit ++ gM :: RA0)
    (hB : s.stk sRB = Glyph.bit b :: tB.map Glyph.bit ++ gM :: RB0) :
    ∃ s' n, Eval main scanBody s s' n ∧ n ≤ 9 ∧
      s'.stk sRA = tA.map Glyph.bit ++ gM :: RA0 ∧ s'.stk sRB = tB.map Glyph.bit ++ gM :: RB0 ∧
      s'.reg rCont = Glyph.eos ∧ s'.reg rFlag = s.reg rFlag ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sRA rA
  have e1 : Eval main (.pop sRA rA) s s1 1 := by
    rw [show s1 = State.tPop s sRA rA from rfl]; exact eval_pop main sRA rA s
  let s2 : State := State.tPop s1 sRB rB
  have e2 : Eval main (.pop sRB rB) s1 s2 1 := by
    rw [show s2 = State.tPop s1 sRB rB from rfl]; exact eval_pop main sRB rB s1
  have h2A : s2.reg rA = Glyph.bit b := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rA_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_pos rfl]
    simp [hA]
  have h2B : s2.reg rB = Glyph.bit b := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h2Ag : ¬ (s2.reg rA = gM) := by rw [h2A]; exact fun h => gM_ne_bit b h.symm
  have h2Bg : ¬ (s2.reg rB = gM) := by rw [h2B]; exact fun h => gM_ne_bit b h.symm
  let s3 : State := State.tSet s2 rCont Glyph.eos
  have eC : Eval main (.set rCont Glyph.eos) s2 s3 1 := by
    rw [show s3 = State.tSet s2 rCont Glyph.eos from rfl]; exact eval_set main rCont Glyph.eos s2
  have ecases : Eval main (.ite rA (Glyph.bit true)
        (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
          (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
        (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
          (.set rCont Glyph.eos))) s2 s3 3 := by
    rcases b with _ | _
    · -- b = false
      have hA' : ¬ (s2.reg rA = Glyph.bit true) := by rw [h2A]; exact by decide
      have hB' : ¬ (s2.reg rB = Glyph.bit true) := by rw [h2B]; exact by decide
      refine Eval.iteF hA' (Eval.iteF hB' ?_)
      simpa using eC
    · -- b = true
      have hB' : s2.reg rB = Glyph.bit true := by rw [h2B]
      refine Eval.iteT (by rw [h2A]) (Eval.iteT hB' ?_)
      simpa using eC
  have ebig : Eval main (.ite rA gM
      (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
        (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
      (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
        (.ite rA (Glyph.bit true)
          (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
            (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
          (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
            (.set rCont Glyph.eos))))) s2 s3 5 :=
    Eval.iteF h2Ag (Eval.iteF h2Bg ecases)
  have ebody : Eval main scanBody s s3 7 := Eval.seq e1 (Eval.seq e2 ebig)
  have h3A : s3.stk sRA = tA.map Glyph.bit ++ gM :: RA0 := by
    rw [show s3 = State.tSet s2 rCont Glyph.eos from rfl, tSet_stk]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg sRA_ne_sRB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_pos rfl]
    simp [hA]
  have h3B : s3.stk sRB = tB.map Glyph.bit ++ gM :: RB0 := by
    rw [show s3 = State.tSet s2 rCont Glyph.eos from rfl, tSet_stk]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h3cont : s3.reg rCont = Glyph.eos := by
    rw [show s3 = State.tSet s2 rCont Glyph.eos from rfl, tSet_reg, if_pos rfl]
  have h3flag : s3.reg rFlag = s.reg rFlag := by
    rw [show s3 = State.tSet s2 rCont Glyph.eos from rfl, tSet_reg, if_neg rFlag_ne_rCont]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rFlag_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_neg rFlag_ne_rA]
  have h3other : ∀ j, j ≠ sRA → j ≠ sRB → s3.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s3 = State.tSet s2 rCont Glyph.eos from rfl, tSet_stk,
      show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg hj2,
      show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg hj1]
  exact ⟨s3, 7, ebody, by omega, h3A, h3B, h3cont, h3flag, h3other⟩

/-- One body step, both sides have a bit and they differ: overwrite the flag, continue. -/
theorem scanBody_ne (main : Cmd) (tA tB : List Bool) (RA0 RB0 : List Glyph) (s : State)
    (hA : s.stk sRA = Glyph.bit true :: tA.map Glyph.bit ++ gM :: RA0)
    (hB : s.stk sRB = Glyph.bit false :: tB.map Glyph.bit ++ gM :: RB0) :
    ∃ s' n, Eval main scanBody s s' n ∧ n ≤ 9 ∧
      s'.stk sRA = tA.map Glyph.bit ++ gM :: RA0 ∧ s'.stk sRB = tB.map Glyph.bit ++ gM :: RB0 ∧
      s'.reg rCont = Glyph.eos ∧ s'.reg rFlag = gGt ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sRA rA
  have e1 : Eval main (.pop sRA rA) s s1 1 := by
    rw [show s1 = State.tPop s sRA rA from rfl]; exact eval_pop main sRA rA s
  let s2 : State := State.tPop s1 sRB rB
  have e2 : Eval main (.pop sRB rB) s1 s2 1 := by
    rw [show s2 = State.tPop s1 sRB rB from rfl]; exact eval_pop main sRB rB s1
  have h2A : s2.reg rA = Glyph.bit true := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rA_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_pos rfl]
    simp [hA]
  have h2B : s2.reg rB = Glyph.bit false := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h2Ag : ¬ (s2.reg rA = gM) := by rw [h2A]; exact fun h => gM_ne_bit true h.symm
  have h2Bg : ¬ (s2.reg rB = gM) := by rw [h2B]; exact fun h => gM_ne_bit false h.symm
  have h2Bt : ¬ (s2.reg rB = Glyph.bit true) := by rw [h2B]; exact by decide
  let s3 : State := State.tSet s2 rFlag gGt
  let s4 : State := State.tSet s3 rCont Glyph.eos
  have e3 : Eval main (.set rFlag gGt) s2 s3 1 := by
    rw [show s3 = State.tSet s2 rFlag gGt from rfl]; exact eval_set main rFlag gGt s2
  have e4 : Eval main (.set rCont Glyph.eos) s3 s4 1 := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl]; exact eval_set main rCont Glyph.eos s3
  have e34 : Eval main (.seq (.set rFlag gGt) (.set rCont Glyph.eos)) s2 s4 2 := Eval.seq e3 e4
  have ecases : Eval main (.ite rA (Glyph.bit true)
        (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
          (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
        (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
          (.set rCont Glyph.eos))) s2 s4 4 :=
    Eval.iteT (by rw [h2A]) (Eval.iteF h2Bt e34)
  have ebig : Eval main (.ite rA gM
      (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
        (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
      (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
        (.ite rA (Glyph.bit true)
          (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
            (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
          (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
            (.set rCont Glyph.eos))))) s2 s4 6 :=
    Eval.iteF h2Ag (Eval.iteF h2Bg ecases)
  have ebody : Eval main scanBody s s4 8 := Eval.seq e1 (Eval.seq e2 ebig)
  have h4A : s4.stk sRA = tA.map Glyph.bit ++ gM :: RA0 := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_stk,
      show s3 = State.tSet s2 rFlag gGt from rfl, tSet_stk]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg sRA_ne_sRB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_pos rfl]
    simp [hA]
  have h4B : s4.stk sRB = tB.map Glyph.bit ++ gM :: RB0 := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_stk,
      show s3 = State.tSet s2 rFlag gGt from rfl, tSet_stk]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h4cont : s4.reg rCont = Glyph.eos := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_reg, if_pos rfl]
  have h4flag : s4.reg rFlag = gGt := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_reg, if_neg rFlag_ne_rCont]
    rw [show s3 = State.tSet s2 rFlag gGt from rfl, tSet_reg, if_pos rfl]
  have h4other : ∀ j, j ≠ sRA → j ≠ sRB → s4.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_stk,
      show s3 = State.tSet s2 rFlag gGt from rfl, tSet_stk,
      show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg hj2,
      show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg hj1]
  exact ⟨s4, 8, ebody, by omega, h4A, h4B, h4cont, h4flag, h4other⟩

/-- One body step, both sides have a bit, `false` then `true`: overwrite the flag, continue. -/
theorem scanBody_ne' (main : Cmd) (tA tB : List Bool) (RA0 RB0 : List Glyph) (s : State)
    (hA : s.stk sRA = Glyph.bit false :: tA.map Glyph.bit ++ gM :: RA0)
    (hB : s.stk sRB = Glyph.bit true :: tB.map Glyph.bit ++ gM :: RB0) :
    ∃ s' n, Eval main scanBody s s' n ∧ n ≤ 9 ∧
      s'.stk sRA = tA.map Glyph.bit ++ gM :: RA0 ∧ s'.stk sRB = tB.map Glyph.bit ++ gM :: RB0 ∧
      s'.reg rCont = Glyph.eos ∧ s'.reg rFlag = gLt ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sRA rA
  have e1 : Eval main (.pop sRA rA) s s1 1 := by
    rw [show s1 = State.tPop s sRA rA from rfl]; exact eval_pop main sRA rA s
  let s2 : State := State.tPop s1 sRB rB
  have e2 : Eval main (.pop sRB rB) s1 s2 1 := by
    rw [show s2 = State.tPop s1 sRB rB from rfl]; exact eval_pop main sRB rB s1
  have h2A : s2.reg rA = Glyph.bit false := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_neg rA_ne_rB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_reg, if_pos rfl]
    simp [hA]
  have h2B : s2.reg rB = Glyph.bit true := by
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_reg, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h2Ag : ¬ (s2.reg rA = gM) := by rw [h2A]; exact fun h => gM_ne_bit false h.symm
  have h2Bg : ¬ (s2.reg rB = gM) := by rw [h2B]; exact fun h => gM_ne_bit true h.symm
  have h2At : ¬ (s2.reg rA = Glyph.bit true) := by rw [h2A]; exact by decide
  let s3 : State := State.tSet s2 rFlag gLt
  let s4 : State := State.tSet s3 rCont Glyph.eos
  have e3 : Eval main (.set rFlag gLt) s2 s3 1 := by
    rw [show s3 = State.tSet s2 rFlag gLt from rfl]; exact eval_set main rFlag gLt s2
  have e4 : Eval main (.set rCont Glyph.eos) s3 s4 1 := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl]; exact eval_set main rCont Glyph.eos s3
  have e34 : Eval main (.seq (.set rFlag gLt) (.set rCont Glyph.eos)) s2 s4 2 := Eval.seq e3 e4
  have ecases : Eval main (.ite rA (Glyph.bit true)
        (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
          (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
        (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
          (.set rCont Glyph.eos))) s2 s4 4 :=
    Eval.iteF h2At (Eval.iteT (by rw [h2B]) e34)
  have ebig : Eval main (.ite rA gM
      (.ite rB gM (.seq (.push sRA rA) (.seq (.push sRB rB) (.set rCont gStop)))
        (.seq (.push sRA rA) (.seq (.set rFlag gLt) (.set rCont gStop))))
      (.ite rB gM (.seq (.push sRB rB) (.seq (.set rFlag gGt) (.set rCont gStop)))
        (.ite rA (Glyph.bit true)
          (.ite rB (Glyph.bit true) (.set rCont Glyph.eos)
            (.seq (.set rFlag gGt) (.set rCont Glyph.eos)))
          (.ite rB (Glyph.bit true) (.seq (.set rFlag gLt) (.set rCont Glyph.eos))
            (.set rCont Glyph.eos))))) s2 s4 6 :=
    Eval.iteF h2Ag (Eval.iteF h2Bg ecases)
  have ebody : Eval main scanBody s s4 8 := Eval.seq e1 (Eval.seq e2 ebig)
  have h4A : s4.stk sRA = tA.map Glyph.bit ++ gM :: RA0 := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_stk,
      show s3 = State.tSet s2 rFlag gLt from rfl, tSet_stk]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg sRA_ne_sRB]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_pos rfl]
    simp [hA]
  have h4B : s4.stk sRB = tB.map Glyph.bit ++ gM :: RB0 := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_stk,
      show s3 = State.tSet s2 rFlag gLt from rfl, tSet_stk]
    rw [show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_pos rfl]
    rw [show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg sRB_ne_sRA]
    simp [hB]
  have h4cont : s4.reg rCont = Glyph.eos := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_reg, if_pos rfl]
  have h4flag : s4.reg rFlag = gLt := by
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_reg, if_neg rFlag_ne_rCont]
    rw [show s3 = State.tSet s2 rFlag gLt from rfl, tSet_reg, if_pos rfl]
  have h4other : ∀ j, j ≠ sRA → j ≠ sRB → s4.stk j = s.stk j := by
    intro j hj1 hj2
    rw [show s4 = State.tSet s3 rCont Glyph.eos from rfl, tSet_stk,
      show s3 = State.tSet s2 rFlag gLt from rfl, tSet_stk,
      show s2 = State.tPop s1 sRB rB from rfl, tPop_stk, if_neg hj2,
      show s1 = State.tPop s sRA rA from rfl, tPop_stk, if_neg hj1]
  exact ⟨s4, 8, ebody, by omega, h4A, h4B, h4cont, h4flag, h4other⟩


/-- The comparison scan: from the state where `sRA` holds `sA0` (LSB first, with marker) and `sRB`
holds `sB0`, the loop stops with `reg rFlag` recording the comparison of `ofBits sA0` and
`ofBits sB0`. -/
theorem scanAux (main : Cmd) (sA0 sB0 : List Bool) (RA0 RB0 : List Glyph)
    (hA0 : IsBits sA0) (hB0 : IsBits sB0) :
    ∀ (gsA gsB pA pB : List Bool) (s : State),
      pA.length = pB.length → sA0 = pA ++ gsA → sB0 = pB ++ gsB →
      s.stk sRA = gsA.map Glyph.bit ++ gM :: RA0 →
      s.stk sRB = gsB.map Glyph.bit ++ gM :: RB0 →
      s.reg rCont = Glyph.eos → NatFlag (s.reg rFlag) (ofBits pA) (ofBits pB) →
      ∃ s' n, Eval main scanLoop s s' n ∧ s'.reg rCont ≠ Glyph.eos ∧
        NatFlag (s'.reg rFlag) (ofBits sA0) (ofBits sB0) ∧
        (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) ∧
        (∃ gA gB, (∀ g ∈ gA, g ≠ gM) ∧ (∀ g ∈ gB, g ≠ gM) ∧
          gA.length ≤ sA0.length ∧ gB.length ≤ sB0.length ∧
          s'.stk sRA = gA ++ gM :: RA0 ∧ s'.stk sRB = gB ++ gM :: RB0) ∧
        n ≤ 12 * (gsA.length + gsB.length + 1) := by
  intro gsA
  induction gsA with
  | nil =>
    intro gsB pA pB s hlen hA' hB' hRA hRB hC hF
    have hsA : sA0 = pA := by simpa using hA'
    cases gsB with
    | nil =>
      have hsB : sB0 = pB := by simpa using hB'
      obtain ⟨s', n, hev, hn, hstkA, hstkB, hcont, hflag, hother⟩ :=
        scanBody_mm main RA0 RB0 s (by simpa using hRA) (by simpa using hRB)
      have hloopF : Eval main scanLoop s' s' 1 := Eval.loopF (by rw [hcont]; exact gStop_ne_eos)
      have hmain : Eval main scanLoop s s' (n + 1 + 1) := Eval.loopT hC hev hloopF
      refine ⟨s', n + 1 + 1, hmain, by rw [hcont]; exact gStop_ne_eos, ?_, hother, ?_, ?_⟩
      · rw [hflag, hsA, hsB]; exact hF
      · exact ⟨[], [], by simp, by simp, by simp, by simp, by simpa using hstkA,
          by simpa using hstkB⟩
      · omega
    | cons bB tB =>
      obtain ⟨s', n, hev, hn, hstkA, hstkB, hcont, hflag, hother⟩ :=
        scanBody_mb main bB tB RA0 RB0 s (by simpa using hRA) (by simpa using hRB)
      have hloopF : Eval main scanLoop s' s' 1 := Eval.loopF (by rw [hcont]; exact gStop_ne_eos)
      have hmain : Eval main scanLoop s s' (n + 1 + 1) := Eval.loopT hC hev hloopF
      refine ⟨s', n + 1 + 1, hmain, by rw [hcont]; exact gStop_ne_eos, ?_, hother, ?_, ?_⟩
      · rw [hflag]
        refine Or.inl ⟨rfl, ?_⟩
        apply ofBits_lt_of_length_lt hA0 hB0
        rw [hsA, hB']
        simp only [List.length_append, List.length_cons, List.length_map]
        omega
      · exact ⟨[], tB.map Glyph.bit, by simp,
          by intro g hg; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg; exact fun h => gM_ne_bit b h.symm,
          by simp,
          by simp only [List.length_map]; rw [hB']
             <;> simp only [List.length_append, List.length_cons]
             <;> omega,
          by simpa using hstkA, by simpa using hstkB⟩
      · omega
  | cons bA tA ih =>
    intro gsB pA pB s hlen hA' hB' hRA hRB hC hF
    have hsA : sA0 = (pA ++ [bA]) ++ tA := by rw [hA']; simp [List.append_assoc]
    cases gsB with
    | nil =>
      have hsB : sB0 = pB := by simpa using hB'
      have hRB' : s.stk sRB = gM :: RB0 := by simpa using hRB
      obtain ⟨s', n, hev, hn, hstkA, hstkB, hcont, hflag, hother⟩ :=
        scanBody_bm main bA tA RA0 RB0 s (by simpa using hRA) hRB'
      have hloopF : Eval main scanLoop s' s' 1 := Eval.loopF (by rw [hcont]; exact gStop_ne_eos)
      have hmain : Eval main scanLoop s s' (n + 1 + 1) := Eval.loopT hC hev hloopF
      refine ⟨s', n + 1 + 1, hmain, by rw [hcont]; exact gStop_ne_eos, ?_, hother, ?_, ?_⟩
      · rw [hflag]
        refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        apply ofBits_lt_of_length_lt hB0 hA0
        rw [hsB, hsA]
        simp only [List.length_append, List.length_cons, List.length_map]
        omega
      · exact ⟨tA.map Glyph.bit, [],
          by intro g hg; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg; exact fun h => gM_ne_bit b h.symm,
          by simp,
          by simp only [List.length_map]; rw [hA']
             <;> simp only [List.length_append, List.length_cons]
             <;> omega,
          by simp,
          by simpa using hstkA, by simpa using hstkB⟩
      · omega
    | cons bB tB =>
      have hsB : sB0 = (pB ++ [bB]) ++ tB := by rw [hB']; simp [List.append_assoc]
      have hRA' : s.stk sRA = Glyph.bit bA :: tA.map Glyph.bit ++ gM :: RA0 := by
        simpa using hRA
      have hRB' : s.stk sRB = Glyph.bit bB :: tB.map Glyph.bit ++ gM :: RB0 := by
        simpa using hRB
      rcases bA with _ | _ <;> rcases bB with _ | _
      · -- false / false : equal, continue
        obtain ⟨s1, n1, hev, hn1, h1A, h1B, hcont, hflag, hother⟩ :=
          scanBody_ee main false tA tB RA0 RB0 s hRA' hRB'
        have hlen' : (pA ++ [false]).length = (pB ++ [false]).length := by simp [hlen]
        have hF' : NatFlag (s1.reg rFlag) (ofBits (pA ++ [false])) (ofBits (pB ++ [false])) := by
          rw [hflag, ofBits_append, ofBits_append, hlen]
          simpa [ofBits_cons, ofBits_nil] using
            natFlag_add (s.reg rFlag) (ofBits pA) (ofBits pB) 0 hF
        obtain ⟨s2, n2, hev2, hcont2, hnf2, hother2, hshape2, hn2⟩ :=
          ih tB (pA ++ [false]) (pB ++ [false]) s1 hlen' hsA hsB h1A h1B hcont hF'
        refine ⟨s2, n1 + n2 + 1, Eval.loopT hC hev hev2, hcont2, hnf2, ?_, hshape2, ?_⟩
        · intro j hj1 hj2; rw [hother2 j hj1 hj2, hother j hj1 hj2]
        · have : n1 ≤ 9 := hn1
          simp only [List.length_cons] at hn2 ⊢
          omega
      · -- false / true : flag gLt, continue
        obtain ⟨s1, n1, hev, hn1, h1A, h1B, hcont, hflag, hother⟩ :=
          scanBody_ne' main tA tB RA0 RB0 s hRA' hRB'
        have hlen' : (pA ++ [false]).length = (pB ++ [true]).length := by simp [hlen]
        have hF' : NatFlag (s1.reg rFlag) (ofBits (pA ++ [false])) (ofBits (pB ++ [true])) := by
          rw [hflag]
          refine Or.inl ⟨rfl, ?_⟩
          rw [ofBits_append, ofBits_append, hlen]
          simp only [ofBits_cons, ofBits_nil, List.length_nil, Bool.toNat_false,
            Bool.toNat_true, mul_zero, mul_one, add_zero, Nat.zero_mul, zero_add]
          have h1 : ofBits pA < 2 ^ pB.length := by
            rw [← hlen]; exact ofBits_lt_two_pow pA
          omega
        obtain ⟨s2, n2, hev2, hcont2, hnf2, hother2, hshape2, hn2⟩ :=
          ih tB (pA ++ [false]) (pB ++ [true]) s1 hlen' hsA hsB h1A h1B hcont hF'
        refine ⟨s2, n1 + n2 + 1, Eval.loopT hC hev hev2, hcont2, hnf2, ?_, hshape2, ?_⟩
        · intro j hj1 hj2; rw [hother2 j hj1 hj2, hother j hj1 hj2]
        · have : n1 ≤ 9 := hn1
          simp only [List.length_cons] at hn2 ⊢
          omega
      · -- true / false : flag gGt, continue
        obtain ⟨s1, n1, hev, hn1, h1A, h1B, hcont, hflag, hother⟩ :=
          scanBody_ne main tA tB RA0 RB0 s hRA' hRB'
        have hlen' : (pA ++ [true]).length = (pB ++ [false]).length := by simp [hlen]
        have hF' : NatFlag (s1.reg rFlag) (ofBits (pA ++ [true])) (ofBits (pB ++ [false])) := by
          rw [hflag]
          refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          rw [ofBits_append, ofBits_append, hlen]
          simp only [ofBits_cons, ofBits_nil, List.length_nil, Bool.toNat_false,
            Bool.toNat_true, mul_zero, mul_one, add_zero, Nat.zero_mul, zero_add]
          have h1 := ofBits_lt_two_pow pB
          omega
        obtain ⟨s2, n2, hev2, hcont2, hnf2, hother2, hshape2, hn2⟩ :=
          ih tB (pA ++ [true]) (pB ++ [false]) s1 hlen' hsA hsB h1A h1B hcont hF'
        refine ⟨s2, n1 + n2 + 1, Eval.loopT hC hev hev2, hcont2, hnf2, ?_, hshape2, ?_⟩
        · intro j hj1 hj2; rw [hother2 j hj1 hj2, hother j hj1 hj2]
        · have : n1 ≤ 9 := hn1
          simp only [List.length_cons] at hn2 ⊢
          omega
      · -- true / true : equal, continue
        obtain ⟨s1, n1, hev, hn1, h1A, h1B, hcont, hflag, hother⟩ :=
          scanBody_ee main true tA tB RA0 RB0 s hRA' hRB'
        have hlen' : (pA ++ [true]).length = (pB ++ [true]).length := by simp [hlen]
        have hF' : NatFlag (s1.reg rFlag) (ofBits (pA ++ [true])) (ofBits (pB ++ [true])) := by
          rw [hflag, ofBits_append, ofBits_append, hlen]
          simpa [ofBits_cons, ofBits_nil] using
            natFlag_add (s.reg rFlag) (ofBits pA) (ofBits pB) (2 ^ pB.length) hF
        obtain ⟨s2, n2, hev2, hcont2, hnf2, hother2, hshape2, hn2⟩ :=
          ih tB (pA ++ [true]) (pB ++ [true]) s1 hlen' hsA hsB h1A h1B hcont hF'
        refine ⟨s2, n1 + n2 + 1, Eval.loopT hC hev hev2, hcont2, hnf2, ?_, hshape2, ?_⟩
        · intro j hj1 hj2; rw [hother2 j hj1 hj2, hother j hj1 hj2]
        · have : n1 ≤ 9 := hn1
          simp only [List.length_cons] at hn2 ⊢
          omega

/-- Top-level statement of the comparison scan. -/
theorem scanLoop_eval (main : Cmd) (sA0 sB0 : List Bool) (RA0 RB0 : List Glyph) (s : State)
    (hA0 : IsBits sA0) (hB0 : IsBits sB0)
    (hA : s.stk sRA = sA0.map Glyph.bit ++ gM :: RA0)
    (hB : s.stk sRB = sB0.map Glyph.bit ++ gM :: RB0)
    (hC : s.reg rCont = Glyph.eos) (hF : s.reg rFlag = gEq) :
    ∃ s' n, Eval main scanLoop s s' n ∧ s'.reg rCont ≠ Glyph.eos ∧
      NatFlag (s'.reg rFlag) (ofBits sA0) (ofBits sB0) ∧
      (∀ j, j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) ∧
      (∃ gA gB, (∀ g ∈ gA, g ≠ gM) ∧ (∀ g ∈ gB, g ≠ gM) ∧
        gA.length ≤ sA0.length ∧ gB.length ≤ sB0.length ∧
        s'.stk sRA = gA ++ gM :: RA0 ∧ s'.stk sRB = gB ++ gM :: RB0) ∧
      n ≤ 12 * (sA0.length + sB0.length + 1) :=
  scanAux main sA0 sB0 RA0 RB0 hA0 hB0 sA0 sB0 [] [] s (by simp) (by simp) (by simp) hA hB hC
    (by rw [hF]; exact Or.inr (Or.inl ⟨rfl, rfl⟩))


/-! ## A two-destination transfer loop (non-destructive copy) -/

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

/-- The sign glyph of an integer. -/
def sg (z : ℤ) : Glyph := if z < 0 then Glyph.neg else Glyph.pos

theorem enc_int' (z : ℤ) :
    (Val.int z).enc = sg z :: (Computability.encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend] := rfl

theorem sg_neg {z : ℤ} (h : z < 0) : sg z = Glyph.neg := if_pos h

theorem neg_eq_neg_natAbs {a : ℤ} (h : a < 0) : a = -(a.natAbs : ℤ) := by
  have h1 : ((-a).natAbs : ℤ) = -a := Int.natAbs_of_nonneg (by omega)
  rw [Int.natAbs_neg] at h1
  omega
theorem sg_pos {z : ℤ} (h : ¬ z < 0) : sg z = Glyph.pos := if_neg h

/-- Combining the two sign glyphs with the magnitude comparison. -/
def cFlag (f sa sb : Glyph) : Glyph :=
  if sa = Glyph.neg then
    (if sb = Glyph.neg then (if f = gLt then gGt else if f = gGt then gLt else gEq) else gLt)
  else (if sb = Glyph.neg then gGt else f)

def combineProg : Cmd :=
  .ite rSA Glyph.neg
    (.ite rSB Glyph.neg
      (.ite rFlag gLt (.set rRes gGt)
        (.ite rFlag gGt (.set rRes gLt) (.set rRes gEq)))
      (.set rRes gLt))
    (.ite rSB Glyph.neg (.set rRes gGt) (.mov rRes rFlag))

theorem combine_flag (a b : ℤ) (f : Glyph) (hf : NatFlag f a.natAbs b.natAbs) :
    IntFlag (cFlag f (sg a) (sg b)) a b := by
  unfold cFlag
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · -- both negative
    rw [sg_neg ha, sg_neg hb]
    rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      simp only [if_pos rfl, if_neg (by decide : ¬ (gLt = gGt)), if_neg (by decide : ¬ (gLt = gEq))]
      refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      have h2' : (a.natAbs : ℤ) < (b.natAbs : ℤ) := by exact_mod_cast h2
      have ha' := neg_eq_neg_natAbs ha
      have hb' := neg_eq_neg_natAbs hb
      omega
    · subst h1
      simp only [if_neg (by decide : ¬ (gEq = gLt)), if_neg (by decide : ¬ (gEq = gGt)),
        if_pos rfl]
      refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      have h2' : (a.natAbs : ℤ) = (b.natAbs : ℤ) := by exact_mod_cast h2
      have ha' := neg_eq_neg_natAbs ha
      have hb' := neg_eq_neg_natAbs hb
      omega
    · subst h1
      simp only [if_neg (by decide : ¬ (gGt = gLt)), if_pos rfl, if_neg (by decide : ¬ (gGt = gEq))]
      refine Or.inl ⟨rfl, ?_⟩
      have h2' : (b.natAbs : ℤ) < (a.natAbs : ℤ) := by exact_mod_cast h2
      have ha' := neg_eq_neg_natAbs ha
      have hb' := neg_eq_neg_natAbs hb
      omega
  · -- a < 0 ≤ b
    rw [sg_neg ha, sg_pos hb]
    simp only [if_pos rfl, if_neg (by decide : ¬ (Glyph.pos = Glyph.neg))]
    refine Or.inl ⟨rfl, by omega⟩
  · -- a ≥ 0 > b
    rw [sg_pos ha, sg_neg hb]
    simp only [if_neg (by decide : ¬ (Glyph.pos = Glyph.neg)), if_pos rfl]
    refine Or.inr (Or.inr ⟨rfl, by omega⟩)
  · -- both nonneg
    rw [sg_pos ha, sg_pos hb]
    simp only [if_neg (by decide : ¬ (Glyph.pos = Glyph.neg))]
    have ha' : a = (a.natAbs : ℤ) := by
      have := Int.natAbs_of_nonneg (le_of_not_gt ha); omega
    have hb' : b = (b.natAbs : ℤ) := by
      have := Int.natAbs_of_nonneg (le_of_not_gt hb); omega
    rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, ?_⟩
      have h2' : (a.natAbs : ℤ) < (b.natAbs : ℤ) := by exact_mod_cast h2
      omega
    · refine Or.inr (Or.inl ⟨h1, ?_⟩)
      have h2' : (a.natAbs : ℤ) = (b.natAbs : ℤ) := by exact_mod_cast h2
      omega
    · refine Or.inr (Or.inr ⟨h1, ?_⟩)
      have h2' : (b.natAbs : ℤ) < (a.natAbs : ℤ) := by exact_mod_cast h2
      omega

theorem combine_eval (main : Cmd) (s : State) (f sa sb : Glyph) (hsa : s.reg rSA = sa)
    (hsb : s.reg rSB = sb) (hsf : s.reg rFlag = f) :
    ∃ n ≤ 6, Eval main combineProg s (s.updReg rRes (cFlag f sa sb)) n := by
  have key : ∀ g : Glyph, cFlag f sa sb = g → (∃ n ≤ 6, Eval main combineProg s (s.updReg rRes g) n) →
      ∃ n ≤ 6, Eval main combineProg s (s.updReg rRes (cFlag f sa sb)) n := by
    intro g hg h
    obtain ⟨n, hn, hev⟩ := h
    exact ⟨n, hn, by rw [hg]; exact hev⟩
  by_cases hneg : sa = Glyph.neg
  · have hsa' : s.reg rSA = Glyph.neg := by rw [hsa, hneg]
    by_cases hnegb : sb = Glyph.neg
    · have hsb' : s.reg rSB = Glyph.neg := by rw [hsb, hnegb]
      by_cases hfl : f = gLt
      · have hf' : s.reg rFlag = gLt := by rw [hsf, hfl]
        exact key gGt (by simp [cFlag, hneg, hnegb, hfl])
          ⟨4, by omega, Eval.iteT hsa' (Eval.iteT hsb' (Eval.iteT hf' (eval_set main rRes gGt s)))⟩
      · by_cases hfg : f = gGt
        · have hf' : s.reg rFlag = gGt := by rw [hsf, hfg]
          exact key gLt (by simp [cFlag, hneg, hnegb, hfl, hfg])
            ⟨5, by omega, Eval.iteT hsa' (Eval.iteT hsb'
              (Eval.iteF (by simp [hsf, hfl]) (Eval.iteT hf' (eval_set main rRes gLt s))))⟩
        · exact key gEq (by simp [cFlag, hneg, hnegb, hfl, hfg])
            ⟨5, by omega, Eval.iteT hsa' (Eval.iteT hsb'
              (Eval.iteF (by simp [hsf, hfl])
                (Eval.iteF (by simp [hsf, hfg]) (eval_set main rRes gEq s))))⟩
    · have hsb' : ¬ (s.reg rSB = Glyph.neg) := by rw [hsb]; exact hnegb
      exact key gLt (by simp [cFlag, hneg, hnegb])
        ⟨3, by omega, Eval.iteT hsa' (Eval.iteF hsb' (eval_set main rRes gLt s))⟩
  · have hsa' : ¬ (s.reg rSA = Glyph.neg) := by rw [hsa]; exact hneg
    by_cases hnegb : sb = Glyph.neg
    · have hsb' : s.reg rSB = Glyph.neg := by rw [hsb, hnegb]
      exact key gGt (by simp [cFlag, hneg, hnegb])
        ⟨3, by omega, Eval.iteF hsa' (Eval.iteT hsb' (eval_set main rRes gGt s))⟩
    · have hsb' : ¬ (s.reg rSB = Glyph.neg) := by rw [hsb]; exact hnegb
      have hmov : Eval main (.mov rRes rFlag) s (s.updReg rRes f) 1 := by
        have h := eval_mov main rRes rFlag s
        rwa [show State.tMov s rRes rFlag = s.updReg rRes f from by
          simp only [State.tMov]; rw [hsf]] at h
      exact key f (by simp [cFlag, hneg, hnegb])
        ⟨3, by omega, Eval.iteF hsa' (Eval.iteF hsb' hmov)⟩

/-- Auxiliary: `cFlag` has the value required by `combine_eval`. -/
theorem cFlag_eq (s : State) (f sa sb : Glyph) (hsa : s.reg rSA = sa) (hsb : s.reg rSB = sb)
    (hsf : s.reg rFlag = f) :
    cFlag f sa sb = cFlag (s.reg rFlag) (s.reg rSA) (s.reg rSB) := by
  rw [hsa, hsb, hsf]

/-- The word list for the leading part of every binary comparison. -/
def coreProg : Cmd :=
  .seq (storeMag 0 sPA sSA rA rB)
   (.seq (storeMag 0 sPB sSB rA rB)
    (.seq (copyMarked2 sPA sCA sTA rA rB)
     (.seq (copyMarked2 sPB sCB sTB rA rB)
      (.seq (revMarked sCA sRA rA rB)
       (.seq (revMarked sCB sRB rA rB)
        (.seq (.set rFlag gEq)
         (.seq (.set rCont Glyph.eos)
          (.seq scanLoop
           (.seq (.pop sSA rSA) (.seq (.pop sSB rSB) combineProg))))))))))

theorem hPA_ne_hSA : sPA ≠ sSA := by decide
theorem hSA_ne_hPA : sSA ≠ sPA := by decide
theorem hPA_ne_hPB : sPA ≠ sPB := by decide
theorem hSA_ne_hSB : sSA ≠ sSB := by decide
theorem hSB_ne_hSA : sSB ≠ sSA := by decide
theorem hPB_ne_hSB : sPB ≠ sSB := by decide

theorem gM2_ne_bit (b : Bool) : gM2 ≠ Glyph.bit b := by intro h; cases h

theorem map_bit_ne_gM (l : List Bool) : ∀ x ∈ l.map Glyph.bit, x ≠ gM := by
  intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact fun h => gM_ne_bit b h.symm
theorem map_bit_ne_gM2 (l : List Bool) : ∀ x ∈ l.map Glyph.bit, x ≠ gM2 := by
  intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact fun h => gM2_ne_bit b h.symm

theorem IsBits_encodeNat (n : ℕ) : IsBits (Computability.encodeNat n) := by
  rw [encodeNat_eq_bits]; exact isBits_bits n

theorem ofBits_encodeNat (n : ℕ) : ofBits (Computability.encodeNat n) = n := by
  rw [encodeNat_eq_bits]; exact ofBits_bits n

theorem storeMag_frame (main : Cmd) (dst sgn : Stk) (a : ℤ) (rest : List Val) (R : List Glyph)
    (s : State) (h1 : dst ≠ 0) (h2 : sgn ≠ 0) (h3 : sgn ≠ dst)
    (h0 : s.stk 0 = (Val.int a).enc ++ encs rest ++ R) :
    ∃ s' n, Eval main (storeMag 0 dst sgn rA rB) s s' n ∧ n ≤ 5 * isz a + 14 ∧
      s'.stk 0 = encs rest ++ R ∧
      s'.stk dst = (Computability.encodeNat a.natAbs).reverse.map Glyph.bit ++ gM :: s.stk dst ∧
      s'.stk sgn = sg a :: s.stk sgn ∧
      (∀ j, j ≠ 0 → j ≠ dst → j ≠ sgn → s'.stk j = s.stk j) := by
  have h0a : s.stk 0 = sg a :: (Computability.encodeNat a.natAbs).map Glyph.bit ++ Glyph.iend ::
      (encs rest ++ R) := by
    rw [h0, enc_int']
    simp [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨s', n, hev, hn, h0', hPA, hSA, hoth⟩ :=
    storeMag_eval main 0 dst sgn rA rB h1 h2 h3
      (sg a) (Computability.encodeNat a.natAbs) (encs rest ++ R) s h0a
  refine ⟨s', n, hev, ?_, h0', hPA, hSA, hoth⟩
  have h1l : (Computability.encodeNat a.natAbs).length ≤ isz a := by
    rw [encodeNat_length, isz_eq]; omega
  have h2l := hn
  omega

/-- The tail of the `lt`/`eq` words: drain the four scratch stacks and emit `int 1` when
`reg rRes = gLt`, `int 0` otherwise. -/
def cmpTail (g : Glyph) : Cmd :=
  .seq (dropMarked sRA rA rB)
   (.seq (dropMarked sRB rA rB)
    (.seq (dropMarked sPA rA rB)
     (.seq (dropMarked sPB rA rB)
      (.ite rRes g (pushGlyphs (Val.int (1:ℤ)).enc.reverse 0 rA)
                   (pushGlyphs (Val.int (0:ℤ)).enc.reverse 0 rA)))))

/-- The tail of the `max` word: drain `sRA`, `sRB` and emit the larger of the two stored values
(according to `reg rRes`). -/
def maxTail : Cmd :=
  .seq (dropMarked sRA rA rB)
   (.seq (dropMarked sRB rA rB)
    (.ite rRes gLt
      (.seq (loadMarked sPB 0 rSB rA rB) (dropMarked sPA rA rB))
      (.seq (loadMarked sPA 0 rSA rA rB) (dropMarked sPB rA rB))))

/-- The negation word: pop the sign glyph; `neg` becomes `pos`, and `pos` becomes `neg` unless the
value is `0` (in which case the next glyph is `iend`). -/
def negProg : Cmd :=
  .seq (.pop 0 rA)
   (.ite rA Glyph.neg (.seq (.set rA Glyph.pos) (.push 0 rA))
      (.seq (.peek 0 rB)
        (.ite rB Glyph.iend (.seq (.set rA Glyph.pos) (.push 0 rA))
                            (.seq (.set rA Glyph.neg) (.push 0 rA)))))

/-- The `lt`/`eq` tail.  NOTE (status): the frame must exclude the four drained stacks, whose final
content is the `below` part, and the cost is `4*(|g1|+|g2|+|g3|+|g4|) + 40`. -/
theorem cmpTailEval (main : Cmd) (g : Glyph) (rest : List Val) (R : List Glyph)
    (g1 g2 g3 g4 b1 b2 b3 b4 : List Glyph) (s : State)
    (h0 : s.stk 0 = encs rest ++ R)
    (h1 : s.stk sRA = g1 ++ gM :: b1) (hg1 : ∀ x ∈ g1, x ≠ gM)
    (h2 : s.stk sRB = g2 ++ gM :: b2) (hg2 : ∀ x ∈ g2, x ≠ gM)
    (h3 : s.stk sPA = g3 ++ gM :: b3) (hg3 : ∀ x ∈ g3, x ≠ gM)
    (h4 : s.stk sPB = g4 ++ gM :: b4) (hg4 : ∀ x ∈ g4, x ≠ gM) :
    ∃ s' n, Eval main (cmpTail g) s s' n ∧
      n ≤ 5 * (g1.length + g2.length + g3.length + g4.length) + 50 ∧
      s'.stk 0 = (if s.reg rRes = g then (Val.int (1 : ℤ)).enc else (Val.int (0 : ℤ)).enc)
        ++ encs rest ++ R ∧
      s'.stk sRA = b1 ∧ s'.stk sRB = b2 ∧ s'.stk sPA = b3 ∧ s'.stk sPB = b4 ∧
      (∀ k, k ≠ 0 → k ≠ sRA → k ≠ sRB → k ≠ sPA → k ≠ sPB → s'.stk k = s.stk k) := by
  obtain ⟨s1, n1, hev1, hn1, h1RA, h1oth, h1reg⟩ :=
    dropMarked_eval main sRA rA rB g1 b1 hg1 s h1
  have h1RB : s1.stk sRB = g2 ++ gM :: b2 := by rw [h1oth sRB (by decide)]; exact h2
  obtain ⟨s2, n2, hev2, hn2, h2RB, h2oth, h2reg⟩ :=
    dropMarked_eval main sRB rA rB g2 b2 hg2 s1 h1RB
  have h2PA : s2.stk sPA = g3 ++ gM :: b3 := by
    rw [h2oth sPA (by decide), h1oth sPA (by decide)]; exact h3
  obtain ⟨s3, n3, hev3, hn3, h3PA, h3oth, h3reg⟩ :=
    dropMarked_eval main sPA rA rB g3 b3 hg3 s2 h2PA
  have h3PB : s3.stk sPB = g4 ++ gM :: b4 := by
    rw [h3oth sPB (by decide), h2oth sPB (by decide), h1oth sPB (by decide)]; exact h4
  obtain ⟨s4, n4, hev4, hn4, h4PB, h4oth, h4reg⟩ :=
    dropMarked_eval main sPB rA rB g4 b4 hg4 s3 h3PB
  have h4res : s4.reg rRes = s.reg rRes := by
    rw [h4reg rRes (by decide) (by decide), h3reg rRes (by decide) (by decide),
      h2reg rRes (by decide) (by decide), h1reg rRes (by decide) (by decide)]
  have h40 : s4.stk 0 = encs rest ++ R := by
    rw [h4oth 0 (by decide), h3oth 0 (by decide), h2oth 0 (by decide), h1oth 0 (by decide)]
    exact h0
  have hc1 : pushGlyphsCost (Val.int (1 : ℤ)).enc.reverse = 7 := by
    rw [pushGlyphsCost_eq, List.length_reverse]
    have : (Val.int (1 : ℤ)).enc.length = 3 := by decide
    omega
  have hc0 : pushGlyphsCost (Val.int (0 : ℤ)).enc.reverse = 5 := by
    rw [pushGlyphsCost_eq, List.length_reverse]
    have : (Val.int (0 : ℤ)).enc.length = 2 := by decide
    omega
  by_cases hres : s.reg rRes = g
  · -- the `ite` takes the `true` branch
    have hpush := eval_pushGlyphs main (Val.int (1 : ℤ)).enc.reverse 0 rA s4
    have hite : Eval main (.ite rRes g (pushGlyphs (Val.int (1 : ℤ)).enc.reverse 0 rA)
        (pushGlyphs (Val.int (0 : ℤ)).enc.reverse 0 rA))
        s4 (pushGlyphsState (Val.int (1 : ℤ)).enc.reverse 0 rA s4)
        (pushGlyphsCost (Val.int (1 : ℤ)).enc.reverse + 1) :=
      Eval.iteT (by rw [h4res]; exact hres) hpush
    have hev : Eval main (cmpTail g) s (pushGlyphsState (Val.int (1 : ℤ)).enc.reverse 0 rA s4)
        (n1 + (n2 + (n3 + (n4 + (pushGlyphsCost (Val.int (1 : ℤ)).enc.reverse + 1))))) :=
      Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 hite)))
    refine ⟨_, _, hev, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1' := hn1; have h2' := hn2; have h3' := hn3; have h4' := hn4
      omega
    · rw [pushGlyphsState_stk, if_pos rfl, List.reverse_reverse, h40, if_pos hres,
        List.append_assoc]
    · rw [pushGlyphsState_stk_ne (Val.int (1 : ℤ)).enc.reverse 0 rA s4 (by decide : sRA ≠ 0),
        h4oth sRA (by decide), h3oth sRA (by decide), h2oth sRA (by decide), h1RA]
    · rw [pushGlyphsState_stk, if_neg (by decide : sRB ≠ 0),
        h4oth sRB (by decide), h3oth sRB (by decide), h2RB]
    · rw [pushGlyphsState_stk, if_neg (by decide : sPA ≠ 0), h4oth sPA (by decide), h3PA]
    · rw [pushGlyphsState_stk, if_neg (by decide : sPB ≠ 0), h4PB]
    · intro k hk0 hkRA hkRB hkPA hkPB
      rw [pushGlyphsState_stk, if_neg hk0, h4oth k hkPB, h3oth k hkPA, h2oth k hkRB,
        h1oth k hkRA]
  · -- the `ite` takes the `false` branch
    have hpush := eval_pushGlyphs main (Val.int (0 : ℤ)).enc.reverse 0 rA s4
    have hite : Eval main (.ite rRes g (pushGlyphs (Val.int (1 : ℤ)).enc.reverse 0 rA)
        (pushGlyphs (Val.int (0 : ℤ)).enc.reverse 0 rA))
        s4 (pushGlyphsState (Val.int (0 : ℤ)).enc.reverse 0 rA s4)
        (pushGlyphsCost (Val.int (0 : ℤ)).enc.reverse + 1) :=
      Eval.iteF (by rw [h4res]; exact hres) hpush
    have hev : Eval main (cmpTail g) s (pushGlyphsState (Val.int (0 : ℤ)).enc.reverse 0 rA s4)
        (n1 + (n2 + (n3 + (n4 + (pushGlyphsCost (Val.int (0 : ℤ)).enc.reverse + 1))))) :=
      Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 hite)))
    refine ⟨_, _, hev, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1' := hn1; have h2' := hn2; have h3' := hn3; have h4' := hn4
      omega
    · rw [pushGlyphsState_stk, if_pos rfl, List.reverse_reverse, h40, if_neg hres,
        List.append_assoc]
    · rw [pushGlyphsState_stk_ne (Val.int (0 : ℤ)).enc.reverse 0 rA s4 (by decide : sRA ≠ 0),
        h4oth sRA (by decide), h3oth sRA (by decide), h2oth sRA (by decide), h1RA]
    · rw [pushGlyphsState_stk, if_neg (by decide : sRB ≠ 0),
        h4oth sRB (by decide), h3oth sRB (by decide), h2RB]
    · rw [pushGlyphsState_stk, if_neg (by decide : sPA ≠ 0), h4oth sPA (by decide), h3PA]
    · rw [pushGlyphsState_stk, if_neg (by decide : sPB ≠ 0), h4PB]
    · intro k hk0 hkRA hkRB hkPA hkPB
      rw [pushGlyphsState_stk, if_neg hk0, h4oth k hkPB, h3oth k hkPA, h2oth k hkRB,
        h1oth k hkRA]

/-- `IntFlag` records `<` faithfully. -/
theorem IntFlag.lt_iff {f : Glyph} {a b : ℤ} (h : IntFlag f a b) : (f = gLt) ↔ a < b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]; exact ⟨fun _ => h2, fun _ => rfl⟩
  · rw [h1]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · rw [h1]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩

/-- `IntFlag` records `=` faithfully. -/
theorem IntFlag.eq_iff {f : Glyph} {a b : ℤ} (h : IntFlag f a b) : (f = gEq) ↔ a = b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · rw [h1]; exact ⟨fun _ => h2, fun _ => rfl⟩
  · rw [h1]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩

theorem maxTailEval (main : Cmd) (a b : ℤ) (rest : List Val) (R : List Glyph)
    (g1 g2 b1 b2 PA0 PB0 : List Glyph) (s : State)
    (h0 : s.stk 0 = encs rest ++ R)
    (h1 : s.stk sRA = g1 ++ gM :: b1) (hg1 : ∀ x ∈ g1, x ≠ gM)
    (h2 : s.stk sRB = g2 ++ gM :: b2) (hg2 : ∀ x ∈ g2, x ≠ gM)
    (h3 : s.stk sPA = (Computability.encodeNat a.natAbs).reverse.map Glyph.bit ++ gM :: PA0)
    (h4 : s.stk sPB = (Computability.encodeNat b.natAbs).reverse.map Glyph.bit ++ gM :: PB0)
    (hSA : s.reg rSA = sg a) (hSB : s.reg rSB = sg b)
    (hres : IntFlag (s.reg rRes) a b) :
    ∃ s' n, Eval main maxTail s s' n ∧
      n ≤ 5 * (g1.length + g2.length) + 5 * (isz a + isz b) + 40 ∧
      s'.stk 0 = (Val.int (max a b)).enc ++ encs rest ++ R ∧
      s'.stk sRA = b1 ∧ s'.stk sRB = b2 ∧ s'.stk sPA = PA0 ∧ s'.stk sPB = PB0 ∧
      (∀ k, k ≠ 0 → k ≠ sRA → k ≠ sRB → k ≠ sPA → k ≠ sPB → s'.stk k = s.stk k) := by
  obtain ⟨s1, n1, hev1, hn1, h1RA, h1oth, h1reg⟩ :=
    dropMarked_eval main sRA rA rB g1 b1 hg1 s h1
  have h1RB : s1.stk sRB = g2 ++ gM :: b2 := by rw [h1oth sRB (by decide)]; exact h2
  obtain ⟨s2, n2, hev2, hn2, h2RB, h2oth, h2reg⟩ :=
    dropMarked_eval main sRB rA rB g2 b2 hg2 s1 h1RB
  have h2PA : s2.stk sPA
      = (Computability.encodeNat a.natAbs).reverse.map Glyph.bit ++ gM :: PA0 := by
    rw [h2oth sPA (by decide), h1oth sPA (by decide)]; exact h3
  have h2PB : s2.stk sPB
      = (Computability.encodeNat b.natAbs).reverse.map Glyph.bit ++ gM :: PB0 := by
    rw [h2oth sPB (by decide), h1oth sPB (by decide)]; exact h4
  have h2stk0 : s2.stk 0 = encs rest ++ R := by
    rw [h2oth 0 (by decide), h1oth 0 (by decide)]; exact h0
  have h2SA : s2.reg rSA = sg a := by
    rw [h2reg rSA (by decide) (by decide), h1reg rSA (by decide) (by decide)]; exact hSA
  have h2SB : s2.reg rSB = sg b := by
    rw [h2reg rSB (by decide) (by decide), h1reg rSB (by decide) (by decide)]; exact hSB
  have h2res : s2.reg rRes = s.reg rRes := by
    rw [h2reg rRes (by decide) (by decide), h1reg rRes (by decide) (by decide)]
  have hbA : (Computability.encodeNat a.natAbs).length ≤ isz a := by
    rw [encodeNat_length, isz_eq]; omega
  have hbB : (Computability.encodeNat b.natAbs).length ≤ isz b := by
    rw [encodeNat_length, isz_eq]; omega
  by_cases hlt : s.reg rRes = gLt
  · -- a < b: the winner is b, stored on sPB
    have hab : a < b := (IntFlag.lt_iff hres).mp hlt
    obtain ⟨s3, n3, hev3, hn3, h3src, h3dst, h3oth⟩ :=
      loadMarked_eval main sPB 0 rSB rA rB (by decide) (by decide) (by decide)
        b (Computability.encodeNat b.natAbs) PB0 s2 h2SB h2PB rfl
    have h3stk0 : s3.stk 0 = (Val.int b).enc ++ encs rest ++ R := by
      rw [h3dst, h2stk0, List.append_assoc]
    have h3PA : s3.stk sPA
        = (Computability.encodeNat a.natAbs).reverse.map Glyph.bit ++ gM :: PA0 := by
      rw [h3oth sPA (by decide) (by decide)]; exact h2PA
    obtain ⟨s4, n4, hev4, hn4, h4src, h4oth, h4reg⟩ :=
      dropMarked_eval main sPA rA rB ((Computability.encodeNat a.natAbs).reverse.map Glyph.bit)
        PA0 (map_bit_ne_gM _) s3 h3PA
    have h4stk0 : s4.stk 0 = (Val.int b).enc ++ encs rest ++ R := by
      rw [h4oth 0 (by decide)]; exact h3stk0
    have hmax : max a b = b := max_eq_right (le_of_lt hab)
    refine ⟨s4, n1 + (n2 + (n3 + n4 + 1)),
      Eval.seq hev1 (Eval.seq hev2 (Eval.iteT (by rw [h2res]; exact hlt) (Eval.seq hev3 hev4))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hn3' := hn3
      have hn4' := hn4
      simp only [List.length_reverse, List.length_map] at hn4'
      omega
    · rw [h4stk0, hmax]
    · rw [h4oth sRA (by decide), h3oth sRA (by decide) (by decide), h2oth sRA (by decide), h1RA]
    · rw [h4oth sRB (by decide), h3oth sRB (by decide) (by decide), h2RB]
    · exact h4src
    · rw [h4oth sPB (by decide)]; exact h3src
    · intro k hk0 hkRA hkRB hkPA hkPB
      rw [h4oth k hkPA, h3oth k hkPB hk0, h2oth k hkRB, h1oth k hkRA]
  · -- b ≤ a: the winner is a, stored on sPA
    have hmax : max a b = a := by
      rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 hlt
      · rw [h2, max_self]
      · exact max_eq_left (le_of_lt h2)
    obtain ⟨s3, n3, hev3, hn3, h3src, h3dst, h3oth⟩ :=
      loadMarked_eval main sPA 0 rSA rA rB (by decide) (by decide) (by decide)
        a (Computability.encodeNat a.natAbs) PA0 s2 h2SA h2PA rfl
    have h3stk0 : s3.stk 0 = (Val.int a).enc ++ encs rest ++ R := by
      rw [h3dst, h2stk0, List.append_assoc]
    have h3PB : s3.stk sPB
        = (Computability.encodeNat b.natAbs).reverse.map Glyph.bit ++ gM :: PB0 := by
      rw [h3oth sPB (by decide) (by decide)]; exact h2PB
    obtain ⟨s4, n4, hev4, hn4, h4src, h4oth, h4reg⟩ :=
      dropMarked_eval main sPB rA rB ((Computability.encodeNat b.natAbs).reverse.map Glyph.bit)
        PB0 (map_bit_ne_gM _) s3 h3PB
    have h4stk0 : s4.stk 0 = (Val.int a).enc ++ encs rest ++ R := by
      rw [h4oth 0 (by decide)]; exact h3stk0
    refine ⟨s4, n1 + (n2 + (n3 + n4 + 1)),
      Eval.seq hev1 (Eval.seq hev2 (Eval.iteF (by rw [h2res]; exact hlt) (Eval.seq hev3 hev4))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hn4' := hn4
      simp only [List.length_reverse, List.length_map] at hn4'
      omega
    · rw [h4stk0, hmax]
    · rw [h4oth sRA (by decide), h3oth sRA (by decide) (by decide), h2oth sRA (by decide), h1RA]
    · rw [h4oth sRB (by decide), h3oth sRB (by decide) (by decide), h2RB]
    · rw [h4oth sPA (by decide)]; exact h3src
    · exact h4src
    · intro k hk0 hkRA hkRB hkPA hkPB
      rw [h4oth k hkPB, h3oth k hkPA hk0, h2oth k hkRB, h1oth k hkRA]

/-! ## Small helpers for the negation word -/

/-- Canonical result state of `set r g ; push 0 r`. -/
def setPushState (s : State) (r : Reg) (g : Glyph) : State := State.tPush (State.tSet s r g) 0 r

theorem setPush_eval (main : Cmd) (s : State) (r : Reg) (g : Glyph) :
    Eval main (.seq (.set r g) (.push 0 r)) s (setPushState s r g) 2 :=
  Eval.seq (eval_set main r g s) (eval_push main 0 r (State.tSet s r g))

theorem setPushState_stk (s : State) (r : Reg) (g : Glyph) :
    (setPushState s r g).stk 0 = g :: s.stk 0 := by
  rw [setPushState, tPush_stk, if_pos rfl, tSet_reg, if_pos rfl, tSet_stk]

theorem setPushState_stk_ne (s : State) (r : Reg) (g : Glyph) (j : Stk) (h : j ≠ 0) :
    (setPushState s r g).stk j = s.stk j := by
  rw [setPushState, tPush_stk, if_neg h, tSet_stk]

theorem tPeek_stk (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPeek s k r).stk j = s.stk j := rfl

theorem tPeek_reg (s : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPeek s k r).reg r' = if r' = r then (s.stk k).headD Glyph.eos else s.reg r' := by
  rw [show State.tPeek s k r = s.updReg r ((s.stk k).headD Glyph.eos) from rfl, State.updReg_apply]

/-- A run of `negProg` from a state whose stack `0` starts with `int a`. -/
theorem negProg_eval (main : Cmd) (a : ℤ) (rest : List Val) (R : List Glyph) (s : State)
    (h0 : s.stk 0 = (Val.int a).enc ++ encs rest ++ R) :
    ∃ s' n, Eval main negProg s s' n ∧ n ≤ 4 * isz a ∧
      s'.stk 0 = (Val.int (-a)).enc ++ encs rest ++ R ∧
      (∀ k, k ≠ 0 → s'.stk k = s.stk k) := by
  have h0' : s.stk 0 = sg a :: ((Computability.encodeNat a.natAbs).map Glyph.bit
      ++ [Glyph.iend] ++ encs rest ++ R) := by
    rw [h0, enc_int']
    simp only [List.cons_append, List.append_assoc]
  let s1 : State := State.tPop s 0 rA
  have e1 : Eval main (.pop 0 rA) s s1 1 := by
    rw [show s1 = State.tPop s 0 rA from rfl]; exact eval_pop main 0 rA s
  have h1reg : s1.reg rA = sg a := by
    rw [show s1 = State.tPop s 0 rA from rfl, tPop_reg, if_pos rfl, h0']
    rfl
  have h1stk : s1.stk 0 = (Computability.encodeNat a.natAbs).map Glyph.bit
      ++ [Glyph.iend] ++ encs rest ++ R := by
    rw [show s1 = State.tPop s 0 rA from rfl, tPop_stk, if_pos rfl, h0']
    rfl
  have h1oth : ∀ k, k ≠ 0 → s1.stk k = s.stk k := by
    intro k hk
    rw [show s1 = State.tPop s 0 rA from rfl, tPop_stk, if_neg hk]
  have hisz : 2 ≤ isz a := by rw [isz_eq]; omega
  by_cases hneg : sg a = Glyph.neg
  · -- `a < 0`: the sign becomes `pos`
    have ha : a < 0 := by
      by_contra hcon
      rw [sg_pos hcon] at hneg
      exact absurd hneg (by decide)
    have hnega : ¬ (-a) < 0 := by omega
    have henc : (Val.int (-a)).enc = Glyph.pos :: ((Computability.encodeNat a.natAbs).map Glyph.bit
        ++ [Glyph.iend]) := by
      rw [enc_int', sg_pos hnega, Int.natAbs_neg]
      simp only [List.cons_append]
    have ev : Eval main negProg s (setPushState s1 rA Glyph.pos) 4 :=
      Eval.seq e1 (Eval.iteT (by rw [h1reg, hneg]) (setPush_eval main s1 rA Glyph.pos))
    refine ⟨setPushState s1 rA Glyph.pos, 4, ev, by omega, ?_, ?_⟩
    · rw [setPushState_stk, h1stk, henc]
      simp only [List.cons_append, List.append_assoc]
    · intro k hk
      rw [setPushState_stk_ne s1 rA Glyph.pos k hk, h1oth k hk]
  · -- `a ≥ 0`: look at the magnitude
    have hpos : sg a = Glyph.pos := by
      by_cases h : a < 0
      · exact absurd (sg_neg h) hneg
      · exact sg_pos h
    have hge : 0 ≤ a := by
      by_contra hcon
      exact hneg (sg_neg (by omega))
    have h1ne : s1.reg rA ≠ Glyph.neg := by rw [h1reg, hpos]; decide
    let s2 : State := State.tPeek s1 0 rB
    have e2 : Eval main (.peek 0 rB) s1 s2 1 := by
      rw [show s2 = State.tPeek s1 0 rB from rfl]; exact eval_peek main 0 rB s1
    have h2stk : s2.stk 0 = (Computability.encodeNat a.natAbs).map Glyph.bit
        ++ [Glyph.iend] ++ encs rest ++ R := by
      rw [show s2 = State.tPeek s1 0 rB from rfl, tPeek_stk, h1stk]
    have h2oth : ∀ k, s2.stk k = s1.stk k := by
      intro k; rw [show s2 = State.tPeek s1 0 rB from rfl, tPeek_stk]
    rcases hbits : Computability.encodeNat a.natAbs with _ | ⟨b0, t⟩
    · -- `a = 0`: the sign stays `pos`
      have haz : a = 0 := by
        have h1 : Work.IntLib.ofBits (Computability.encodeNat a.natAbs) = a.natAbs := by
          rw [encodeNat_eq_bits]; exact ofBits_bits a.natAbs
        rw [hbits] at h1
        exact Int.natAbs_eq_zero.mp h1.symm
      have h1stk0 : s1.stk 0 = Glyph.iend :: (encs rest ++ R) := by
        rw [h1stk, hbits]; simp
      have h2reg : s2.reg rB = Glyph.iend := by
        rw [show s2 = State.tPeek s1 0 rB from rfl, tPeek_reg, if_pos rfl, h1stk0]
        rfl
      have henc : (Val.int (-a)).enc = [Glyph.pos, Glyph.iend] := by
        have hna : -a = 0 := by omega
        rw [enc_int', sg_pos (by omega), hna]
        rfl
      have ev : Eval main negProg s (setPushState s2 rA Glyph.pos) 6 :=
        Eval.seq e1 (Eval.iteF h1ne
          (Eval.seq e2 (Eval.iteT h2reg (setPush_eval main s2 rA Glyph.pos))))
      refine ⟨setPushState s2 rA Glyph.pos, 6, ev, by omega, ?_, ?_⟩
      · rw [setPushState_stk, h2stk, henc, hbits]
        simp only [List.map_nil, List.nil_append, List.cons_append, List.append_assoc]
      · intro k hk
        rw [setPushState_stk_ne s2 rA Glyph.pos k hk, h2oth k, h1oth k hk]
    · -- `a > 0`: the sign becomes `neg`
      have hne0 : a.natAbs ≠ 0 := by
        intro hz
        have hlen0 : (Computability.encodeNat 0).length = 0 := rfl
        have h1 : (Computability.encodeNat a.natAbs).length = (b0 :: t).length := by rw [hbits]
        rw [hz, hlen0] at h1
        have h2 : 0 = t.length + 1 := by simpa using h1
        omega
      have hposa : 0 < a := by
        by_contra hcon
        have haz : a = 0 := by omega
        exact hne0 (Int.natAbs_eq_zero.mpr haz)
      have hnega : -a < 0 := by omega
      have henc : (Val.int (-a)).enc = Glyph.neg :: ((Computability.encodeNat a.natAbs).map Glyph.bit
          ++ [Glyph.iend]) := by
        rw [enc_int', sg_neg hnega, Int.natAbs_neg]
        simp only [List.cons_append]
      have h1stk0 : s1.stk 0 = Glyph.bit b0 :: (t.map Glyph.bit ++ [Glyph.iend]
          ++ encs rest ++ R) := by
        rw [h1stk, hbits]; simp only [List.map_cons, List.cons_append, List.append_assoc]
      have h2reg : s2.reg rB = Glyph.bit b0 := by
        rw [show s2 = State.tPeek s1 0 rB from rfl, tPeek_reg, if_pos rfl, h1stk0]
        rfl
      have h2ne : s2.reg rB ≠ Glyph.iend := by
        rw [h2reg]; exact fun h => nomatch h
      have ev : Eval main negProg s (setPushState s2 rA Glyph.neg) 6 :=
        Eval.seq e1 (Eval.iteF h1ne
          (Eval.seq e2 (Eval.iteF h2ne (setPush_eval main s2 rA Glyph.neg))))
      refine ⟨setPushState s2 rA Glyph.neg, 6, ev, by omega, ?_, ?_⟩
      · rw [setPushState_stk, h2stk, henc, hbits]
        simp only [List.map_cons, List.nil_append, List.cons_append, List.append_assoc]
      · intro k hk
        rw [setPushState_stk_ne s2 rA Glyph.neg k hk, h2oth k, h1oth k hk]

/-- The negation word. -/
theorem negWord : ∃ (p : Cmd) (K : ℕ), ∀ main,
    UnOp main p (fun _ => True) (fun a => -a) (fun a => K * isz a) := by
  refine ⟨negProg, 4, ?_⟩
  intro main vs hpre s R h0
  obtain ⟨a, rest, rfl, _⟩ := hpre
  obtain ⟨s', n, hev, hn, hstk, hoth⟩ := negProg_eval main a rest R s h0
  exact ⟨.int (-a) :: rest, s', n, ⟨a, rest, rfl, rfl⟩, hev, hn, hstk, hoth⟩

/-- The common leading part of the binary comparison words: the two magnitudes are stored on
`sPA`/`sPB` (sign glyphs on `sSA`/`sSB`), a copy is reversed onto `sRA`/`sRB`, and the parallel scan
records the comparison of the two magnitudes in `rRes`.

PROVED here: `core_eval` composes the chain

  `storeMag sPA/sSA` -> `storeMag sPB/sSB` -> `copyMarked2 sPA sCA` -> `copyMarked2 sPB sCB`
  -> `revMarked sCA sRA` -> `revMarked sCB sRB` -> `set rFlag gEq` -> `set rCont eos` -> `scanLoop`
  -> `pop sSA rSA` -> `pop sSB rSB` -> `combineProg`

with `Eval.seq`, propagating the `hoth`-frame facts, and hands the result to the tails
`cmpTail gLt`/`cmpTail gEq` and `maxTail`. -/
theorem core_eval (main : Cmd) (a b : ℤ) (rest : List Val) (R : List Glyph) (s : State)
    (h0 : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R) :
    ∃ s' n, Eval main coreProg s s' n ∧ n ≤ 130 * (isz a + isz b + 1) ∧
      s'.stk 0 = encs rest ++ R ∧
      IntFlag (s'.reg rRes) a b ∧
      (∃ gA gB, (∀ g ∈ gA, g ≠ gM) ∧ (∀ g ∈ gB, g ≠ gM) ∧
        gA.length ≤ (Computability.encodeNat a.natAbs).length ∧
        gB.length ≤ (Computability.encodeNat b.natAbs).length ∧
        s'.stk sRA = gA ++ gM :: s.stk sRA ∧ s'.stk sRB = gB ++ gM :: s.stk sRB) ∧
      s'.stk sPA = (Computability.encodeNat a.natAbs).reverse.map Glyph.bit ++ gM :: s.stk sPA ∧
      s'.stk sPB = (Computability.encodeNat b.natAbs).reverse.map Glyph.bit ++ gM :: s.stk sPB ∧
      (∀ j, j ≠ 0 → j ≠ sPA → j ≠ sPB → j ≠ sRA → j ≠ sRB → s'.stk j = s.stk j) ∧
      s'.reg rSA = sg a ∧ s'.reg rSB = sg b := by
  set ga := (Computability.encodeNat a.natAbs).reverse.map Glyph.bit with hga
  set gb := (Computability.encodeNat b.natAbs).reverse.map Glyph.bit with hgb
  -- step 1: store the magnitude of a
  have h0a : s.stk 0 = (Val.int a).enc ++ encs (Val.int b :: rest) ++ R := by
    rw [h0]; simp [encs_cons, List.append_assoc]
  obtain ⟨s1, n1, hev1, hn1, h0_1, hPA1, hSA1, hoth1⟩ :=
    storeMag_frame main sPA sSA a (Val.int b :: rest) R s (by decide) (by decide) (by decide) h0a
  -- step 2: store the magnitude of b
  have h1b : s1.stk 0 = (Val.int b).enc ++ encs rest ++ R := by rw [h0_1, encs_cons]
  obtain ⟨s2, n2, hev2, hn2, h0_2, hPB2, hSB2, hoth2⟩ :=
    storeMag_frame main sPB sSB b rest R s1 (by decide) (by decide) (by decide) h1b
  -- step 3: copy the magnitude of a
  have hPA2 : s2.stk sPA = ga ++ gM :: s.stk sPA := by
    rw [hoth2 sPA (by decide) (by decide) (by decide), hPA1]
  obtain ⟨s3, n3, hev3, hn3, hPA3, hCA3, hTA3, hoth3⟩ :=
    copyMarked2_eval main sPA sCA sTA rA rB (by decide) (by decide) (by decide) (by decide)
      ga (s.stk sPA) (by rw [hga]; exact map_bit_ne_gM _) (by rw [hga]; exact map_bit_ne_gM2 _)
      s2 hPA2
  -- step 4: copy the magnitude of b
  have hPB3 : s3.stk sPB = gb ++ gM :: s.stk sPB := by
    rw [hoth3 sPB (by decide) (by decide) (by decide), hPB2,
      hoth1 sPB (by decide) (by decide) (by decide)]
  obtain ⟨s4, n4, hev4, hn4, hPB4, hCB4, hTB4, hoth4⟩ :=
    copyMarked2_eval main sPB sCB sTB rA rB (by decide) (by decide) (by decide) (by decide)
      gb (s.stk sPB) (by rw [hgb]; exact map_bit_ne_gM _) (by rw [hgb]; exact map_bit_ne_gM2 _)
      s3 hPB3
  -- step 5: reverse the copy of a into sRA
  have hCA4 : s4.stk sCA = ga ++ gM :: s.stk sCA := by
    rw [hoth4 sCA (by decide) (by decide) (by decide), hCA3,
      hoth2 sCA (by decide) (by decide) (by decide), hoth1 sCA (by decide) (by decide) (by decide)]
  obtain ⟨s5, n5, hev5, hn5, hCA5, hRA5, hoth5⟩ :=
    revMarked_eval main sCA sRA rA rB (by decide) ga (s.stk sCA)
      (by rw [hga]; exact map_bit_ne_gM _) s4 hCA4
  -- step 6: reverse the copy of b into sRB
  have hCB5 : s5.stk sCB = gb ++ gM :: s.stk sCB := by
    rw [hoth5 sCB (by decide) (by decide), hCB4, hoth3 sCB (by decide) (by decide) (by decide),
      hoth2 sCB (by decide) (by decide) (by decide), hoth1 sCB (by decide) (by decide) (by decide)]
  obtain ⟨s6, n6, hev6, hn6, hCB6, hRB6, hoth6⟩ :=
    revMarked_eval main sCB sRB rA rB (by decide) gb (s.stk sCB)
      (by rw [hgb]; exact map_bit_ne_gM _) s5 hCB5
  -- step 7: reset the flag
  let s7 : State := State.tSet s6 rFlag gEq
  have hev7 : Eval main (.set rFlag gEq) s6 s7 1 := by
    rw [show s7 = State.tSet s6 rFlag gEq from rfl]; exact eval_set main rFlag gEq s6
  have h7f : s7.reg rFlag = gEq := by
    rw [show s7 = State.tSet s6 rFlag gEq from rfl, tSet_reg, if_pos rfl]
  -- step 8: reset the loop register
  let s8 : State := State.tSet s7 rCont Glyph.eos
  have hev8 : Eval main (.set rCont Glyph.eos) s7 s8 1 := by
    rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl]; exact eval_set main rCont Glyph.eos s7
  have h8c : s8.reg rCont = Glyph.eos := by
    rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_reg, if_pos rfl]
  -- the two stacks the scan reads
  have h8RA : s8.stk sRA = (Computability.encodeNat a.natAbs).map Glyph.bit ++ gM :: s.stk sRA := by
    rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_stk,
      show s7 = State.tSet s6 rFlag gEq from rfl, tSet_stk,
      hoth6 sRA (by decide) (by decide), hRA5,
      hoth4 sRA (by decide) (by decide) (by decide), hoth3 sRA (by decide) (by decide) (by decide),
      hoth2 sRA (by decide) (by decide) (by decide), hoth1 sRA (by decide) (by decide) (by decide)]
    rw [hga, List.map_reverse, List.reverse_reverse]
  have h8RB : s8.stk sRB = (Computability.encodeNat b.natAbs).map Glyph.bit ++ gM :: s.stk sRB := by
    rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_stk,
      show s7 = State.tSet s6 rFlag gEq from rfl, tSet_stk, hRB6,
      hoth5 sRB (by decide) (by decide), hoth4 sRB (by decide) (by decide) (by decide),
      hoth3 sRB (by decide) (by decide) (by decide), hoth2 sRB (by decide) (by decide) (by decide),
      hoth1 sRB (by decide) (by decide) (by decide)]
    rw [hgb, List.map_reverse, List.reverse_reverse]
  -- step 9: the parallel scan
  obtain ⟨s10, n10, hev10, h10c, h10f, h10oth, h10shape, hn10⟩ :=
    scanLoop_eval main (Computability.encodeNat a.natAbs) (Computability.encodeNat b.natAbs)
      (s.stk sRA) (s.stk sRB) s8 (IsBits_encodeNat _) (IsBits_encodeNat _) h8RA h8RB h8c h7f
  have h10nf : NatFlag (s10.reg rFlag) a.natAbs b.natAbs := by
    rw [← ofBits_encodeNat a.natAbs, ← ofBits_encodeNat b.natAbs]; exact h10f
  -- the sign stacks survive the scan, which only touches sRA/sRB
  have h10SA : s10.stk sSA = sg a :: s.stk sSA := by
    rw [h10oth sSA (by decide) (by decide),
      show s8.stk sSA = s7.stk sSA from by
        rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_stk],
      show s7.stk sSA = s6.stk sSA from by
        rw [show s7 = State.tSet s6 rFlag gEq from rfl, tSet_stk],
      hoth6 sSA (by decide) (by decide), hoth5 sSA (by decide) (by decide),
      hoth4 sSA (by decide) (by decide) (by decide), hoth3 sSA (by decide) (by decide) (by decide),
      hoth2 sSA (by decide) (by decide) (by decide), hSA1]
  have h10SB : s10.stk sSB = sg b :: s.stk sSB := by
    rw [h10oth sSB (by decide) (by decide),
      show s8.stk sSB = s7.stk sSB from by
        rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_stk],
      show s7.stk sSB = s6.stk sSB from by
        rw [show s7 = State.tSet s6 rFlag gEq from rfl, tSet_stk],
      hoth6 sSB (by decide) (by decide), hoth5 sSB (by decide) (by decide),
      hoth4 sSB (by decide) (by decide) (by decide), hoth3 sSB (by decide) (by decide) (by decide),
      hSB2, hoth1 sSB (by decide) (by decide) (by decide)]
  -- step 10, 11: recover the sign glyphs (after the scan, so the scan cannot clobber them)
  let s11 : State := State.tPop s10 sSA rSA
  have hev11 : Eval main (.pop sSA rSA) s10 s11 1 := by
    rw [show s11 = State.tPop s10 sSA rSA from rfl]; exact eval_pop main sSA rSA s10
  have h11r : s11.reg rSA = sg a := by
    rw [show s11 = State.tPop s10 sSA rSA from rfl, tPop_reg, if_pos rfl, h10SA]; rfl
  let s12 : State := State.tPop s11 sSB rSB
  have hev12 : Eval main (.pop sSB rSB) s11 s12 1 := by
    rw [show s12 = State.tPop s11 sSB rSB from rfl]; exact eval_pop main sSB rSB s11
  have h12r : s12.reg rSB = sg b := by
    rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_reg, if_pos rfl,
      show s11 = State.tPop s10 sSA rSA from rfl, tPop_stk, if_neg hSB_ne_hSA, h10SB]
    rfl
  have h12rA : s12.reg rSA = sg a := by
    rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_reg, if_neg (by decide : rSA ≠ rSB)]
    exact h11r
  -- step 12: combine the signs with the magnitude comparison
  obtain ⟨n13, hn13, hev13⟩ := combine_eval main s12 (s12.reg rFlag) (sg a) (sg b) h12rA h12r rfl
  have fwd6 : ∀ j, j ≠ sCB → j ≠ sRB → j ≠ sRA → j ≠ sSA → j ≠ sSB →
      (s12.updReg rRes (cFlag (s12.reg rFlag) (sg a) (sg b))).stk j = s6.stk j := by
    intro j hCB hRB hRA hSA hSB
    rw [State.updReg_stk,
      show s12.stk j = s11.stk j from by
        rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_stk, if_neg hSB],
      show s11.stk j = s10.stk j from by
        rw [show s11 = State.tPop s10 sSA rSA from rfl, tPop_stk, if_neg hSA],
      h10oth j hRA hRB,
      show s8.stk j = s7.stk j from by
        rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_stk],
      show s7.stk j = s6.stk j from by
        rw [show s7 = State.tSet s6 rFlag gEq from rfl, tSet_stk]]
  have fwd10 : ∀ j, j ≠ sSA → j ≠ sSB →
      (s12.updReg rRes (cFlag (s12.reg rFlag) (sg a) (sg b))).stk j = s10.stk j := by
    intro j hSA hSB
    rw [State.updReg_stk,
      show s12.stk j = s11.stk j from by
        rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_stk, if_neg hSB],
      show s11.stk j = s10.stk j from by
        rw [show s11 = State.tPop s10 sSA rSA from rfl, tPop_stk, if_neg hSA]]
  have back : ∀ j, j ≠ 0 → j ≠ sPA → j ≠ sPB → j ≠ sSA → j ≠ sSB → j ≠ sCA → j ≠ sCB →
      j ≠ sTA → j ≠ sTB → j ≠ sRA → j ≠ sRB → s6.stk j = s.stk j := by
    intro j h0 hPA hPB hSA hSB hCA hCB hTA hTB hRA hRB
    rw [hoth6 j hCB hRB, hoth5 j hCA hRA, hoth4 j hPB hCB hTB, hoth3 j hPA hCA hTA,
      hoth2 j h0 hPB hSB, hoth1 j h0 hPA hSA]
  refine ⟨s12.updReg rRes (cFlag (s12.reg rFlag) (sg a) (sg b)),
    n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (1 + (1 + (n10 + (1 + (1 + n13)))))))))),
    Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 (Eval.seq hev5 (Eval.seq hev6
      (Eval.seq hev7 (Eval.seq hev8 (Eval.seq hev10 (Eval.seq hev11 (Eval.seq hev12 hev13)))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have hsz : 2 ≤ isz a + isz b := by rw [isz_eq, isz_eq]; omega
    have h1 : (Computability.encodeNat a.natAbs).length ≤ isz a := by
      rw [encodeNat_length, isz_eq]; omega
    have h2 : (Computability.encodeNat b.natAbs).length ≤ isz b := by
      rw [encodeNat_length, isz_eq]; omega
    have h3 : ga.length ≤ isz a := by
      rw [hga]; simp only [List.length_map, List.length_reverse]; omega
    have h4 : gb.length ≤ isz b := by
      rw [hgb]; simp only [List.length_map, List.length_reverse]; omega
    have hn10' : n10 ≤ 12 * (((Computability.encodeNat a.natAbs).length
      + (Computability.encodeNat b.natAbs).length) + 1) := hn10
    have hn13' : n13 ≤ 6 := hn13
    omega
  · -- stack 0
    rw [fwd6 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hoth6 0 (by decide) (by decide), hoth5 0 (by decide) (by decide),
      hoth4 0 (by decide) (by decide) (by decide), hoth3 0 (by decide) (by decide) (by decide)]
    exact h0_2
  · -- the flag
    rw [State.updReg_apply, if_pos rfl]
    exact combine_flag a b (s12.reg rFlag) h10nf
  · -- the shapes of sRA and sRB: the scan leaves the rest of the magnitude above the marker
    obtain ⟨gA, gB, hA, hB, hlenA, hlenB, hshA, hshB⟩ := h10shape
    exact ⟨gA, gB, hA, hB, hlenA, hlenB, by rw [fwd10 sRA (by decide) (by decide), hshA],
      by rw [fwd10 sRB (by decide) (by decide), hshB]⟩
  · -- sPA
    rw [fwd6 sPA (by decide) (by decide) (by decide) (by decide) (by decide),
      hoth6 sPA (by decide) (by decide), hoth5 sPA (by decide) (by decide),
      hoth4 sPA (by decide) (by decide) (by decide)]
    exact hPA3
  · -- sPB
    rw [fwd6 sPB (by decide) (by decide) (by decide) (by decide) (by decide),
      hoth6 sPB (by decide) (by decide), hoth5 sPB (by decide) (by decide)]
    exact hPB4
  · -- the frame
    intro j hj0 hjPA hjPB hjRA hjRB
    by_cases hSA : j = sSA
    · subst hSA
      rw [State.updReg_stk,
        show s12.stk sSA = s11.stk sSA from by
          rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_stk,
            if_neg (by decide : sSA ≠ sSB)],
        show s11.stk sSA = (s10.stk sSA).tail from by
          rw [show s11 = State.tPop s10 sSA rSA from rfl, tPop_stk, if_pos rfl],
        h10SA]
      simp
    · by_cases hSB : j = sSB
      · subst hSB
        rw [State.updReg_stk,
          show s12.stk sSB = (s10.stk sSB).tail from by
            rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_stk, if_pos rfl,
              show s11.stk sSB = s10.stk sSB from by
                rw [show s11 = State.tPop s10 sSA rSA from rfl, tPop_stk,
                  if_neg (by decide : sSB ≠ sSA)]],
          h10SB]
        simp
      · by_cases hCA : j = sCA
        · subst hCA
          rw [fwd6 sCA (by decide) (by decide) (by decide) (by decide) (by decide),
            hoth6 sCA (by decide) (by decide), hCA5]
        · by_cases hCB : j = sCB
          · subst hCB
            rw [State.updReg_stk,
              show s12.stk sCB = s11.stk sCB from by
                rw [show s12 = State.tPop s11 sSB rSB from rfl, tPop_stk,
                  if_neg (by decide : sCB ≠ sSB)],
              show s11.stk sCB = s10.stk sCB from by
                rw [show s11 = State.tPop s10 sSA rSA from rfl, tPop_stk,
                  if_neg (by decide : sCB ≠ sSA)],
              h10oth sCB (by decide) (by decide),
              show s8.stk sCB = s7.stk sCB from by
                rw [show s8 = State.tSet s7 rCont Glyph.eos from rfl, tSet_stk],
              show s7.stk sCB = s6.stk sCB from by
                rw [show s7 = State.tSet s6 rFlag gEq from rfl, tSet_stk],
              hCB6]
          · by_cases hTA : j = sTA
            · subst hTA
              rw [fwd6 sTA (by decide) (by decide) (by decide) (by decide) (by decide),
                hoth6 sTA (by decide) (by decide), hoth5 sTA (by decide) (by decide),
                hoth4 sTA (by decide) (by decide) (by decide), hTA3,
                hoth2 sTA (by decide) (by decide) (by decide),
                hoth1 sTA (by decide) (by decide) (by decide)]
            · by_cases hTB : j = sTB
              · subst hTB
                rw [fwd6 sTB (by decide) (by decide) (by decide) (by decide) (by decide),
                  hoth6 sTB (by decide) (by decide), hoth5 sTB (by decide) (by decide),
                  hTB4, hoth3 sTB (by decide) (by decide) (by decide),
                  hoth2 sTB (by decide) (by decide) (by decide),
                  hoth1 sTB (by decide) (by decide) (by decide)]
              · rw [fwd6 j hCB hjRB hjRA hSA hSB]
                rw [back j hj0 hjPA hjPB hSA hSB hCA hCB hTA hTB hjRA hjRB]
  · -- the sign registers
    rw [State.updReg_apply, if_neg (by decide : rSA ≠ rRes)]
    exact h12rA
  · rw [State.updReg_apply, if_neg (by decide : rSB ≠ rRes)]
    exact h12r

/-! ## The four integer words -/

/-- A generic end of a binary word: stack `0` holds the result, the four drained stacks are
restored. -/
theorem binFrame (s s' s1 : State) (k : Stk)
    (h1 : ∀ j, j ≠ 0 → j ≠ sPA → j ≠ sPB → j ≠ sRA → j ≠ sRB → s1.stk j = s.stk j)
    (h2 : ∀ j, j ≠ 0 → j ≠ sRA → j ≠ sRB → j ≠ sPA → j ≠ sPB → s'.stk j = s1.stk j)
    (hk0 : k ≠ 0) (hRA : k ≠ sRA) (hRB : k ≠ sRB) (hPA : k ≠ sPA) (hPB : k ≠ sPB) :
    s'.stk k = s.stk k := by
  rw [h2 k hk0 hRA hRB hPA hPB, h1 k hk0 hPA hPB hRA hRB]

/-- The `lt` word. -/
theorem ltWord : ∃ (p : Cmd) (K : ℕ), ∀ main,
    BinOp main p (fun _ _ => True) (fun a b => if a < b then (1 : ℤ) else 0)
      (fun a b => K * (isz a + isz b)) := by
  refine ⟨.seq coreProg (cmpTail gLt), 200, ?_⟩
  intro main vs hpre s R h0
  obtain ⟨a, b, rest, rfl, _⟩ := hpre
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R := by
    rw [h0]; simp only [encs_cons, List.append_assoc]
  obtain ⟨s1, n1, hev1, hn1, h10, h1f, h1shape, h1PA, h1PB, h1oth, h1SA, h1SB⟩ :=
    core_eval main a b rest R s h0'
  obtain ⟨gA, gB, hgA, hgB, hlenA, hlenB, hshA, hshB⟩ := h1shape
  obtain ⟨s2, n2, hev2, hn2, h2stk0, h2RA, h2RB, h2PA, h2PB, h2oth⟩ :=
    cmpTailEval main gLt rest R gA gB
      ((Computability.encodeNat a.natAbs).reverse.map Glyph.bit)
      ((Computability.encodeNat b.natAbs).reverse.map Glyph.bit)
      (s.stk sRA) (s.stk sRB) (s.stk sPA) (s.stk sPB) s1
      h10 hshA hgA hshB hgB h1PA (map_bit_ne_gM _) h1PB (map_bit_ne_gM _)
  have hltiff : (s1.reg rRes = gLt) ↔ a < b := IntFlag.lt_iff h1f
  have hencout : (if s1.reg rRes = gLt then (Val.int (1 : ℤ)).enc else (Val.int (0 : ℤ)).enc)
      = (Val.int (if a < b then (1 : ℤ) else 0)).enc := by
    by_cases hab : a < b
    · rw [if_pos (hltiff.mpr hab), if_pos hab]
    · rw [if_neg (fun h => hab (hltiff.mp h)), if_neg hab]
  refine ⟨.int (if a < b then (1 : ℤ) else 0) :: rest, s2, n1 + n2,
    ⟨a, b, rest, rfl, rfl⟩, Eval.seq hev1 hev2, ?_, ?_, ?_⟩
  · change n1 + n2 ≤ 200 * (isz a + isz b)
    have hS : 4 ≤ isz a + isz b := by rw [isz_eq, isz_eq]; omega
    have hbA : (Computability.encodeNat a.natAbs).length ≤ isz a := by
      rw [encodeNat_length, isz_eq]; omega
    have hbB : (Computability.encodeNat b.natAbs).length ≤ isz b := by
      rw [encodeNat_length, isz_eq]; omega
    have hga : gA.length ≤ isz a := le_trans hlenA hbA
    have hgb : gB.length ≤ isz b := le_trans hlenB hbB
    have hn2' := hn2
    simp only [List.length_reverse, List.length_map] at hn2'
    omega
  · rw [h2stk0, hencout, encs_cons]
  · intro k hk0
    by_cases hRA : k = sRA
    · subst hRA; exact h2RA
    by_cases hRB : k = sRB
    · subst hRB; exact h2RB
    by_cases hPA : k = sPA
    · subst hPA; exact h2PA
    by_cases hPB : k = sPB
    · subst hPB; exact h2PB
    exact binFrame s s2 s1 k h1oth h2oth hk0 hRA hRB hPA hPB

/-- The `eq` word. -/
theorem eqWord : ∃ (p : Cmd) (K : ℕ), ∀ main,
    BinOp main p (fun _ _ => True) (fun a b => if a = b then (1 : ℤ) else 0)
      (fun a b => K * (isz a + isz b)) := by
  refine ⟨.seq coreProg (cmpTail gEq), 200, ?_⟩
  intro main vs hpre s R h0
  obtain ⟨a, b, rest, rfl, _⟩ := hpre
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R := by
    rw [h0]; simp only [encs_cons, List.append_assoc]
  obtain ⟨s1, n1, hev1, hn1, h10, h1f, h1shape, h1PA, h1PB, h1oth, h1SA, h1SB⟩ :=
    core_eval main a b rest R s h0'
  obtain ⟨gA, gB, hgA, hgB, hlenA, hlenB, hshA, hshB⟩ := h1shape
  obtain ⟨s2, n2, hev2, hn2, h2stk0, h2RA, h2RB, h2PA, h2PB, h2oth⟩ :=
    cmpTailEval main gEq rest R gA gB
      ((Computability.encodeNat a.natAbs).reverse.map Glyph.bit)
      ((Computability.encodeNat b.natAbs).reverse.map Glyph.bit)
      (s.stk sRA) (s.stk sRB) (s.stk sPA) (s.stk sPB) s1
      h10 hshA hgA hshB hgB h1PA (map_bit_ne_gM _) h1PB (map_bit_ne_gM _)
  have heqiff : (s1.reg rRes = gEq) ↔ a = b := IntFlag.eq_iff h1f
  have hencout : (if s1.reg rRes = gEq then (Val.int (1 : ℤ)).enc else (Val.int (0 : ℤ)).enc)
      = (Val.int (if a = b then (1 : ℤ) else 0)).enc := by
    by_cases hab : a = b
    · rw [if_pos (heqiff.mpr hab), if_pos hab]
    · rw [if_neg (fun h => hab (heqiff.mp h)), if_neg hab]
  refine ⟨.int (if a = b then (1 : ℤ) else 0) :: rest, s2, n1 + n2,
    ⟨a, b, rest, rfl, rfl⟩, Eval.seq hev1 hev2, ?_, ?_, ?_⟩
  · change n1 + n2 ≤ 200 * (isz a + isz b)
    have hS : 4 ≤ isz a + isz b := by rw [isz_eq, isz_eq]; omega
    have hbA : (Computability.encodeNat a.natAbs).length ≤ isz a := by
      rw [encodeNat_length, isz_eq]; omega
    have hbB : (Computability.encodeNat b.natAbs).length ≤ isz b := by
      rw [encodeNat_length, isz_eq]; omega
    have hga : gA.length ≤ isz a := le_trans hlenA hbA
    have hgb : gB.length ≤ isz b := le_trans hlenB hbB
    have hn2' := hn2
    simp only [List.length_reverse, List.length_map] at hn2'
    omega
  · rw [h2stk0, hencout, encs_cons]
  · intro k hk0
    by_cases hRA : k = sRA
    · subst hRA; exact h2RA
    by_cases hRB : k = sRB
    · subst hRB; exact h2RB
    by_cases hPA : k = sPA
    · subst hPA; exact h2PA
    by_cases hPB : k = sPB
    · subst hPB; exact h2PB
    exact binFrame s s2 s1 k h1oth h2oth hk0 hRA hRB hPA hPB

/-- The `max` word. -/
theorem maxWord : ∃ (p : Cmd) (K : ℕ), ∀ main,
    BinOp main p (fun _ _ => True) max (fun a b => K * (isz a + isz b)) := by
  refine ⟨.seq coreProg maxTail, 200, ?_⟩
  intro main vs hpre s R h0
  obtain ⟨a, b, rest, rfl, _⟩ := hpre
  have h0' : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R := by
    rw [h0]; simp only [encs_cons, List.append_assoc]
  obtain ⟨s1, n1, hev1, hn1, h10, h1f, h1shape, h1PA, h1PB, h1oth, h1SA, h1SB⟩ :=
    core_eval main a b rest R s h0'
  obtain ⟨gA, gB, hgA, hgB, hlenA, hlenB, hshA, hshB⟩ := h1shape
  obtain ⟨s2, n2, hev2, hn2, h2stk0, h2RA, h2RB, h2PA, h2PB, h2oth⟩ :=
    maxTailEval main a b rest R gA gB (s.stk sRA) (s.stk sRB) (s.stk sPA) (s.stk sPB) s1
      h10 hshA hgA hshB hgB h1PA h1PB h1SA h1SB h1f
  refine ⟨.int (max a b) :: rest, s2, n1 + n2, ⟨a, b, rest, rfl, rfl⟩,
    Eval.seq hev1 hev2, ?_, ?_, ?_⟩
  · change n1 + n2 ≤ 200 * (isz a + isz b)
    have hS : 4 ≤ isz a + isz b := by rw [isz_eq, isz_eq]; omega
    have hbA : (Computability.encodeNat a.natAbs).length ≤ isz a := by
      rw [encodeNat_length, isz_eq]; omega
    have hbB : (Computability.encodeNat b.natAbs).length ≤ isz b := by
      rw [encodeNat_length, isz_eq]; omega
    have hga : gA.length ≤ isz a := le_trans hlenA hbA
    have hgb : gB.length ≤ isz b := le_trans hlenB hbB
    omega
  · rw [h2stk0, encs_cons]
  · intro k hk0
    by_cases hRA : k = sRA
    · subst hRA; exact h2RA
    by_cases hRB : k = sRB
    · subst hRB; exact h2RB
    by_cases hPA : k = sPA
    · subst hPA; exact h2PA
    by_cases hPB : k = sPB
    · subst hPB; exact h2PB
    exact binFrame s s2 s1 k h1oth h2oth hk0 hRA hRB hPA hPB

end Cmp

theorem cmpWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.UnOp main p (fun _ => True) (fun a => -a) (fun a => K * HvdH.isz a)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) max (fun a b => K * (HvdH.isz a + HvdH.isz b))) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) (fun a b => if a < b then 1 else 0) (fun a b => K * (HvdH.isz a + HvdH.isz b))) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) (fun a b => if a = b then 1 else 0) (fun a b => K * (HvdH.isz a + HvdH.isz b))) := by
  exact ⟨Cmp.negWord, Cmp.maxWord, Cmp.ltWord, Cmp.eqWord⟩

end Work.IntLib
