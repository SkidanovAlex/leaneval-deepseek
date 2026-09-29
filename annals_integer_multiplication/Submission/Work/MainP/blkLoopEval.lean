import Mathlib
import Submission.Work.MainP.crtJoinDefs

/-!
# `blkLoopEval`: one round-counted copy of the interleaving phase

`Work.MainP.blkLoop cnt buf` (`Submission/Work/MainP/crtJoinDefs.lean`) copies as many glyphs as
there are `jtok` tokens on top of the count stack `cnt` from the buffer `buf` to the value stack 0:
`peek cnt 1` arms the test register, and every round of the loop pops one token, pops one glyph of
`buf` into register 1, pushes it on stack 0 and refreshes the test register.

This file proves `Work.MainP.blkLoopEval`: from a state with `s.stk cnt = jtok^m ++ c`
(`c.headD eos ≠ jtok`, so that the scan stops exactly after `m` rounds) and `s.stk buf = u ++ b` with
`m ≤ u.length`, the program terminates with cost `≤ 5 * m + 2`, pushing exactly the first `m` glyphs
of `u` (reversed) on stack 0, leaving `c` on `cnt` and `u.drop m ++ b` on `buf`, and touching no
other stack.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.MainP

open HvdH

/-! ## The loop body and one round -/

/-- The body of the loop of `blkLoop`: pop a token from the count stack `cnt` (register 1), pop one
glyph of the buffer `buf` (register 1), push it on stack 0, refresh the test register. -/
def blkBody (cnt buf : Stk) : Cmd :=
  .seq (.pop cnt 1) (.seq (.pop buf 1) (.seq (.push 0 1) (.peek cnt 1)))

theorem blkLoop_eq (cnt buf : Stk) :
    blkLoop cnt buf = .seq (.peek cnt 1) (.loop 1 jtok (blkBody cnt buf)) := rfl

/-- Canonical state after one round of the loop. -/
def blkStep (s : State) (cnt buf : Stk) : State :=
  State.tPeek (State.tPush (State.tPop (State.tPop s cnt 1) buf 1) 0 1) cnt 1

/-- One round of the loop costs 4 (two pops, one push, one peek). -/
theorem eval_blkBody (main : Cmd) (cnt buf : Stk) (s : State) :
    Eval main (blkBody cnt buf) s (blkStep s cnt buf) 4 := by
  unfold blkBody blkStep
  exact Work.Kernel.eval_seq (Work.Kernel.eval_pop main cnt 1 s)
    (Work.Kernel.eval_seq (Work.Kernel.eval_pop main buf 1 _)
      (Work.Kernel.eval_seq (Work.Kernel.eval_push main 0 1 _)
        (Work.Kernel.eval_peek main cnt 1 _)))

/-! ## Components of one round -/

theorem blkStep_stk_cnt (s : State) (cnt buf : Stk) (h0c : cnt ≠ 0) (hcb : cnt ≠ buf) :
    (blkStep s cnt buf).stk cnt = (s.stk cnt).tail := by
  simp [blkStep, State.tPop, State.tPush, State.tPeek, State.updStk, State.updReg,
    h0c, hcb, Ne.symm hcb]

theorem blkStep_stk_buf (s : State) (cnt buf : Stk) (h0b : buf ≠ 0) (hcb : cnt ≠ buf) :
    (blkStep s cnt buf).stk buf = (s.stk buf).tail := by
  simp [blkStep, State.tPop, State.tPush, State.tPeek, State.updStk, State.updReg,
    h0b, hcb, Ne.symm hcb]

theorem blkStep_stk0 (s : State) (cnt buf : Stk) (h0c : cnt ≠ 0) (h0b : buf ≠ 0)
    (hcb : cnt ≠ buf) :
    (blkStep s cnt buf).stk 0 = (s.stk buf).headD Glyph.eos :: s.stk 0 := by
  simp [blkStep, State.tPop, State.tPush, State.tPeek, State.updStk, State.updReg,
    h0c, h0b, hcb, Ne.symm hcb, Ne.symm h0b, Ne.symm h0c]

theorem blkStep_reg1 (s : State) (cnt buf : Stk) (h0c : cnt ≠ 0) (hcb : cnt ≠ buf) :
    (blkStep s cnt buf).reg 1 = ((s.stk cnt).tail).headD Glyph.eos := by
  simp [blkStep, State.tPop, State.tPush, State.tPeek, State.updStk, State.updReg,
    h0c, hcb, Ne.symm hcb]

theorem blkStep_stk_other (s : State) (cnt buf : Stk) (k : Stk) (h0 : k ≠ 0) (hc : k ≠ cnt)
    (hb : k ≠ buf) : (blkStep s cnt buf).stk k = s.stk k := by
  simp [blkStep, State.tPop, State.tPush, State.tPeek, State.updStk, State.updReg, h0, hc, hb]

/-! ## Elementary list facts -/

/-- Consuming one glyph: the first `k + 1` glyphs of `x :: u`, reversed, are the first `k` glyphs of
`u`, reversed, followed by `x`. -/
theorem take_succ_reverse_cons (u : List Glyph) (x : Glyph) (k : ℕ) (l : List Glyph) :
    ((x :: u).take (k + 1)).reverse ++ l = (u.take k).reverse ++ x :: l := by
  rw [List.take_succ_cons, List.reverse_cons]
  simp [List.append_assoc]

/-! ## The loop -/

/-- The loop of `blkLoop`, from the state armed by the leading `peek`: while there are tokens on
`cnt`, one glyph of `buf` is moved to stack 0. -/
theorem blkLoopCore (main : Cmd) (cnt buf : Stk) (h0c : cnt ≠ 0) (h0b : buf ≠ 0)
    (hcb : cnt ≠ buf) :
    ∀ (m : ℕ) (u : List Glyph) (s : State) (c b : List Glyph),
      m ≤ u.length → c.headD Glyph.eos ≠ jtok →
      s.stk cnt = List.replicate m jtok ++ c → s.stk buf = u ++ b →
      s.reg 1 = (s.stk cnt).headD Glyph.eos →
      ∃ (s' : State) (n : ℕ), n ≤ 5 * m + 1 ∧
        Eval main (.loop 1 jtok (blkBody cnt buf)) s s' n ∧
        s'.stk 0 = (u.take m).reverse ++ s.stk 0 ∧
        s'.stk cnt = c ∧
        s'.stk buf = u.drop m ++ b ∧
        (∀ k : Stk, k ≠ 0 → k ≠ cnt → k ≠ buf → s'.stk k = s.stk k) := by
  intro m
  induction m with
  | zero =>
    intro u s c b hm hc hcnt hbuf hreg
    have hhd : (s.stk cnt).headD Glyph.eos = c.headD Glyph.eos := by rw [hcnt]; simp
    have hne : s.reg 1 ≠ jtok := by rw [hreg, hhd]; exact hc
    refine ⟨s, 1, by simp, Work.Kernel.eval_loopF hne, ?_, ?_, ?_, ?_⟩
    · simp
    · rw [hcnt]; simp
    · simpa using hbuf
    · intro k _ _ _; rfl
  | succ k ih =>
    intro u s c b hm hc hcnt hbuf hreg
    cases u with
    | nil => simp at hm
    | cons x ur =>
      have hkur : k ≤ ur.length := by
        simp only [List.length_cons] at hm; omega
      have hcnt' : s.stk cnt = jtok :: (List.replicate k jtok ++ c) := by
        rw [hcnt, List.replicate_succ]
        rfl
      have hbuf' : s.stk buf = x :: (ur ++ b) := hbuf
      have hreg1 : s.reg 1 = jtok := by rw [hreg, hcnt']; rfl
      have hbody : Eval main (blkBody cnt buf) s (blkStep s cnt buf) 4 :=
        eval_blkBody main cnt buf s
      have h1cnt : (blkStep s cnt buf).stk cnt = List.replicate k jtok ++ c := by
        rw [blkStep_stk_cnt s cnt buf h0c hcb, hcnt', List.tail_cons]
      have h1buf : (blkStep s cnt buf).stk buf = ur ++ b := by
        rw [blkStep_stk_buf s cnt buf h0b hcb, hbuf', List.tail_cons]
      have h10 : (blkStep s cnt buf).stk 0 = x :: s.stk 0 := by
        rw [blkStep_stk0 s cnt buf h0c h0b hcb, hbuf']; rfl
      have h1reg : (blkStep s cnt buf).reg 1 = ((blkStep s cnt buf).stk cnt).headD Glyph.eos := by
        rw [blkStep_reg1 s cnt buf h0c hcb, hcnt', List.tail_cons, h1cnt]
      obtain ⟨s', n, hn, hev, h0', hcnt'', hbuf'', hoth⟩ :=
        ih ur (blkStep s cnt buf) c b hkur hc h1cnt h1buf h1reg
      refine ⟨s', 4 + n + 1, by omega, Eval.loopT hreg1 hbody hev, ?_, hcnt'', ?_,
        fun t ht0 htc htb => ?_⟩
      · rw [h0', h10, take_succ_reverse_cons]
      · rw [hbuf'', List.drop_succ_cons]
      · rw [hoth t ht0 htc htb, blkStep_stk_other s cnt buf t ht0 htc htb]

/-! ## The program -/

theorem blkLoopEval (main : HvdH.Cmd) (s : HvdH.State) (cnt buf : HvdH.Stk)
    (m : ℕ) (u c b : List HvdH.Glyph)
    (hm : m ≤ u.length) (hc : c.headD HvdH.Glyph.eos ≠ Work.MainP.jtok)
    (h0c : cnt ≠ 0) (h0b : buf ≠ 0) (hcb : cnt ≠ buf)
    (hcnt : s.stk cnt = List.replicate m Work.MainP.jtok ++ c)
    (hbuf : s.stk buf = u ++ b) :
    ∃ (s' : HvdH.State) (n : ℕ), n ≤ 5 * m + 2 ∧
      HvdH.Eval main (Work.MainP.blkLoop cnt buf) s s' n ∧
      s'.stk 0 = (u.take m).reverse ++ s.stk 0 ∧
      s'.stk cnt = c ∧
      s'.stk buf = u.drop m ++ b ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ cnt → k ≠ buf → s'.stk k = s.stk k) := by
  obtain ⟨s', n, hn, hev, h0, hcnt', hbuf', hoth⟩ :=
    blkLoopCore main cnt buf h0c h0b hcb m u (State.tPeek s cnt 1) c b hm hc
      (by simpa [State.tPeek, State.updReg] using hcnt)
      (by simpa [State.tPeek, State.updReg] using hbuf)
      (by simp [State.tPeek, State.updReg])
  refine ⟨s', 1 + n, by omega, ?_, ?_, hcnt', hbuf', ?_⟩
  · rw [blkLoop_eq]
    exact Work.Kernel.eval_seq (Work.Kernel.eval_peek main cnt 1 s) hev
  · simpa [State.tPeek, State.updReg] using h0
  · intro k hk0 hkc hkb
    rw [hoth k hk0 hkc hkb]
    simp [State.tPeek, State.updReg]

end Work.MainP
