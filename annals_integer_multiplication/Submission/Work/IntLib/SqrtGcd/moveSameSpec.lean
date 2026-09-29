import Mathlib
import Submission.Work.IntLib.SqrtGcd.Basic
import Submission.Work.IntLib.SqrtGcd.SqrtProg

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH
open Work.IntLib.SG

/-! ## Local state bookkeeping for `SG.mSt` (private copies, to stay independent of
`gcdFinishEval`). -/

private theorem gMkNeEosP (i : Stk) : Glyph.mk i ≠ Glyph.eos := fun h => by cases h

private theorem memMapBitNeMkP (l : List Bool) (i : Stk) :
    ∀ g ∈ l.map Glyph.bit, g ≠ Glyph.mk i := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨b, -, rfl⟩ := hg
  exact fun h => by cases h

private theorem mStKP (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h : k ≠ d) : (SG.mSt k T d r gs below s).stk k = T :: below := by
  simp [SG.mSt, h]

private theorem mStDP (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) : (SG.mSt k T d r gs below s).stk d = gs.reverse ++ s.stk d := by
  simp [SG.mSt]

private theorem mStOP (k : Stk) (T : Glyph) (d j : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h1 : j ≠ k) (h2 : j ≠ d) : (SG.mSt k T d r gs below s).stk j = s.stk j := by
  simp [SG.mSt, h1, h2]

/-- `SG.moveSame src dst tmp r` unfolds into its two loops. -/
private theorem moveSame_def (src dst tmp : Stk) (r : Reg) :
    SG.moveSame src dst tmp r
      = .seq (SG.rLoop src (Glyph.mk src) (some tmp) r)
             (SG.rLoop tmp (Glyph.mk tmp) (some dst) r) := rfl

/-- `moveSame src dst tmp r` moves the bit region of `src` (least significant bit first, delimited
by the marker `mk src`, with raw content `bsrc` below) onto `dst`, keeping the order of the bits,
through the scratch stack `tmp` (whose raw content `btmp` below its own marker is restored).  The
cost is exactly `14 + 10 * |A|`: each of the two region loops pays `7 + 5 * |A|`. -/
theorem moveSameSpec (main : HvdH.Cmd) (src dst tmp : HvdH.Stk) (r : HvdH.Reg)
    (A : List Bool) (bsrc btmp : List HvdH.Glyph) (s : HvdH.State)
    (hsrc : s.stk src = A.map HvdH.Glyph.bit ++ HvdH.Glyph.mk src :: bsrc)
    (htmp : s.stk tmp = HvdH.Glyph.mk tmp :: btmp)
    (hds : dst ≠ src) (hdt : dst ≠ tmp) (hts : tmp ≠ src) :
    ∃ s' m, HvdH.Eval main (Work.IntLib.SG.moveSame src dst tmp r) s s' m ∧
      m = 14 + 10 * A.length ∧
      s'.stk src = HvdH.Glyph.mk src :: bsrc ∧
      s'.stk tmp = HvdH.Glyph.mk tmp :: btmp ∧
      s'.stk dst = A.map HvdH.Glyph.bit ++ s.stk dst ∧
      (∀ j : HvdH.Stk, j ≠ src → j ≠ tmp → j ≠ dst → s'.stk j = s.stk j) := by
  let s1 : State := SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s
  let s2 : State := SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1
  have h1 : Eval main (SG.rLoop src (Glyph.mk src) (some tmp) r) s s1
      (7 + (A.map Glyph.bit).length * 5) :=
    SG.mLoop_eval main src (Glyph.mk src) tmp r (gMkNeEosP src) hts (A.map Glyph.bit) bsrc s hsrc
      (memMapBitNeMkP A src)
  have ht1 : s1.stk tmp = A.reverse.map Glyph.bit ++ Glyph.mk tmp :: btmp := by
    show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk tmp
        = A.reverse.map Glyph.bit ++ Glyph.mk tmp :: btmp
    rw [mStDP, htmp, List.map_reverse]
  have h2 : Eval main (SG.rLoop tmp (Glyph.mk tmp) (some dst) r) s1 s2
      (7 + (A.reverse.map Glyph.bit).length * 5) :=
    SG.mLoop_eval main tmp (Glyph.mk tmp) dst r (gMkNeEosP tmp) hdt (A.reverse.map Glyph.bit) btmp
      s1 ht1 (memMapBitNeMkP A.reverse tmp)
  refine ⟨s2, (7 + (A.map Glyph.bit).length * 5) + (7 + (A.reverse.map Glyph.bit).length * 5),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveSame_def]; exact Eval.seq h1 h2
  · simp only [List.length_map, List.length_reverse]; ring
  · show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk src
        = Glyph.mk src :: bsrc
    rw [mStOP tmp (Glyph.mk tmp) dst src r (A.reverse.map Glyph.bit) btmp s1 hts.symm hds.symm]
    show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk src
        = Glyph.mk src :: bsrc
    rw [mStKP src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s hts.symm]
  · show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk tmp
        = Glyph.mk tmp :: btmp
    rw [mStKP tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1 hdt.symm]
  · have hdst1 : s1.stk dst = s.stk dst := by
      show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk dst = s.stk dst
      rw [mStOP src (Glyph.mk src) tmp dst r (A.map Glyph.bit) bsrc s hds hdt]
    show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk dst
        = A.map Glyph.bit ++ s.stk dst
    rw [mStDP tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1, List.map_reverse,
      List.reverse_reverse, hdst1]
  · intro j hjS hjT hjD
    show (SG.mSt tmp (Glyph.mk tmp) dst r (A.reverse.map Glyph.bit) btmp s1).stk j = s.stk j
    rw [mStOP tmp (Glyph.mk tmp) dst j r (A.reverse.map Glyph.bit) btmp s1 hjT hjD]
    show (SG.mSt src (Glyph.mk src) tmp r (A.map Glyph.bit) bsrc s).stk j = s.stk j
    rw [mStOP src (Glyph.mk src) tmp j r (A.map Glyph.bit) bsrc s hjS hjT]

end Work.IntLib.SqrtGcd
