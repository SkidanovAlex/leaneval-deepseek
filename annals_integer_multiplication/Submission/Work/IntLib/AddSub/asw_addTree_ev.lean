import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.EvKit

namespace Work.IntLib.AddSub

open HvdH

/-- The leaf: set the output bit, push it, set the carry/borrow register. -/
theorem asw_leafEv {main : Cmd} (owOut owBw : Bool) (rT rbw : Reg) (out : Stk)
    (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (asw_leaf owOut owBw rT rbw out) ⟨g, X⟩
      ⟨Function.update (Function.update g rT (Glyph.bit owOut)) rbw (Glyph.bit owBw),
        Function.update X out (Glyph.bit owOut :: X out)⟩ 3 := by
  have h1 : Ev main (.set rT (.bit owOut)) ⟨g, X⟩
      ⟨Function.update g rT (.bit owOut), X⟩ 1 := ev_set' main rT (.bit owOut) g X
  have h2 : Ev main (.push out rT) ⟨Function.update g rT (.bit owOut), X⟩
      ⟨Function.update g rT (.bit owOut), Function.update X out (.bit owOut :: X out)⟩ 1 := by
    have h := ev_push' main out rT (Function.update g rT (.bit owOut)) X
    simpa using h
  have h3 : Ev main (.set rbw (.bit owBw))
      ⟨Function.update g rT (.bit owOut), Function.update X out (.bit owOut :: X out)⟩
      ⟨Function.update (Function.update g rT (.bit owOut)) rbw (.bit owBw),
        Function.update X out (.bit owOut :: X out)⟩ 1 :=
    ev_set' main rbw (.bit owBw) (Function.update g rT (.bit owOut))
      (Function.update X out (.bit owOut :: X out))
  have h12 : Ev main (.seq (.set rT (.bit owOut)) (.seq (.push out rT) (.set rbw (.bit owBw))))
      ⟨g, X⟩ ⟨Function.update (Function.update g rT (.bit owOut)) rbw (.bit owBw),
        Function.update X out (.bit owOut :: X out)⟩ (1 + (1 + 1)) :=
    Ev.seq h1 (Ev.seq h2 h3)
  simp only [asw_leaf, seqs]
  exact h12.mono (by omega)

/-- Innermost level of the tree: the `rc`-test selecting the leaf. -/
theorem asw_addTree_c {main : Cmd} {rc rT : Reg} {out : Stk} {x y c : Bool}
    {g : Reg → Glyph} {X : Stk → List Glyph} (hc : g rc = Glyph.bit c) :
    Ev main (.ite rc (.bit true)
        (asw_leaf (asw_addOutBit x y true) (asw_addCarry x y true) rT rc out)
        (asw_leaf (asw_addOutBit x y false) (asw_addCarry x y false) rT rc out)) ⟨g, X⟩
      ⟨Function.update (Function.update g rT (Glyph.bit (asw_addOutBit x y c))) rc
          (Glyph.bit (asw_addCarry x y c)),
        Function.update X out (Glyph.bit (asw_addOutBit x y c) :: X out)⟩ 4 := by
  cases c with
  | true => exact Ev.iteT hc (asw_leafEv (main := main) _ _ rT rc out g X)
  | false =>
      exact Ev.iteF (by show g rc ≠ Glyph.bit true; rw [hc]; decide)
        (asw_leafEv (main := main) _ _ rT rc out g X)

/-- Middle level: the `rY`-test. -/
theorem asw_addTree_b {main : Cmd} {rY rc rT : Reg} {out : Stk} {x y c : Bool}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hY : g rY = Glyph.bit y) (hc : g rc = Glyph.bit c) :
    Ev main (.ite rY (.bit true)
        (.ite rc (.bit true)
          (asw_leaf (asw_addOutBit x true true) (asw_addCarry x true true) rT rc out)
          (asw_leaf (asw_addOutBit x true false) (asw_addCarry x true false) rT rc out))
        (.ite rc (.bit true)
          (asw_leaf (asw_addOutBit x false true) (asw_addCarry x false true) rT rc out)
          (asw_leaf (asw_addOutBit x false false) (asw_addCarry x false false) rT rc out)))
      ⟨g, X⟩
      ⟨Function.update (Function.update g rT (Glyph.bit (asw_addOutBit x y c))) rc
          (Glyph.bit (asw_addCarry x y c)),
        Function.update X out (Glyph.bit (asw_addOutBit x y c) :: X out)⟩ 5 := by
  cases y with
  | true => exact Ev.iteT hY (asw_addTree_c (x := x) (y := true) (c := c) hc)
  | false =>
      exact Ev.iteF (by show g rY ≠ Glyph.bit true; rw [hY]; decide)
        (asw_addTree_c (x := x) (y := false) (c := c) hc)

theorem asw_addTree_ev {main : HvdH.Cmd} (rX rY rc rT : HvdH.Reg) (out : HvdH.Stk) (x y c : Bool)
    (s : HvdH.State)
    (hX : s.reg rX = HvdH.Glyph.bit x) (hY : s.reg rY = HvdH.Glyph.bit y)
    (hc : s.reg rc = HvdH.Glyph.bit c) :
    Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_addTree rX rY rc rT out) s
      ⟨Function.update (Function.update s.reg rT
            (HvdH.Glyph.bit (Work.IntLib.AddSub.asw_addOutBit x y c))) rc
          (HvdH.Glyph.bit (Work.IntLib.AddSub.asw_addCarry x y c)),
        Function.update s.stk out
          (HvdH.Glyph.bit (Work.IntLib.AddSub.asw_addOutBit x y c) :: s.stk out)⟩ 6 := by
  cases x with
  | true =>
      simp only [asw_addTree]
      exact Ev.iteT hX (asw_addTree_b (x := true) (y := y) (c := c) hY hc)
  | false =>
      simp only [asw_addTree]
      exact Ev.iteF (by rw [hX]; decide) (asw_addTree_b (x := false) (y := y) (c := c) hY hc)

end Work.IntLib.AddSub
