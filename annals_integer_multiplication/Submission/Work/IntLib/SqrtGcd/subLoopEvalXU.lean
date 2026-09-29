import Mathlib
import Submission.Work.IntLib.SqrtGcd.SubProg
import Submission.Work.IntLib.SqrtGcd.SubDefs

/-!
# The ripple subtractor `SG.subLoop`, with the missing side condition `rX ≠ rU`

`Work.IntLib.SqrtGcd.subLoopEval` is *false* as stated — see
`Submission/Work/IntLib/SqrtGcd/subLoopEval_refute.lean`: the second `readBit` of a step
(`readBit b Tb rU rY`) clobbers the register `rX` holding the bit of `a` whenever `rU = rX`, so a
ripple step then computes its digit from `(false, y, c)` instead of `(x, y, c)`.

The present file proves the corrected statement, i.e. the same lemma with the additional hypothesis

```
(hXU : rX ≠ rU)
```

(`subLoopEvalXU` at the end).  The development follows the program:

* `Inv` is the invariant of the loop: the two bit regions of `a` and `b` (marker on top), the digits
  already pushed onto `out` (in push order, so `p.reverse` is what one sees on the stack), the frame
  conditions (`out`'s content below the digits and all other stacks), and the borrow in `rC`;
* `subDo_eval`: one read/subtract/emit step (`subDo`), cost `13`;
* `subBody_go` / `subBody_stop`: one iteration of the loop body, costs `≤ 17` and `5`;
* `subLoopAux`: the loop itself, by strong induction on `max as.length bs.length`,
  cost `≤ 18 * (max as.length bs.length + 1) + 1`;
* `subLoopEvalXU`: the whole word, cost `≤ 18 * (max as.length bs.length + 1) + 3` (hence the
  requested `40 * (… + 1) + 4`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SGX

open HvdH
open Work.IntLib.SG

/-- The invariant maintained by the ripple subtractor: the two remaining bit regions (least
significant bit first, marker on top), the digits pushed onto `out` so far (`p`, in the order in
which they were pushed, so the stack carries `p.reverse`), the content of `out` below the digits,
the frame condition on all other stacks, and the borrow. -/
def Inv (a b out : Stk) (Ta Tb : Glyph) (belowA belowB : List Glyph) (s₀ : State) (rC : Reg)
    (p as bs : List Bool) (c : Bool) (s : State) : Prop :=
  s.stk a = as.map Glyph.bit ++ Ta :: belowA ∧
  s.stk b = bs.map Glyph.bit ++ Tb :: belowB ∧
  s.stk out = p.reverse.map Glyph.bit ++ s₀.stk out ∧
  (∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → s.stk j = s₀.stk j) ∧
  s.reg rC = Glyph.bit c

/-! ## One step: `subDo` -/

/-- One ripple-subtraction step reads one bit of each region, pushes the digit of `x - y - c` on
`out`, leaves the new borrow in `rC` and sets `rF` to `gGo`.  Cost `13`.  It only uses the
hypotheses of `Work.IntLib.Sqrt.Gcd.readBit_eval`/`subStep_eval`, plus the new one `rX ≠ rU`. -/
theorem subDo_eval (main : Cmd) (a b out : Stk) (Ta Tb : Glyph)
    (rX rY rC rZ rT rU rF : Reg) (belowA belowB : List Glyph) (s₀ t : State)
    (hab : a ≠ b) (hoa : out ≠ a) (hob : out ≠ b)
    (hXY : rX ≠ rY) (hXU : rX ≠ rU)
    (hXc : rC ≠ rX) (hYc : rC ≠ rY) (hTc : rC ≠ rT) (hUc : rC ≠ rU) (hFc : rC ≠ rF)
    (hTa : Ta ≠ Glyph.eos) (hTb : Tb ≠ Glyph.eos)
    (hTab : ∀ c : Bool, Ta ≠ Glyph.bit c) (hTbb : ∀ c : Bool, Tb ≠ Glyph.bit c)
    (p as bs : List Bool) (c : Bool)
    (hstkA : t.stk a = as.map Glyph.bit ++ Ta :: belowA)
    (hstkB : t.stk b = bs.map Glyph.bit ++ Tb :: belowB)
    (hout : t.stk out = p.reverse.map Glyph.bit ++ s₀.stk out)
    (hfr : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t.stk j = s₀.stk j)
    (hrC : t.reg rC = Glyph.bit c) :
    ∃ t' m, Eval main (subDo a b Ta Tb out rX rY rC rZ rT rU rF) t t' m ∧ m = 13 ∧
      Inv a b out Ta Tb belowA belowB s₀ rC (p ++ [subBit (as.getD 0 false) (bs.getD 0 false) c])
        (as.drop 1) (bs.drop 1) (subBw (as.getD 0 false) (bs.getD 0 false) c) t' ∧
      t'.reg rF = gGo := by
  let t1 : State :=
    ⟨Function.update (Function.update t.reg rT ((as.map Glyph.bit ++ Ta :: belowA).headD Glyph.eos))
        rX (Glyph.bit (as.getD 0 false)),
      Function.update t.stk a ((as.drop 1).map Glyph.bit ++ Ta :: belowA)⟩
  have h1 : Eval main (readBit a Ta rT rX) t t1 3 :=
    readBit_eval main a Ta rT rX as belowA t hstkA hTa hTab
  let t2 : State :=
    ⟨Function.update (Function.update t1.reg rU ((bs.map Glyph.bit ++ Tb :: belowB).headD Glyph.eos))
        rY (Glyph.bit (bs.getD 0 false)),
      Function.update t1.stk b ((bs.drop 1).map Glyph.bit ++ Tb :: belowB)⟩
  have ht1b : t1.stk b = bs.map Glyph.bit ++ Tb :: belowB := by
    simp only [t1, Function.update_apply]
    split_ifs <;> simp_all
  have h2 : Eval main (readBit b Tb rU rY) t1 t2 3 :=
    readBit_eval main b Tb rU rY bs belowB t1 ht1b hTb hTbb
  have ht2X : t2.reg rX = Glyph.bit (as.getD 0 false) := by
    simp only [t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  have ht2Y : t2.reg rY = Glyph.bit (bs.getD 0 false) := by
    simp only [t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  have ht2C : t2.reg rC = Glyph.bit c := by
    simp only [t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  let t3 : State :=
    ⟨Function.update (Function.update t2.reg rZ
        (Glyph.bit (subBit (as.getD 0 false) (bs.getD 0 false) c)))
        rC (Glyph.bit (subBw (as.getD 0 false) (bs.getD 0 false) c)),
      Function.update t2.stk out
        (Glyph.bit (subBit (as.getD 0 false) (bs.getD 0 false) c) :: t2.stk out)⟩
  have h3 : Eval main (subStep rX rY rC rZ out) t2 t3 6 :=
    subStep_eval main rX rY rC rZ out (as.getD 0 false) (bs.getD 0 false) c t2 ht2X ht2Y ht2C
  let t4 : State := ⟨Function.update t3.reg rF gGo, t3.stk⟩
  have h4 : Eval main (.set rF gGo) t3 t4 1 := Eval.set rF gGo t3
  have ht4a : t4.stk a = (as.drop 1).map Glyph.bit ++ Ta :: belowA := by
    simp only [t4, t3, t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  have ht4b : t4.stk b = (bs.drop 1).map Glyph.bit ++ Tb :: belowB := by
    simp only [t4, t3, t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  have ht4o_raw : t4.stk out =
      Glyph.bit (subBit (as.getD 0 false) (bs.getD 0 false) c) :: t.stk out := by
    simp only [t4, t3, t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  have ht4o : t4.stk out =
      (p ++ [subBit (as.getD 0 false) (bs.getD 0 false) c]).reverse.map Glyph.bit
        ++ s₀.stk out := by
    rw [ht4o_raw, hout]
    simp [List.reverse_append]
  have ht4fr : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t4.stk j = s₀.stk j := by
    intro j hja hjb hjo
    simp only [t4, t3, t2, t1, Function.update_apply]
    split_ifs <;> simp_all
  have ht4C : t4.reg rC = Glyph.bit (subBw (as.getD 0 false) (bs.getD 0 false) c) := by
    simp only [t4, t3, Function.update_apply]
    split_ifs <;> simp_all
  have ht4F : t4.reg rF = gGo := by
    simp only [t4, Function.update_apply]
    split_ifs <;> simp_all
  exact ⟨t4, 13, Eval.seq h1 (Eval.seq h2 (Eval.seq h3 h4)), rfl,
    ⟨ht4a, ht4b, ht4o, ht4fr, ht4C⟩, ht4F⟩

/-! ## One iteration of the loop -/

/-- One iteration of the loop body when at least one region is still nonempty: cost `≤ 17`, one
digit emitted, one bit of each region consumed, the borrow updated and `rF` set to `gGo` (so the
loop continues). -/
theorem subBody_go (main : Cmd) (a b out : Stk) (Ta Tb : Glyph)
    (rX rY rC rZ rT rU rF : Reg) (belowA belowB : List Glyph) (s₀ t : State)
    (hab : a ≠ b) (hoa : out ≠ a) (hob : out ≠ b)
    (hXY : rX ≠ rY) (hXU : rX ≠ rU) (hTU : rT ≠ rU)
    (hXc : rC ≠ rX) (hYc : rC ≠ rY) (hTc : rC ≠ rT) (hUc : rC ≠ rU) (hFc : rC ≠ rF)
    (hTa : Ta ≠ Glyph.eos) (hTb : Tb ≠ Glyph.eos)
    (hTab : ∀ c : Bool, Ta ≠ Glyph.bit c) (hTbb : ∀ c : Bool, Tb ≠ Glyph.bit c)
    (p as bs : List Bool) (c : Bool)
    (hstkA : t.stk a = as.map Glyph.bit ++ Ta :: belowA)
    (hstkB : t.stk b = bs.map Glyph.bit ++ Tb :: belowB)
    (hout : t.stk out = p.reverse.map Glyph.bit ++ s₀.stk out)
    (hfr : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t.stk j = s₀.stk j)
    (hrC : t.reg rC = Glyph.bit c)
    (hne : as ≠ [] ∨ bs ≠ []) :
    ∃ t' m, Eval main (subBody a b Ta Tb out rX rY rC rZ rT rU rF) t t' m ∧ m ≤ 17 ∧
      Inv a b out Ta Tb belowA belowB s₀ rC (p ++ [subBit (as.headD false) (bs.headD false) c])
        as.tail bs.tail (subBw (as.headD false) (bs.headD false) c) t' ∧
      t'.reg rF = gGo := by
  rcases as with - | ⟨x, as'⟩ <;> rcases bs with - | ⟨y, bs'⟩
  · exact absurd hne (by simp)
  · -- `as = []`, `bs = y :: bs'`: the two peeks see `Ta` and `bit y`, the else-branch is taken
    have hA : t.stk a = Ta :: belowA := by simpa using hstkA
    have hB : t.stk b = Glyph.bit y :: (bs'.map Glyph.bit ++ Tb :: belowB) := by simpa using hstkB
    let t1 : State := ⟨Function.update t.reg rT ((t.stk a).headD Glyph.eos), t.stk⟩
    have e1 : Eval main (.peek a rT) t t1 1 := Eval.peek a rT t
    let t2 : State := ⟨Function.update t1.reg rU ((t1.stk b).headD Glyph.eos), t1.stk⟩
    have e2 : Eval main (.peek b rU) t1 t2 1 := Eval.peek b rU t1
    have ht2A : t2.stk a = Ta :: belowA := by
      simp only [t2, t1]; exact hA
    have ht2B : t2.stk b = Glyph.bit y :: (bs'.map Glyph.bit ++ Tb :: belowB) := by
      simp only [t2, t1]; exact hB
    have ht2O : t2.stk out = p.reverse.map Glyph.bit ++ s₀.stk out := by
      simp only [t2, t1]; exact hout
    have ht2FR : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t2.stk j = s₀.stk j := by
      intro j hja hjb hjo
      simp only [t2, t1]; exact hfr j hja hjb hjo
    have ht2C : t2.reg rC = Glyph.bit c := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    have ht2rT : t2.reg rT = Ta := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    have ht2rU : t2.reg rU = Glyph.bit y := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    obtain ⟨t3, m3, hev3, hm3, hInv3, hrF3⟩ :=
      subDo_eval main a b out Ta Tb rX rY rC rZ rT rU rF belowA belowB s₀ t2
        hab hoa hob hXY hXU hXc hYc hTc hUc hFc hTa hTb hTab hTbb p [] (y :: bs') c
        (by simpa using ht2A) (by simpa using ht2B) ht2O ht2FR ht2C
    have hneTb : ¬ (t2.reg rU = Tb) := by
      rw [ht2rU]; exact fun h => hTbb y h.symm
    have hinner : Eval main (.ite rU Tb (.set rF gStop)
        (subDo a b Ta Tb out rX rY rC rZ rT rU rF)) t2 t3 (m3 + 1) :=
      Eval.iteF hneTb hev3
    have houter : Eval main
        (.ite rT Ta (.ite rU Tb (.set rF gStop) (subDo a b Ta Tb out rX rY rC rZ rT rU rF))
          (subDo a b Ta Tb out rX rY rC rZ rT rU rF)) t2 t3 (m3 + 2) :=
      Eval.iteT ht2rT hinner
    have hbody : Eval main (subBody a b Ta Tb out rX rY rC rZ rT rU rF) t t3
        (1 + (1 + (m3 + 2))) := Eval.seq e1 (Eval.seq e2 houter)
    refine ⟨t3, 1 + (1 + (m3 + 2)), hbody, by omega, ?_, hrF3⟩
    simpa using hInv3
  · -- `as = x :: as'`, `bs = []`: the first peek sees `bit x`, so the else-branch is taken
    have hA : t.stk a = Glyph.bit x :: (as'.map Glyph.bit ++ Ta :: belowA) := by simpa using hstkA
    have hB : t.stk b = Tb :: belowB := by simpa using hstkB
    let t1 : State := ⟨Function.update t.reg rT ((t.stk a).headD Glyph.eos), t.stk⟩
    have e1 : Eval main (.peek a rT) t t1 1 := Eval.peek a rT t
    let t2 : State := ⟨Function.update t1.reg rU ((t1.stk b).headD Glyph.eos), t1.stk⟩
    have e2 : Eval main (.peek b rU) t1 t2 1 := Eval.peek b rU t1
    have ht2A : t2.stk a = Glyph.bit x :: (as'.map Glyph.bit ++ Ta :: belowA) := by
      simp only [t2, t1]; exact hA
    have ht2B : t2.stk b = Tb :: belowB := by
      simp only [t2, t1]; exact hB
    have ht2O : t2.stk out = p.reverse.map Glyph.bit ++ s₀.stk out := by
      simp only [t2, t1]; exact hout
    have ht2FR : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t2.stk j = s₀.stk j := by
      intro j hja hjb hjo
      simp only [t2, t1]; exact hfr j hja hjb hjo
    have ht2C : t2.reg rC = Glyph.bit c := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    have ht2rTx : t2.reg rT = Glyph.bit x := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    have ht2rT : ¬ (t2.reg rT = Ta) := by
      rw [ht2rTx]
      exact fun h => hTab x h.symm
    obtain ⟨t3, m3, hev3, hm3, hInv3, hrF3⟩ :=
      subDo_eval main a b out Ta Tb rX rY rC rZ rT rU rF belowA belowB s₀ t2
        hab hoa hob hXY hXU hXc hYc hTc hUc hFc hTa hTb hTab hTbb p (x :: as') [] c
        (by simpa using ht2A) (by simpa using ht2B) ht2O ht2FR ht2C
    have hbody : Eval main (subBody a b Ta Tb out rX rY rC rZ rT rU rF) t t3
        (1 + (1 + (m3 + 1))) := Eval.seq e1 (Eval.seq e2 (Eval.iteF ht2rT hev3))
    refine ⟨t3, 1 + (1 + (m3 + 1)), hbody, by omega, ?_, hrF3⟩
    simpa using hInv3
  · -- `as = x :: as'`, `bs = y :: bs'`
    have hA : t.stk a = Glyph.bit x :: (as'.map Glyph.bit ++ Ta :: belowA) := by simpa using hstkA
    have hB : t.stk b = Glyph.bit y :: (bs'.map Glyph.bit ++ Tb :: belowB) := by simpa using hstkB
    let t1 : State := ⟨Function.update t.reg rT ((t.stk a).headD Glyph.eos), t.stk⟩
    have e1 : Eval main (.peek a rT) t t1 1 := Eval.peek a rT t
    let t2 : State := ⟨Function.update t1.reg rU ((t1.stk b).headD Glyph.eos), t1.stk⟩
    have e2 : Eval main (.peek b rU) t1 t2 1 := Eval.peek b rU t1
    have ht2A : t2.stk a = Glyph.bit x :: (as'.map Glyph.bit ++ Ta :: belowA) := by
      simp only [t2, t1]; exact hA
    have ht2B : t2.stk b = Glyph.bit y :: (bs'.map Glyph.bit ++ Tb :: belowB) := by
      simp only [t2, t1]; exact hB
    have ht2O : t2.stk out = p.reverse.map Glyph.bit ++ s₀.stk out := by
      simp only [t2, t1]; exact hout
    have ht2FR : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t2.stk j = s₀.stk j := by
      intro j hja hjb hjo
      simp only [t2, t1]; exact hfr j hja hjb hjo
    have ht2C : t2.reg rC = Glyph.bit c := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    have ht2rTx : t2.reg rT = Glyph.bit x := by
      simp only [t2, t1, Function.update_apply]
      simp_all
    have ht2rT : ¬ (t2.reg rT = Ta) := by
      rw [ht2rTx]
      exact fun h => hTab x h.symm
    obtain ⟨t3, m3, hev3, hm3, hInv3, hrF3⟩ :=
      subDo_eval main a b out Ta Tb rX rY rC rZ rT rU rF belowA belowB s₀ t2
        hab hoa hob hXY hXU hXc hYc hTc hUc hFc hTa hTb hTab hTbb p (x :: as') (y :: bs') c
        (by simpa using ht2A) (by simpa using ht2B) ht2O ht2FR ht2C
    have hbody : Eval main (subBody a b Ta Tb out rX rY rC rZ rT rU rF) t t3
        (1 + (1 + (m3 + 1))) := Eval.seq e1 (Eval.seq e2 (Eval.iteF ht2rT hev3))
    refine ⟨t3, 1 + (1 + (m3 + 1)), hbody, by omega, ?_, hrF3⟩
    simpa using hInv3

/-- One iteration of the loop body when both regions are exhausted: cost `5`, nothing is pushed,
the borrow is unchanged and `rF` is set to `gStop` (the loop ends). -/
theorem subBody_stop (main : Cmd) (a b out : Stk) (Ta Tb : Glyph)
    (rX rY rC rZ rT rU rF : Reg) (belowA belowB : List Glyph) (t : State)
    (hTU : rT ≠ rU)
    (hXc : rC ≠ rX) (hYc : rC ≠ rY) (hTc : rC ≠ rT) (hUc : rC ≠ rU) (hFc : rC ≠ rF)
    (hstkA : t.stk a = Ta :: belowA) (hstkB : t.stk b = Tb :: belowB) :
    ∃ t' m, Eval main (subBody a b Ta Tb out rX rY rC rZ rT rU rF) t t' m ∧ m = 5 ∧
      t'.stk a = t.stk a ∧ t'.stk b = t.stk b ∧ t'.stk out = t.stk out ∧
      (∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t'.stk j = t.stk j) ∧
      t'.reg rC = t.reg rC ∧ t'.reg rF = gStop := by
  let t1 : State := ⟨Function.update t.reg rT ((t.stk a).headD Glyph.eos), t.stk⟩
  have e1 : Eval main (.peek a rT) t t1 1 := Eval.peek a rT t
  let t2 : State := ⟨Function.update t1.reg rU ((t1.stk b).headD Glyph.eos), t1.stk⟩
  have e2 : Eval main (.peek b rU) t1 t2 1 := Eval.peek b rU t1
  have ht1rT : t1.reg rT = Ta := by
    simp only [t1, Function.update_apply]
    simp_all
  have ht2rU : t2.reg rU = Tb := by
    simp only [t2, t1, Function.update_apply]
    simp_all
  let t3 : State := ⟨Function.update t2.reg rF gStop, t2.stk⟩
  have e3 : Eval main (.set rF gStop) t2 t3 1 := Eval.set rF gStop t2
  have ht2rT : t2.reg rT = Ta := by
    simp only [t2, t1, Function.update_apply]
    simp_all
  have hinner : Eval main (.ite rU Tb (.set rF gStop)
      (subDo a b Ta Tb out rX rY rC rZ rT rU rF)) t2 t3 2 := Eval.iteT ht2rU e3
  have houter : Eval main
      (.ite rT Ta (.ite rU Tb (.set rF gStop) (subDo a b Ta Tb out rX rY rC rZ rT rU rF))
        (subDo a b Ta Tb out rX rY rC rZ rT rU rF)) t2 t3 3 :=
    Eval.iteT ht2rT hinner
  have hbody : Eval main (subBody a b Ta Tb out rX rY rC rZ rT rU rF) t t3 5 :=
    Eval.seq e1 (Eval.seq e2 houter)
  have ht3a : t3.stk a = t.stk a := by simp [t3, t2, t1]
  have ht3b : t3.stk b = t.stk b := by simp [t3, t2, t1]
  have ht3o : t3.stk out = t.stk out := by simp [t3, t2, t1]
  have ht3fr : ∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → t3.stk j = t.stk j := by
    intro j _ _ _
    simp [t3, t2, t1]
  have ht3C : t3.reg rC = t.reg rC := by
    simp only [t3, t2, t1, Function.update_apply]
    simp_all
  have ht3F : t3.reg rF = gStop := by
    simp only [t3, Function.update_apply]
    simp_all
  exact ⟨t3, 5, hbody, rfl, ht3a, ht3b, ht3o, ht3fr, ht3C, ht3F⟩

/-! ## Arithmetic helpers for the loop -/

theorem max_succ_succ (a b : ℕ) : max (a + 1) (b + 1) = max a b + 1 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.succ_le_succ h)]
  · rw [max_eq_left h, max_eq_left (Nat.succ_le_succ h)]

/-- The number of loop iterations drops by one when both regions lose the bit just processed. -/
theorem max_tail_succ (as bs : List Bool) (h : as ≠ [] ∨ bs ≠ []) :
    max as.tail.length bs.tail.length + 1 = max as.length bs.length := by
  rcases as with - | ⟨x, as'⟩ <;> rcases bs with - | ⟨y, bs'⟩
  · simp at h
  · simp only [List.tail_cons, List.length_cons, List.tail_nil, List.length_nil]
    rw [Nat.max_eq_right (Nat.zero_le _), Nat.max_eq_right (Nat.zero_le _)]
  · simp only [List.tail_cons, List.length_cons, List.tail_nil, List.length_nil]
    rw [Nat.max_eq_left (Nat.zero_le _), Nat.max_eq_left (Nat.zero_le _)]
  · simp only [List.tail_cons, List.length_cons]
    rw [max_succ_succ]

/-- Pushing one more digit onto the output stack, written on the reversed (= stack order) list. -/
theorem rev_map_append_singleton (p q : List Bool) (d : Bool) :
    (((p ++ [d]) ++ q).reverse).map Glyph.bit = ((p ++ (d :: q)).reverse).map Glyph.bit := by
  have h : (p ++ [d]) ++ q = p ++ (d :: q) := by simp
  rw [h]

/-! ## The loop -/

/-- The ripple subtractor loop: cost `≤ 18 * (max as.length bs.length + 1) + 1`, and it consumes
the two regions completely, having emitted the digits of `subDigits`. -/
theorem subLoopAux (main : Cmd) (a b out : Stk) (Ta Tb : Glyph)
    (rX rY rC rZ rT rU rF : Reg) (belowA belowB : List Glyph) (s₀ t : State)
    (hab : a ≠ b) (hoa : out ≠ a) (hob : out ≠ b)
    (hXY : rX ≠ rY) (hXU : rX ≠ rU) (hTU : rT ≠ rU)
    (hXc : rC ≠ rX) (hYc : rC ≠ rY) (hTc : rC ≠ rT) (hUc : rC ≠ rU) (hFc : rC ≠ rF)
    (hTa : Ta ≠ Glyph.eos) (hTb : Tb ≠ Glyph.eos)
    (hTab : ∀ c : Bool, Ta ≠ Glyph.bit c) (hTbb : ∀ c : Bool, Tb ≠ Glyph.bit c)
    (p as bs : List Bool) (c : Bool)
    (hInv : Inv a b out Ta Tb belowA belowB s₀ rC p as bs c t) (hrF : t.reg rF = gGo) :
    ∃ t' m, Eval main (.loop rF gGo (subBody a b Ta Tb out rX rY rC rZ rT rU rF)) t t' m ∧
      m ≤ 18 * (max as.length bs.length + 1) + 1 ∧
      Inv a b out Ta Tb belowA belowB s₀ rC
        (p ++ (SG.subDigits (max as.length bs.length) as bs c).2) [] []
        (SG.subDigits (max as.length bs.length) as bs c).1 t' := by
  have key : ∀ M, ∀ (as bs : List Bool), max as.length bs.length = M →
      ∀ (p : List Bool) (c : Bool) (t : State),
        Inv a b out Ta Tb belowA belowB s₀ rC p as bs c t → t.reg rF = gGo →
        ∃ t' m, Eval main (.loop rF gGo (subBody a b Ta Tb out rX rY rC rZ rT rU rF)) t t' m ∧
          m ≤ 18 * (max as.length bs.length + 1) + 1 ∧
          Inv a b out Ta Tb belowA belowB s₀ rC
            (p ++ (SG.subDigits (max as.length bs.length) as bs c).2) [] []
            (SG.subDigits (max as.length bs.length) as bs c).1 t' := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
      intro as bs hM p c t hInv hrF
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · -- both regions are already exhausted
        subst hM0
        have has : as = [] := by
          have hle : as.length ≤ max as.length bs.length := Nat.le_max_left _ _
          rw [hM] at hle
          have h0 : as.length = 0 := Nat.le_zero.mp hle
          cases as with
          | nil => rfl
          | cons x xs => simp at h0
        have hbs : bs = [] := by
          have hle : bs.length ≤ max as.length bs.length := Nat.le_max_right _ _
          rw [hM] at hle
          have h0 : bs.length = 0 := Nat.le_zero.mp hle
          cases bs with
          | nil => rfl
          | cons y ys => simp at h0
        subst has
        subst hbs
        obtain ⟨hA, hB, hO, hFR, hC⟩ := hInv
        obtain ⟨t1, m1, hev1, hm1, ha1, hb1, ho1, hfr1, hrc1, hrf1⟩ :=
          subBody_stop main a b out Ta Tb rX rY rC rZ rT rU rF belowA belowB t
            hTU hXc hYc hTc hUc hFc (by simpa using hA) (by simpa using hB)
        have hneF : ¬ (t1.reg rF = gGo) := by
          rw [hrf1]
          decide
        have hloop : Eval main (.loop rF gGo (subBody a b Ta Tb out rX rY rC rZ rT rU rF)) t t1
            (m1 + 1 + 1) := Eval.loopT hrF hev1 (Eval.loopF hneF)
        refine ⟨t1, m1 + 1 + 1, hloop, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hm1]
          decide
        · simpa using ha1.trans hA
        · simpa using hb1.trans hB
        · rw [ho1, hO]
          simp [SG.subDigits]
        · intro j h1 h2 h3
          rw [hfr1 j h1 h2 h3]
          exact hFR j h1 h2 h3
        · rw [hrc1, hC]
          simp [SG.subDigits]
      · -- at least one region is nonempty: one more iteration, then the induction hypothesis
        have hne : as ≠ [] ∨ bs ≠ [] := by
          rcases as with - | ⟨x, as'⟩
          · rcases bs with - | ⟨y, bs'⟩
            · simp only [List.length_nil] at hM
              omega
            · exact Or.inr (by simp)
          · exact Or.inl (by simp)
        obtain ⟨hA, hB, hO, hFR, hC⟩ := hInv
        obtain ⟨t1, m1, hev1, hm1, hInv1, hrF1⟩ :=
          subBody_go main a b out Ta Tb rX rY rC rZ rT rU rF belowA belowB s₀ t
            hab hoa hob hXY hXU hTU hXc hYc hTc hUc hFc hTa hTb hTab hTbb p as bs c
            hA hB hO hFR hC hne
        have hMmax : max as.length bs.length = max as.tail.length bs.tail.length + 1 := by
          have h1 := max_tail_succ as bs hne
          rw [hM] at h1
          omega
        have hlt : max as.tail.length bs.tail.length < M := by omega
        obtain ⟨t2, m2, hev2, hm2, hInv2⟩ :=
          ih (max as.tail.length bs.tail.length) hlt as.tail bs.tail rfl
            (p ++ [subBit (as.headD false) (bs.headD false) c])
            (subBw (as.headD false) (bs.headD false) c) t1 hInv1 hrF1
        have hloop : Eval main (.loop rF gGo (subBody a b Ta Tb out rX rY rC rZ rT rU rF)) t t2
            (m1 + m2 + 1) := Eval.loopT hrF hev1 hev2
        have hsd : SG.subDigits (max as.length bs.length) as bs c
            = ((SG.subDigits (max as.tail.length bs.tail.length) as.tail bs.tail
                  (subBw (as.headD false) (bs.headD false) c)).1,
               subBit (as.headD false) (bs.headD false) c ::
                 (SG.subDigits (max as.tail.length bs.tail.length) as.tail bs.tail
                  (subBw (as.headD false) (bs.headD false) c)).2) := by
          rw [hMmax]
          simp only [SG.subDigits]
        refine ⟨t2, m1 + m2 + 1, hloop, ?_, ?_⟩
        · rw [hMmax]
          omega
        · rw [hsd]
          refine ⟨hInv2.1, hInv2.2.1, ?_, hInv2.2.2.2.1, hInv2.2.2.2.2⟩
          rw [hInv2.2.2.1, rev_map_append_singleton]
  exact key (max as.length bs.length) as bs rfl p c t hInv hrF

/-! ## The word -/

/-- **Ripple subtraction, corrected.**  Same statement as `Work.IntLib.SqrtGcd.subLoopEval`, with
the additional hypothesis `rX ≠ rU` (the temporary register of the second `readBit` must differ from
the register holding the first operand's bit, otherwise it is overwritten). -/
theorem subLoopEvalXU (main : Cmd) (a b : Stk) (Ta Tb : Glyph) (out : Stk)
    (rX rY rC rZ rT rU rF : Reg) (as bs : List Bool) (belowA belowB : List Glyph)
    (s : State) (hab : a ≠ b) (hoa : out ≠ a) (hob : out ≠ b)
    (hXY : rX ≠ rY) (hXU : rX ≠ rU) (hTU : rT ≠ rU)
    (hXc : rC ≠ rX) (hYc : rC ≠ rY) (hTc : rC ≠ rT) (hUc : rC ≠ rU) (hFc : rC ≠ rF)
    (hTa : Ta ≠ Glyph.eos) (hTb : Tb ≠ Glyph.eos)
    (hTab : ∀ c : Bool, Ta ≠ Glyph.bit c) (hTbb : ∀ c : Bool, Tb ≠ Glyph.bit c)
    (hstkA : s.stk a = as.map Glyph.bit ++ Ta :: belowA)
    (hstkB : s.stk b = bs.map Glyph.bit ++ Tb :: belowB) :
    ∃ s' m, Eval main (subLoop a b Ta Tb out rX rY rC rZ rT rU rF) s s' m ∧
      m ≤ 40 * (max as.length bs.length + 1) + 4 ∧
      s'.stk a = Ta :: belowA ∧ s'.stk b = Tb :: belowB ∧
      s'.stk out = ((SG.subDigits (max as.length bs.length) as bs false).2.reverse).map Glyph.bit
          ++ s.stk out ∧
      s'.reg rC = Glyph.bit (SG.subDigits (max as.length bs.length) as bs false).1 ∧
      (∀ j : Stk, j ≠ a → j ≠ b → j ≠ out → s'.stk j = s.stk j) := by
  let t1 : State := ⟨Function.update s.reg rC (Glyph.bit false), s.stk⟩
  have e1 : Eval main (.set rC (Glyph.bit false)) s t1 1 := Eval.set rC (Glyph.bit false) s
  let t2 : State := ⟨Function.update t1.reg rF gGo, t1.stk⟩
  have e2 : Eval main (.set rF gGo) t1 t2 1 := Eval.set rF gGo t1
  have ht2rC : t2.reg rC = Glyph.bit false := by
    simp only [t2, t1, Function.update_apply]
    simp_all
  have ht2rF : t2.reg rF = gGo := by
    simp only [t2, Function.update_apply]
    simp_all
  have hInv2 : Inv a b out Ta Tb belowA belowB s rC [] as bs false t2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [t2, t1]; exact hstkA
    · simp only [t2, t1]; exact hstkB
    · simp only [t2, t1]
      simp
    · intro j _ _ _
      simp only [t2, t1]
    · exact ht2rC
  obtain ⟨t3, m3, hev3, hm3, hInv3⟩ :=
    subLoopAux main a b out Ta Tb rX rY rC rZ rT rU rF belowA belowB s t2
      hab hoa hob hXY hXU hTU hXc hYc hTc hUc hFc hTa hTb hTab hTbb [] as bs false hInv2 ht2rF
  obtain ⟨hA, hB, hO, hFR, hC⟩ := hInv3
  have hbody : Eval main (subLoop a b Ta Tb out rX rY rC rZ rT rU rF) s t3 (1 + (1 + m3)) :=
    Eval.seq e1 (Eval.seq e2 hev3)
  refine ⟨t3, 1 + (1 + m3), hbody, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h2 : m3 ≤ 18 * (max as.length bs.length + 1) + 1 := hm3
    omega
  · simpa using hA
  · simpa using hB
  · simpa using hO
  · simpa using hC
  · intro j h1 h2 h3
    exact hFR j h1 h2 h3

end SGX
end Work.IntLib
