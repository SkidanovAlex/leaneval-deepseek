import Submission.Work.IntLib.SqrtGcd.Basic
import Submission.Work.IntLib.SqrtGcd.SubDefs

/-!
# The ripple subtractor (program layer)

`subLoop a b Ta Tb out ...` pops the two bit regions of stacks `a` and `b` (delimited by the
markers `Ta`, `Tb`, least significant bit first) and pushes the digits of the ripple subtraction
on stack `out` (most significant last, i.e. the *reverse* of the least-significant-first digit
list of `subDigits`).  A register `rC` carries the borrow.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

/-- Emit the digit `d` on `out` and set the borrow register `rC` to `bw`. -/
def leaf (rZ rC : Reg) (d bw : Bool) (out : Stk) : Cmd :=
  .seq (.set rZ (.bit d)) (.seq (.push out rZ) (.set rC (.bit bw)))

/-- One ripple-subtraction step: `rX`, `rY`, `rC` hold the bits `x`, `y` and the borrow `c`; the
digit of `x - y - c` is pushed on `out` and the new borrow is left in `rC`. -/
def subStep (rX rY rC rZ : Reg) (out : Stk) : Cmd :=
  .ite rX (.bit true)
    (.ite rY (.bit true)
      (.ite rC (.bit true) (leaf rZ rC true true out) (leaf rZ rC false false out))
      (.ite rC (.bit true) (leaf rZ rC false false out) (leaf rZ rC true false out)))
    (.ite rY (.bit true)
      (.ite rC (.bit true) (leaf rZ rC false true out) (leaf rZ rC true true out))
      (.ite rC (.bit true) (leaf rZ rC true true out) (leaf rZ rC false false out)))

/-- Read one bit of the region of stack `k`: if the top glyph is the marker `T`, leave `false` in
`rR` without popping, otherwise pop the top bit into `rR`. -/
def readBit (k : Stk) (T : Glyph) (rT rR : Reg) : Cmd :=
  .seq (.peek k rT) (.ite rT T (.set rR (.bit false)) (.pop k rR))

theorem leaf_eval (main : Cmd) (rZ rC : Reg) (d bw : Bool) (out : Stk) (t : State) :
    Eval main (leaf rZ rC d bw out) t
      ⟨Function.update (Function.update t.reg rZ (Glyph.bit d)) rC (Glyph.bit bw),
        Function.update t.stk out (Glyph.bit d :: t.stk out)⟩ 3 := by
  have e1 : Eval main (.set rZ (Glyph.bit d)) t
      ⟨Function.update t.reg rZ (Glyph.bit d), t.stk⟩ 1 := Eval.set rZ (Glyph.bit d) t
  have e2 : Eval main (.push out rZ) ⟨Function.update t.reg rZ (Glyph.bit d), t.stk⟩
      ⟨Function.update t.reg rZ (Glyph.bit d),
        Function.update t.stk out (Glyph.bit d :: t.stk out)⟩ 1 := by
    have h := Eval.push (main := main) out rZ ⟨Function.update t.reg rZ (Glyph.bit d), t.stk⟩
    simpa [Function.update_apply] using h
  have e3 : Eval main (.set rC (Glyph.bit bw))
      ⟨Function.update t.reg rZ (Glyph.bit d),
        Function.update t.stk out (Glyph.bit d :: t.stk out)⟩
      ⟨Function.update (Function.update t.reg rZ (Glyph.bit d)) rC (Glyph.bit bw),
        Function.update t.stk out (Glyph.bit d :: t.stk out)⟩ 1 :=
    Eval.set rC (Glyph.bit bw) _
  exact Eval.seq e1 (Eval.seq e2 e3)

theorem ne_bit_true_of_eq_false {g : Glyph} (h : g = Glyph.bit false) : g ≠ Glyph.bit true := by
  rw [h]; intro hc; exact Bool.noConfusion (Glyph.bit.inj hc)

theorem ne_bit_false_of_eq_true {g : Glyph} (h : g = Glyph.bit true) : g ≠ Glyph.bit false := by
  rw [h]; intro hc; exact Bool.noConfusion (Glyph.bit.inj hc)

theorem subStep_eval (main : Cmd) (rX rY rC rZ : Reg) (out : Stk) (x y c : Bool) (t : State)
    (hX : t.reg rX = Glyph.bit x) (hY : t.reg rY = Glyph.bit y) (hC : t.reg rC = Glyph.bit c) :
    Eval main (subStep rX rY rC rZ out) t
      ⟨Function.update (Function.update t.reg rZ (Glyph.bit (subBit x y c)))
          rC (Glyph.bit (subBw x y c)),
        Function.update t.stk out (Glyph.bit (subBit x y c) :: t.stk out)⟩ 6 := by
  cases x <;> cases y <;> cases c <;>
    first
      | exact Eval.iteT hX (Eval.iteT hY (Eval.iteT hC (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteT hX (Eval.iteT hY (Eval.iteF (ne_bit_true_of_eq_false hC) (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteT hX (Eval.iteF (ne_bit_true_of_eq_false hY) (Eval.iteT hC (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteT hX (Eval.iteF (ne_bit_true_of_eq_false hY) (Eval.iteF (ne_bit_true_of_eq_false hC) (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteF (ne_bit_true_of_eq_false hX) (Eval.iteT hY (Eval.iteT hC (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteF (ne_bit_true_of_eq_false hX) (Eval.iteT hY (Eval.iteF (ne_bit_true_of_eq_false hC) (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteF (ne_bit_true_of_eq_false hX) (Eval.iteF (ne_bit_true_of_eq_false hY) (Eval.iteT hC (leaf_eval main rZ rC _ _ out t)))
      | exact Eval.iteF (ne_bit_true_of_eq_false hX) (Eval.iteF (ne_bit_true_of_eq_false hY) (Eval.iteF (ne_bit_true_of_eq_false hC) (leaf_eval main rZ rC _ _ out t)))

theorem readBit_eval (main : Cmd) (k : Stk) (T : Glyph) (rT rR : Reg) (gs : List Bool)
    (below : List Glyph) (t : State) (hstk : t.stk k = gs.map Glyph.bit ++ T :: below)
    (hT : T ≠ Glyph.eos) (hTb : ∀ b : Bool, T ≠ Glyph.bit b) :
    Eval main (readBit k T rT rR) t
      ⟨Function.update (Function.update t.reg rT ((gs.map Glyph.bit ++ T :: below).headD Glyph.eos))
          rR (Glyph.bit (gs.getD 0 false)),
        Function.update t.stk k ((gs.drop 1).map Glyph.bit ++ T :: below)⟩ 3 := by
  rcases gs with - | ⟨g, gs⟩
  · -- empty region: the marker is on top, `rR` is set to `false`
    have hstk' : t.stk k = T :: below := by simpa using hstk
    have e1 : Eval main (.peek k rT) t ⟨Function.update t.reg rT T, t.stk⟩ 1 := by
      have h := Eval.peek (main := main) k rT t
      rw [hstk'] at h
      simpa [List.headD_cons] using h
    have hr : (⟨Function.update t.reg rT T, t.stk⟩ : State).reg rT = T := by
      simp [Function.update_apply]
    have e2 : Eval main (.set rR (.bit false)) ⟨Function.update t.reg rT T, t.stk⟩
        ⟨Function.update (Function.update t.reg rT T) rR (Glyph.bit false), t.stk⟩ 1 :=
      Eval.set (main := main) rR (Glyph.bit false) _
    have hmain : Eval main (readBit k T rT rR) t
        ⟨Function.update (Function.update t.reg rT T) rR (Glyph.bit false), t.stk⟩ 3 :=
      Eval.seq e1 (Eval.iteT hr e2)
    have hgoal : (⟨Function.update (Function.update t.reg rT T) rR (Glyph.bit false), t.stk⟩ : State)
        = ⟨Function.update (Function.update t.reg rT
              ((([] : List Bool).map Glyph.bit ++ T :: below).headD Glyph.eos)) rR
              (Glyph.bit (([] : List Bool).getD 0 false)),
            Function.update t.stk k ((([] : List Bool).drop 1).map Glyph.bit ++ T :: below)⟩ := by
      apply State.ext'
      · intro q
        simp only [List.map_nil, List.nil_append, List.drop_nil, List.headD_cons, List.getD_nil,
          Function.update_apply]
      · intro q
        simp only [List.map_nil, List.nil_append, List.drop_nil, Function.update_apply]
        by_cases h2 : q = k
        · subst h2; simp [hstk']
        · simp [h2]
    rw [hgoal] at hmain
    exact hmain
  · -- nonempty region: the leading bit is popped into `rR`
    have hstk' : t.stk k = Glyph.bit g :: (gs.map Glyph.bit ++ T :: below) := by simpa using hstk
    have hgT : Glyph.bit g ≠ T := fun h => hTb g h.symm
    have e1 : Eval main (.peek k rT) t ⟨Function.update t.reg rT (Glyph.bit g), t.stk⟩ 1 := by
      have h := Eval.peek (main := main) k rT t
      rw [hstk'] at h
      simpa [List.headD_cons] using h
    have hr : (⟨Function.update t.reg rT (Glyph.bit g), t.stk⟩ : State).reg rT = Glyph.bit g := by
      simp [Function.update_apply]
    have hne : ¬ ((⟨Function.update t.reg rT (Glyph.bit g), t.stk⟩ : State).reg rT = T) := by
      simp only [Function.update_apply, if_pos rfl]; exact hgT
    have e2 : Eval main (.pop k rR) ⟨Function.update t.reg rT (Glyph.bit g), t.stk⟩
        ⟨Function.update (Function.update t.reg rT (Glyph.bit g)) rR (Glyph.bit g),
          Function.update t.stk k (gs.map Glyph.bit ++ T :: below)⟩ 1 := by
      have h := Eval.pop (main := main) k rR ⟨Function.update t.reg rT (Glyph.bit g), t.stk⟩
      rw [show (⟨Function.update t.reg rT (Glyph.bit g), t.stk⟩ : State).stk k =
          Glyph.bit g :: (gs.map Glyph.bit ++ T :: below) from hstk'] at h
      simpa [List.headD_cons, List.tail_cons] using h
    have hmain : Eval main (readBit k T rT rR) t
        ⟨Function.update (Function.update t.reg rT (Glyph.bit g)) rR (Glyph.bit g),
          Function.update t.stk k (gs.map Glyph.bit ++ T :: below)⟩ 3 :=
      Eval.seq e1 (Eval.iteF hne e2)
    have hgoal : (⟨Function.update (Function.update t.reg rT (Glyph.bit g)) rR (Glyph.bit g),
          Function.update t.stk k (gs.map Glyph.bit ++ T :: below)⟩ : State)
        = ⟨Function.update (Function.update t.reg rT
              (((g :: gs).map Glyph.bit ++ T :: below).headD Glyph.eos)) rR
              (Glyph.bit ((g :: gs).getD 0 false)),
            Function.update t.stk k (((g :: gs).drop 1).map Glyph.bit ++ T :: below)⟩ := by
      apply State.ext'
      · intro q
        simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.headD_cons,
          List.getD_cons_zero, Function.update_apply]
        by_cases h1 : q = rT
        · subst h1; by_cases h2 : rT = rR <;> simp [h2]
        · by_cases h2 : q = rR <;> simp [h1, h2]
      · intro q
        simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero,
          Function.update_apply]
    rw [hgoal] at hmain
    exact hmain


/-! ## The subtractor loop -/

/-- The "do one step" branch: read a bit of each region, subtract and continue. -/
def subDo (a b : Stk) (Ta Tb : Glyph) (out : Stk)
    (rX rY rC rZ rT rU rF : Reg) : Cmd :=
  .seq (readBit a Ta rT rX)
    (.seq (readBit b Tb rU rY)
      (.seq (subStep rX rY rC rZ out) (.set rF gGo)))

/-- One step of the subtractor: stop (setting `rF` to `gStop`) when both regions are exhausted,
otherwise run `subDo`. -/
def subBody (a b : Stk) (Ta Tb : Glyph) (out : Stk)
    (rX rY rC rZ rT rU rF : Reg) : Cmd :=
  .seq (.peek a rT)
    (.seq (.peek b rU)
      (.ite rT Ta (.ite rU Tb (.set rF gStop) (subDo a b Ta Tb out rX rY rC rZ rT rU rF))
                  (subDo a b Ta Tb out rX rY rC rZ rT rU rF)))

/-- The whole ripple subtractor. -/
def subLoop (a b : Stk) (Ta Tb : Glyph) (out : Stk)
    (rX rY rC rZ rT rU rF : Reg) : Cmd :=
  .seq (.set rC (.bit false))
    (.seq (.set rF gGo) (.loop rF gGo (subBody a b Ta Tb out rX rY rC rZ rT rU rF)))

end SG
end Work.IntLib
