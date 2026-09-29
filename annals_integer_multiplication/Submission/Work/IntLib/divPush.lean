import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.subRippleBits_padBits
import Submission.Work.IntLib.incBitsListAPI
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.eval_dropRgn
import Submission.Work.IntLib.eval_subBitProg

/-!
# IntLib division: proofs for the long-division core

Assembly of the core of `Work.IntLib.divCore` from the raw toolkit and the primitive lemmas.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib.Div

open HvdH

/-! ## Pure list algebra -/

/-- `subRippleBits` on lists obtained by appending one element: the new element is processed last. -/
theorem subRippleBits_append (xs ys : List Bool) (d e : Bool) :
    ∀ (c : Bool), xs.length = ys.length →
    subRippleBits (xs ++ [d]) (ys ++ [e]) c =
      (subBorrow d e (subRippleBits xs ys c).1,
        (subRippleBits xs ys c).2 ++ [subBitVal d e (subRippleBits xs ys c).1]) := by
  induction xs generalizing ys with
  | nil =>
    intro c h
    cases ys with
    | nil => simp [subRippleBits]
    | cons _ _ => simp at h
  | cons x xt ih =>
    intro c h
    cases ys with
    | nil => simp at h
    | cons y yt =>
      have h' : xt.length = yt.length := by simpa using h
      simp only [List.cons_append, subRippleBits]
      rw [ih yt (subBorrow x y c) h']

/-! ## Pushing markers -/

/-- `mkG k m` pushes `m` onto stack `k` in two steps. -/
theorem eval_mkG (main : Cmd) (k : Stk) (m : Glyph) (S : State) :
    Eval main (mkG k m) S ((S.updReg rgT m).updStk k (m :: S.stk k)) 2 := by
  have h1 : Eval main (.set rgT m) S (S.updReg rgT m) 1 := Eval.set rgT m S
  have h2 : Eval main (.push k rgT) (S.updReg rgT m)
      ((S.updReg rgT m).updStk k (m :: (S.updReg rgT m).stk k)) 1 := Eval.push k rgT _
  have h3 := Eval.seq h1 h2
  simpa [mkG, State.updStk, State.updReg, State.tPush, State.tSet, Function.update_apply] using h3

/-- Successive `mkG`s, as a foldl of stack updates. -/
def pmAux (b0 : State) (l : List (Stk × Glyph)) : State :=
  l.foldl (fun S km => (S.updReg rgT km.2).updStk km.1 (km.2 :: S.stk km.1)) b0

theorem pmAux_cons (b0 : State) (km : Stk × Glyph) (l : List (Stk × Glyph)) :
    pmAux b0 (km :: l) = pmAux ((b0.updReg rgT km.2).updStk km.1 (km.2 :: b0.stk km.1)) l := by
  simp [pmAux, List.foldl_cons]

theorem eval_pmAux (main : Cmd) (l : List (Stk × Glyph)) :
    ∀ b0 : State, Eval main (seqs (l.map fun km => mkG km.1 km.2)) b0 (pmAux b0 l)
      (2 * l.length + 1) := by
  induction l with
  | nil => intro b0; simpa [seqs, pmAux] using Eval.skip b0
  | cons km rest ih =>
    intro b0
    have h1 : Eval main (mkG km.1 km.2) b0
        ((b0.updReg rgT km.2).updStk km.1 (km.2 :: b0.stk km.1)) 2 := eval_mkG main km.1 km.2 b0
    have h2 := ih ((b0.updReg rgT km.2).updStk km.1 (km.2 :: b0.stk km.1))
    have h3 := Eval.seq h1 h2
    rw [pmAux_cons]
    simpa [seqs, List.length_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using h3

/-- The marker list of `pushMarkers`. -/
def markerList : List (Stk × Glyph) :=
  [(stP, gP), (stB, gB), (stR, gR), (stQ, gQ), (stS, gS), (stC, gC), (stD, gD), (stX, gX), (stY, gY)]

/-- The state produced by `pushMarkers`. -/
def pushedSt (b0 : State) : State := pmAux b0 markerList

@[simp] theorem pushedSt_stk1 (b0 : State) : (pushedSt b0).stk stP = [gP] ++ b0.stk stP := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stP, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk2 (b0 : State) : (pushedSt b0).stk stB = [gB] ++ b0.stk stB := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stB, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk3 (b0 : State) : (pushedSt b0).stk stR = [gR] ++ b0.stk stR := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stR, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk4 (b0 : State) : (pushedSt b0).stk stQ = [gQ] ++ b0.stk stQ := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stQ, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk5 (b0 : State) : (pushedSt b0).stk stS = [gS] ++ b0.stk stS := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stS, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk6 (b0 : State) : (pushedSt b0).stk stC = [gC] ++ b0.stk stC := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stC, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk7 (b0 : State) : (pushedSt b0).stk stD = [gD] ++ b0.stk stD := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stD, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk8 (b0 : State) : (pushedSt b0).stk stX = [gX] ++ b0.stk stX := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stX, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk9 (b0 : State) : (pushedSt b0).stk stY = [gY] ++ b0.stk stY := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, stY, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_stk0 (b0 : State) : (pushedSt b0).stk 0 = b0.stk 0 := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, State.updStk, State.updReg, Function.update_apply]

@[simp] theorem pushedSt_reg (b0 : State) (r : Reg) : (pushedSt b0).reg r = if r = rgT then gY else b0.reg r := by
  simp (config := { decide := true }) [pushedSt, pmAux, markerList, State.updStk, State.updReg, Function.update_apply]

theorem eval_pushMarkers (main : Cmd) (b0 : State) :
    Eval main pushMarkers b0 (pushedSt b0) 19 := by
  have h0 : pushMarkers = seqs (markerList.map fun km => mkG km.1 km.2) := rfl
  have h := eval_pmAux main markerList b0
  rw [h0]
  simpa [markerList, pushedSt] using h

/-! ## Component lemmas for the canonical result states -/

@[simp] theorem tPop_stk_same (s : State) (k : Stk) (r : Reg) :
    (State.tPop s k r).stk k = (s.stk k).tail := by
  simp [State.tPop, State.updStk, State.updReg]

@[simp] theorem tPop_stk_ne (s : State) (k : Stk) (r : Reg) (j : Stk) (h : j ≠ k) :
    (State.tPop s k r).stk j = s.stk j := by
  simp [State.tPop, State.updStk, State.updReg, h]

@[simp] theorem tPop_reg_same (s : State) (k : Stk) (r : Reg) :
    (State.tPop s k r).reg r = (s.stk k).headD .eos := by
  simp [State.tPop, State.updReg]

@[simp] theorem tPop_reg_ne (s : State) (k : Stk) (r r' : Reg) (h : r' ≠ r) :
    (State.tPop s k r).reg r' = s.reg r' := by
  simp [State.tPop, State.updReg, h]

@[simp] theorem tPush_stk_same (s : State) (k : Stk) (r : Reg) :
    (State.tPush s k r).stk k = s.reg r :: s.stk k := by
  simp [State.tPush, State.updStk]

@[simp] theorem tPush_stk_ne (s : State) (k : Stk) (r : Reg) (j : Stk) (h : j ≠ k) :
    (State.tPush s k r).stk j = s.stk j := by
  simp [State.tPush, State.updStk, h]

@[simp] theorem tPush_reg (s : State) (k : Stk) (r r' : Reg) :
    (State.tPush s k r).reg r' = s.reg r' := rfl

@[simp] theorem tSet_reg_same (s : State) (r : Reg) (g : Glyph) :
    (State.tSet s r g).reg r = g := by
  simp [State.tSet, State.updReg]

@[simp] theorem tSet_reg_ne (s : State) (r r' : Reg) (g : Glyph) (h : r' ≠ r) :
    (State.tSet s r g).reg r' = s.reg r' := by
  simp [State.tSet, State.updReg, h]

@[simp] theorem tSet_stk (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet s r g).stk j = s.stk j := rfl


end Work.IntLib.Div
