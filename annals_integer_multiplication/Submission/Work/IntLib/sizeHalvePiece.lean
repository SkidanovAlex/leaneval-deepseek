import Mathlib
import Submission.Work.IntLib.SizeShared

/-!
# `size` / `clog 2` / `pow2`, piece `sizeHalve`

Repeatedly halve the unary counter `u` sitting on stack 1 (`toks u ++ gA :: below1`), pushing the
parity bits (least significant first) onto stack 3, so that stack 3 finally carries the *most*
significant bit first: `(u.bits).reverse.map Glyph.bit ++ gC :: below3`.

Algorithm.  The two scratch stacks 1 and 2 alternate as "current counter region" and "halved
counter region".  One *round* of the outer loop consumes the counter `a` from stack 1 (pushing
the parity bit of `a` onto stack 3 and writing `a / 2` onto stack 2) and then the counter `a / 2`
from stack 2 (pushing the parity bit of `a / 2` and writing `a / 4` back onto stack 1).  So each
round costs `O(a)` and reduces the counter by a factor of at most 4, for total cost `O(u)`.
Each half-step walks the unary counter in pairs (`tok tok ↦ tok`, `tok` `marker` ↦ parity 1).

-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

namespace SizeHalve

open Work.IntLib.Size (toks gTok gA gB gC toks_zero toks_succ toks_length toks_add toks_headD toks_tail eos_ne_gA gA_ne_eos gTok_ne_gA gTok_ne_gB)

/-! ## Registers -/

/-- Outer loop condition (`gA` = continue). -/
def rCond : Reg := 0
/-- First scratch (pop) register. -/
def rX1 : Reg := 1
/-- Second scratch (pop) register. -/
def rX2 : Reg := 2
/-- Constant register holding the counter token `gTok`. -/
def rKC : Reg := 3
/-- Constant register holding `bit false`. -/
def rFC : Reg := 4
/-- Constant register holding `bit true`. -/
def rTC : Reg := 5
/-- Inner loop condition (`gA` = continue). -/
def rIn : Reg := 6
/-- Constant register holding the marker `gB`. -/
def rMC : Reg := 7
/-- Constant register holding the marker `gC`. -/
def rSC : Reg := 8

/-! ## Arithmetic of `Nat.bits` / `Nat.bodd` -/

theorem bits_eq_bodd_cons {n : ℕ} (hn : n ≠ 0) : n.bits = n.bodd :: (n / 2).bits := by
  conv_lhs => rw [← Nat.bit_bodd_div2 n]
  rw [Nat.bits_append_bit]
  · rfl
  · intro h
    have h2 : n / 2 = 0 := by simpa [Nat.div2_val] using h
    have h1 : n = 1 := by omega
    subst h1; rfl

theorem bodd_add_two (n : ℕ) : (n + 2).bodd = n.bodd := by
  have h : n + 2 = (n + 1) + 1 := by omega
  rw [h, Nat.bodd_succ, Nat.bodd_succ, Bool.not_not]

theorem bodd_sub_two {n : ℕ} (hn : 2 ≤ n) : (n - 2).bodd = n.bodd := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [bodd_add_two m]

theorem div2_div2 (n : ℕ) : n / 2 / 2 = n / 4 := by
  rw [Nat.div_div_eq_div_mul]

theorem ne_comm {α : Type} [DecidableEq α] {a b : α} (h : a ≠ b) : ¬ (b = a) :=
  fun h' => h h'.symm

theorem toks_headD_ne {m : ℕ} (hm : m ≠ 0) (M : Glyph) (l : List Glyph) :
    (toks m ++ M :: l).headD Glyph.eos = gTok := by
  rw [toks_headD]; simp [hm]

theorem tPeek_reg_eq (s : State) (k : Stk) (r : Reg) (c : Glyph)
    (h : (s.stk k).headD Glyph.eos = c) : (State.tPeek s k r).reg r = c := by
  show (s.updReg r ((s.stk k).headD Glyph.eos)).reg r = c
  rw [State.updReg_apply, if_pos rfl]
  exact h

theorem tPeek_stk_eq (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPeek s k r).stk j = s.stk j := by
  simp [State.tPeek, State.updReg_stk]

theorem sub_two_div_two {n : ℕ} (hn : 2 ≤ n) : (n - 2) / 2 + 1 = n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := Nat.add_mul_div_left m 1 (y := 2) (by norm_num)
  simpa using h

theorem toks_one : toks 1 = [gTok] := by
  rw [show (1 : ℕ) = 0 + 1 by norm_num, toks_succ, toks_zero]

theorem one_div_two : (1 : ℕ) / 2 = 0 := by norm_num

theorem toks_two (m : ℕ) : toks (m + 2) = gTok :: gTok :: toks m := by
  rw [toks_succ, toks_succ]

theorem toks_pred_pred {m : ℕ} (hm : 2 ≤ m) : toks m = gTok :: gTok :: toks (m - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [toks_two, Nat.add_sub_cancel]

theorem toks_add_one (m : ℕ) : toks (m + 1) = gTok :: toks m := by
  rw [toks_succ]

theorem bits_reverse_eq (n : ℕ) (hn : 2 ≤ n) :
    (n.bits).reverse = ((n / 4).bits).reverse ++ [(n / 2).bodd, n.bodd] := by
  have h1 : n.bits = n.bodd :: (n / 2).bits := bits_eq_bodd_cons (by omega)
  have h2 : (n / 2).bits = (n / 2).bodd :: ((n / 2) / 2).bits := bits_eq_bodd_cons (by omega)
  rw [h1, List.reverse_cons, h2, List.reverse_cons]
  simp only [List.append_assoc, List.singleton_append]
  congr 1
  rw [div2_div2]

theorem bits_reverse_map_eq (n : ℕ) (hn : 2 ≤ n) :
    (n.bits).reverse.map Glyph.bit =
      ((n / 4).bits).reverse.map Glyph.bit ++ [Glyph.bit (n / 2).bodd, Glyph.bit n.bodd] := by
  rw [bits_reverse_eq n hn, List.map_append]
  simp

/-! ## Programs -/

/-- One step of the inner halving loop: read a token from `sA`; if the marker `mA` is on top the
counter is exhausted (push `bit false` and stop); otherwise drop the token, look at the next glyph;
if it is the marker the counter was odd (push `bit true` and stop), otherwise drop it as well, push
one token on `sB` and continue. -/
def halveInner (sA sB : Stk) (mA : Glyph) : Cmd :=
  Cmd.seq (Cmd.peek sA rX1)
    (Cmd.ite rX1 mA
      (Cmd.seq (Cmd.push 3 rFC) (Cmd.set rIn Glyph.eos))
      (Cmd.seq (Cmd.pop sA rX1)
        (Cmd.seq (Cmd.peek sA rX2)
          (Cmd.ite rX2 mA
            (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
            (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA)))))))

/-- Halve the unary counter on stack `sA` (marker `mA`), pushing `bit (m.bodd)` on stack 3 and
writing `m / 2` tokens on stack `sB`. -/
def halve (sA sB : Stk) (mA : Glyph) : Cmd :=
  Cmd.seq (Cmd.set rIn gA) (Cmd.loop rIn gA (halveInner sA sB mA))

/-- Half-step from stack 1 to stack 2 (if stack 1's counter is nonempty). -/
def step12 : Cmd :=
  Cmd.seq (Cmd.peek 1 rX1)
    (Cmd.ite rX1 gA Cmd.skip (Cmd.seq (halve 1 2 gA) (Cmd.set rCond gA)))

/-- Half-step from stack 2 to stack 1 (if stack 2's counter is nonempty). -/
def step21 : Cmd :=
  Cmd.seq (Cmd.peek 2 rX1)
    (Cmd.ite rX1 gB Cmd.skip (Cmd.seq (halve 2 1 gB) (Cmd.set rCond gA)))

/-- One round of the outer loop. -/
def loopBody : Cmd := Cmd.seq (Cmd.set rCond Glyph.eos) (Cmd.seq step12 step21)

/-- The outer loop. -/
def loopProg : Cmd := Cmd.loop rCond gA loopBody

/-- Initialisation: push the markers `gB` (stack 2) and `gC` (stack 3), load the constant
registers and set the loop condition. -/
def initProg : Cmd :=
  Cmd.seq (Cmd.set rMC gB)
    (Cmd.seq (Cmd.push 2 rMC)
      (Cmd.seq (Cmd.set rSC gC)
        (Cmd.seq (Cmd.push 3 rSC)
          (Cmd.seq (Cmd.set rKC gTok)
            (Cmd.seq (Cmd.set rFC (Glyph.bit false))
              (Cmd.seq (Cmd.set rTC (Glyph.bit true)) (Cmd.set rCond gA)))))))

/-- Discard the `gB` marker of stack 2. -/
def finishProg : Cmd := Cmd.pop 2 rSC

/-- The complete piece. -/
def prog : Cmd := Cmd.seq initProg (Cmd.seq loopProg finishProg)

/-! ## States of one inner iteration -/

/-- State after the iteration that finds the marker (even counter). -/
def stopEvenState (sA : Stk) (s : State) : State :=
  State.tSet (State.tPush (State.tPeek s sA rX1) 3 rFC) rIn Glyph.eos

/-- State after the iteration that finds a single leftover token (odd counter). -/
def stopOddState (sA : Stk) (s : State) : State :=
  State.tSet (State.tPush (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) 3 rTC)
    rIn Glyph.eos

/-- State after an iteration that consumes two tokens (counter reduced by two). -/
def contState (sA sB : Stk) (s : State) : State :=
  State.tSet
    (State.tPush (State.tPop (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) sA rX2)
      sB rKC) rIn gA

/-! ## The inner loop body -/

theorem eval_innerBody_stopEven (main : Cmd) (sA sB : Stk) (mA : Glyph) (rest : List Glyph)
    (s : State) (hsA : s.stk sA = mA :: rest) (hF : s.reg rFC = Glyph.bit false) :
    Eval main (halveInner sA sB mA) s (stopEvenState sA s) 4 := by
  have h1 : Eval main (Cmd.peek sA rX1) s (State.tPeek s sA rX1) 1 := Eval.peek sA rX1 s
  have hr1 : (State.tPeek s sA rX1).reg rX1 = mA := by
    simp [State.tPeek, State.updReg_apply, hsA]
  have hpush : Eval main (Cmd.push 3 rFC) (State.tPeek s sA rX1)
      (State.tPush (State.tPeek s sA rX1) 3 rFC) 1 := Eval.push 3 rFC _
  have hset : Eval main (Cmd.set rIn Glyph.eos) (State.tPush (State.tPeek s sA rX1) 3 rFC)
      (stopEvenState sA s) 1 := Eval.set rIn Glyph.eos _
  have h2 : Eval main (Cmd.seq (Cmd.push 3 rFC) (Cmd.set rIn Glyph.eos))
      (State.tPeek s sA rX1) (stopEvenState sA s) 2 := Eval.seq hpush hset
  have h3 : Eval main
      (Cmd.ite rX1 mA (Cmd.seq (Cmd.push 3 rFC) (Cmd.set rIn Glyph.eos))
        (Cmd.seq (Cmd.pop sA rX1)
          (Cmd.seq (Cmd.peek sA rX2)
            (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
              (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA)))))))
      (State.tPeek s sA rX1) (stopEvenState sA s) 3 := Eval.iteT hr1 h2
  exact Eval.seq h1 h3

theorem eval_innerBody_stopOdd (main : Cmd) (sA sB : Stk) (mA : Glyph) (rest : List Glyph)
    (s : State) (hsA : s.stk sA = gTok :: mA :: rest) (hmA : gTok ≠ mA)
    (hT : s.reg rTC = Glyph.bit true) :
    Eval main (halveInner sA sB mA) s (stopOddState sA s) 7 := by
  have h1 : Eval main (Cmd.peek sA rX1) s (State.tPeek s sA rX1) 1 := Eval.peek sA rX1 s
  have hr1 : (State.tPeek s sA rX1).reg rX1 = gTok := by
    simp [State.tPeek, State.updReg_apply, hsA]
  have hr1' : (State.tPeek s sA rX1).reg rX1 ≠ mA := by rw [hr1]; exact hmA
  have h2 : Eval main (Cmd.pop sA rX1) (State.tPeek s sA rX1)
      (State.tPop (State.tPeek s sA rX1) sA rX1) 1 := Eval.pop sA rX1 _
  have h3 : Eval main (Cmd.peek sA rX2) (State.tPop (State.tPeek s sA rX1) sA rX1)
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) 1 := Eval.peek sA rX2 _
  have hr2 : (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2).reg rX2 = mA := by
    simp [State.tPeek, State.tPop, State.updReg_apply, State.updStk_apply, hsA]
  have hpush : Eval main (Cmd.push 3 rTC)
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2)
      (State.tPush (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) 3 rTC) 1 :=
    Eval.push 3 rTC _
  have hset : Eval main (Cmd.set rIn Glyph.eos)
      (State.tPush (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) 3 rTC)
      (stopOddState sA s) 1 := Eval.set rIn Glyph.eos _
  have h4 : Eval main (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) (stopOddState sA s) 2 :=
    Eval.seq hpush hset
  have h5 : Eval main
      (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
        (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA))))
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) (stopOddState sA s) 3 :=
    Eval.iteT hr2 h4
  have h6 : Eval main
      (Cmd.seq (Cmd.pop sA rX1)
        (Cmd.seq (Cmd.peek sA rX2)
          (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
            (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA))))))
      (State.tPeek s sA rX1) (stopOddState sA s) 5 := Eval.seq h2 (Eval.seq h3 h5)
  have h7 : Eval main
      (Cmd.ite rX1 mA (Cmd.seq (Cmd.push 3 rFC) (Cmd.set rIn Glyph.eos))
        (Cmd.seq (Cmd.pop sA rX1)
          (Cmd.seq (Cmd.peek sA rX2)
            (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
              (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA)))))))
      (State.tPeek s sA rX1) (stopOddState sA s) 6 := Eval.iteF hr1' h6
  exact Eval.seq h1 h7

theorem eval_innerBody_cont (main : Cmd) (sA sB : Stk) (mA : Glyph) (rest : List Glyph)
    (s : State) (hsA : s.stk sA = gTok :: gTok :: rest) (hmA : gTok ≠ mA) :
    Eval main (halveInner sA sB mA) s (contState sA sB s) 8 := by
  have h1 : Eval main (Cmd.peek sA rX1) s (State.tPeek s sA rX1) 1 := Eval.peek sA rX1 s
  have hr1 : (State.tPeek s sA rX1).reg rX1 = gTok := by
    simp [State.tPeek, State.updReg_apply, hsA]
  have hr1' : (State.tPeek s sA rX1).reg rX1 ≠ mA := by rw [hr1]; exact hmA
  have h2 : Eval main (Cmd.pop sA rX1) (State.tPeek s sA rX1)
      (State.tPop (State.tPeek s sA rX1) sA rX1) 1 := Eval.pop sA rX1 _
  have h3 : Eval main (Cmd.peek sA rX2) (State.tPop (State.tPeek s sA rX1) sA rX1)
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) 1 := Eval.peek sA rX2 _
  have hr2 : (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2).reg rX2 = gTok := by
    simp [State.tPeek, State.tPop, State.updReg_apply, State.updStk_apply, hsA]
  have hr2' : (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2).reg rX2 ≠ mA := by
    rw [hr2]; exact hmA
  have h4 : Eval main (Cmd.pop sA rX2)
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2)
      (State.tPop (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) sA rX2) 1 :=
    Eval.pop sA rX2 _
  have h5 : Eval main (Cmd.push sB rKC)
      (State.tPop (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) sA rX2)
      (State.tPush (State.tPop (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2)
        sA rX2) sB rKC) 1 := Eval.push sB rKC _
  have h6 : Eval main (Cmd.set rIn gA)
      (State.tPush (State.tPop (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2)
        sA rX2) sB rKC) (contState sA sB s) 1 := Eval.set rIn gA _
  have h7 : Eval main (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA))
      (State.tPop (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) sA rX2)
      (contState sA sB s) 2 := Eval.seq h5 h6
  have h8 : Eval main (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA)))
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) (contState sA sB s) 3 :=
    Eval.seq h4 h7
  have h9 : Eval main
      (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
        (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA))))
      (State.tPeek (State.tPop (State.tPeek s sA rX1) sA rX1) sA rX2) (contState sA sB s) 4 :=
    Eval.iteF hr2' h8
  have h10 : Eval main
      (Cmd.seq (Cmd.peek sA rX2)
        (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
          (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA)))))
      (State.tPop (State.tPeek s sA rX1) sA rX1) (contState sA sB s) 5 := Eval.seq h3 h9
  have h11 : Eval main
      (Cmd.seq (Cmd.pop sA rX1)
        (Cmd.seq (Cmd.peek sA rX2)
          (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
            (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA))))))
      (State.tPeek s sA rX1) (contState sA sB s) 6 := Eval.seq h2 h10
  have h12 : Eval main
      (Cmd.ite rX1 mA (Cmd.seq (Cmd.push 3 rFC) (Cmd.set rIn Glyph.eos))
        (Cmd.seq (Cmd.pop sA rX1)
          (Cmd.seq (Cmd.peek sA rX2)
            (Cmd.ite rX2 mA (Cmd.seq (Cmd.push 3 rTC) (Cmd.set rIn Glyph.eos))
              (Cmd.seq (Cmd.pop sA rX2) (Cmd.seq (Cmd.push sB rKC) (Cmd.set rIn gA)))))))
      (State.tPeek s sA rX1) (contState sA sB s) 7 := Eval.iteF hr1' h11
  exact Eval.seq h1 h12

/-! ## Projections -/

theorem stopEvenState_reg_rIn (sA : Stk) (s : State) : (stopEvenState sA s).reg rIn = Glyph.eos := by
  simp +decide [stopEvenState, State.tSet]

theorem stopEvenState_stk_3 (sA : Stk) (s : State) (hF : s.reg rFC = Glyph.bit false) :
    (stopEvenState sA s).stk 3 = Glyph.bit false :: s.stk 3 := by
  simp +decide [stopEvenState, State.tSet, State.tPush, State.tPeek, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, hF]

theorem stopEvenState_stk_ne (sA : Stk) (s : State) {k : Stk} (hk : k ≠ 3) :
    (stopEvenState sA s).stk k = s.stk k := by
  simp +decide [stopEvenState, State.tSet, State.tPush, State.tPeek, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, hk]

theorem stopEvenState_reg_rCond (sA : Stk) (s : State) :
    (stopEvenState sA s).reg rCond = s.reg rCond := by
  simp +decide [stopEvenState, State.tSet, State.tPush, State.tPeek, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem stopEvenState_reg_rKC (sA : Stk) (s : State) :
    (stopEvenState sA s).reg rKC = s.reg rKC := by
  simp +decide [stopEvenState, State.tSet, State.tPush, State.tPeek, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem stopEvenState_reg_rTC (sA : Stk) (s : State) :
    (stopEvenState sA s).reg rTC = s.reg rTC := by
  simp +decide [stopEvenState, State.tSet, State.tPush, State.tPeek, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem stopEvenState_reg_rFC (sA : Stk) (s : State) :
    (stopEvenState sA s).reg rFC = s.reg rFC := by
  simp +decide [stopEvenState, State.tSet, State.tPush, State.tPeek, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem stopOddState_reg_rFC (sA : Stk) (s : State) :
    (stopOddState sA s).reg rFC = s.reg rFC := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem stopOddState_reg_rTC (sA : Stk) (s : State) :
    (stopOddState sA s).reg rTC = s.reg rTC := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem contState_stk_3 (sA sB : Stk) (s : State) (hA3 : 3 ≠ sA) (hB3 : 3 ≠ sB) :
    (contState sA sB s).stk 3 = s.stk 3 := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, hA3, hB3]

theorem stopOddState_reg_rIn (sA : Stk) (s : State) : (stopOddState sA s).reg rIn = Glyph.eos := by
  simp +decide [stopOddState, State.tSet]

theorem stopOddState_stk_3 (sA : Stk) (s : State) (hA3 : 3 ≠ sA)
    (hT : s.reg rTC = Glyph.bit true) :
    (stopOddState sA s).stk 3 = Glyph.bit true :: s.stk 3 := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, hA3, hT]

theorem stopOddState_stk_sA (sA : Stk) (rest : List Glyph) (s : State)
    (hA3 : sA ≠ 3) (hsA : s.stk sA = gTok :: rest) :
    (stopOddState sA s).stk sA = rest := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, hA3, ne_comm hA3, hsA]

theorem stopOddState_stk_ne (sA : Stk) (s : State) {k : Stk} (h1 : k ≠ sA) (h2 : k ≠ 3) :
    (stopOddState sA s).stk k = s.stk k := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, h1, h2]

theorem stopOddState_reg_rCond (sA : Stk) (s : State) :
    (stopOddState sA s).reg rCond = s.reg rCond := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem stopOddState_reg_rKC (sA : Stk) (s : State) :
    (stopOddState sA s).reg rKC = s.reg rKC := by
  simp +decide [stopOddState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem contState_stk_sA (sA sB : Stk) (rest : List Glyph) (s : State)
    (hAB : sA ≠ sB) (hA3 : sA ≠ 3) (hsA : s.stk sA = gTok :: gTok :: rest) :
    (contState sA sB s).stk sA = rest := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, hAB, hA3, hsA]

theorem contState_stk_sB (sA sB : Stk) (s : State) (hAB : sA ≠ sB) (hB3 : sB ≠ 3)
    (hK : s.reg rKC = gTok) :
    (contState sA sB s).stk sB = gTok :: s.stk sB := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, ne_comm hAB, hB3, hK]

theorem contState_stk_ne (sA sB : Stk) (s : State) {k : Stk} (h1 : k ≠ sA) (h2 : k ≠ sB)
    (h3 : k ≠ 3) : (contState sA sB s).stk k = s.stk k := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk, h1, h2, h3]

theorem contState_reg_rIn (sA sB : Stk) (s : State) : (contState sA sB s).reg rIn = gA := by
  simp +decide [contState, State.tSet]

theorem contState_reg_rCond (sA sB : Stk) (s : State) :
    (contState sA sB s).reg rCond = s.reg rCond := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem contState_reg_rKC (sA sB : Stk) (s : State) :
    (contState sA sB s).reg rKC = s.reg rKC := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem contState_reg_rFC (sA sB : Stk) (s : State) :
    (contState sA sB s).reg rFC = s.reg rFC := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

theorem contState_reg_rTC (sA sB : Stk) (s : State) :
    (contState sA sB s).reg rTC = s.reg rTC := by
  simp +decide [contState, State.tSet, State.tPush, State.tPeek, State.tPop, State.updStk_apply,
    State.updReg_apply, State.updReg_stk]

/-! ## The inner halving loop -/

theorem halveInner_eval (main : Cmd) (sA sB : Stk) (mA : Glyph)
    (hAB : sA ≠ sB) (hA3 : sA ≠ 3) (hB3 : sB ≠ 3) (hmA : gTok ≠ mA) :
    ∀ (m w : ℕ) (belowA Y Z : List Glyph) (s : State),
      s.stk sA = toks m ++ mA :: belowA → s.stk sB = toks w ++ Y → s.stk 3 = Z →
      s.reg rIn = gA → s.reg rKC = gTok → s.reg rFC = Glyph.bit false →
      s.reg rTC = Glyph.bit true →
      ∃ (s' : State) (c : ℕ), Eval main (Cmd.loop rIn gA (halveInner sA sB mA)) s s' c ∧
        c ≤ 9 * (m + 1) + 2 ∧
        s'.stk sA = mA :: belowA ∧ s'.stk sB = toks (w + m / 2) ++ Y ∧
        s'.stk 3 = Glyph.bit m.bodd :: Z ∧ s'.reg rIn = Glyph.eos ∧
        s'.reg rKC = gTok ∧ s'.reg rFC = Glyph.bit false ∧ s'.reg rTC = Glyph.bit true ∧
        s'.reg rCond = s.reg rCond ∧
        (∀ k : Stk, k ≠ sA → k ≠ sB → k ≠ 3 → s'.stk k = s.stk k) := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro n ih w belowA Y Z s hsA hsB hs3 hIn hK hF hT
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have hsA0 : s.stk sA = mA :: belowA := by rw [hsA]; rfl
      have hev : Eval main (halveInner sA sB mA) s (stopEvenState sA s) 4 :=
        eval_innerBody_stopEven main sA sB mA belowA s hsA0 hF
      have hstop : (stopEvenState sA s).reg rIn ≠ gA := by
        rw [stopEvenState_reg_rIn]; exact eos_ne_gA
      have hloop : Eval main (Cmd.loop rIn gA (halveInner sA sB mA)) s (stopEvenState sA s) 6 :=
        Eval.loopT hIn hev (Eval.loopF hstop)
      refine ⟨stopEvenState sA s, 6, hloop, by omega, ?_, ?_, ?_, stopEvenState_reg_rIn sA s,
        ?_, ?_, ?_, stopEvenState_reg_rCond sA s, ?_⟩
      · rw [stopEvenState_stk_ne sA s hA3]; exact hsA0
      · rw [stopEvenState_stk_ne sA s hB3]; simpa using hsB
      · rw [stopEvenState_stk_3 sA s hF, hs3]; simp
      · rw [stopEvenState_reg_rKC sA s]; exact hK
      · rw [stopEvenState_reg_rFC sA s]; exact hF
      · rw [stopEvenState_reg_rTC sA s]; exact hT
      · intro k hk1 hk2 hk3; exact stopEvenState_stk_ne sA s hk3
    · have hsA1 : s.stk sA = gTok :: mA :: belowA := by rw [hsA]; simp [toks_one]
      have hev : Eval main (halveInner sA sB mA) s (stopOddState sA s) 7 :=
        eval_innerBody_stopOdd main sA sB mA belowA s hsA1 hmA hT
      have hstop : (stopOddState sA s).reg rIn ≠ gA := by
        rw [stopOddState_reg_rIn]; exact eos_ne_gA
      have hloop : Eval main (Cmd.loop rIn gA (halveInner sA sB mA)) s (stopOddState sA s) 9 :=
        Eval.loopT hIn hev (Eval.loopF hstop)
      refine ⟨stopOddState sA s, 9, hloop, by omega, ?_, ?_, ?_, stopOddState_reg_rIn sA s,
        ?_, ?_, ?_, stopOddState_reg_rCond sA s, ?_⟩
      · rw [stopOddState_stk_sA sA (mA :: belowA) s hA3 hsA1]
      · rw [stopOddState_stk_ne sA s (ne_comm hAB) hB3]; simpa [one_div_two] using hsB
      · rw [stopOddState_stk_3 sA s (ne_comm hA3) hT, hs3]; simp
      · rw [stopOddState_reg_rKC sA s]; exact hK
      · rw [stopOddState_reg_rFC sA s]; exact hF
      · rw [stopOddState_reg_rTC sA s]; exact hT
      · intro k hk1 hk2 hk3; exact stopOddState_stk_ne sA s hk1 hk3
  · have hsA2 : s.stk sA = gTok :: gTok :: (toks (n - 2) ++ mA :: belowA) := by
      rw [hsA, toks_pred_pred hn]
      simp only [List.cons_append]
    have hev : Eval main (halveInner sA sB mA) s (contState sA sB s) 8 :=
      eval_innerBody_cont main sA sB mA (toks (n - 2) ++ mA :: belowA) s hsA2 hmA
    have h1 : (contState sA sB s).stk sA = toks (n - 2) ++ mA :: belowA :=
      contState_stk_sA sA sB _ s hAB hA3 hsA2
    have h2 : (contState sA sB s).stk sB = toks (w + 1) ++ Y := by
      rw [contState_stk_sB sA sB s hAB hB3 hK, hsB, toks_add_one]
      simp only [List.cons_append]
    have h3 : (contState sA sB s).stk 3 = Z := by
      rw [contState_stk_3 sA sB s (ne_comm hA3) (ne_comm hB3), hs3]
    have h4 : (contState sA sB s).reg rIn = gA := contState_reg_rIn sA sB s
    have h5 : (contState sA sB s).reg rKC = gTok := by rw [contState_reg_rKC sA sB s]; exact hK
    have h6 : (contState sA sB s).reg rFC = Glyph.bit false := by
      rw [contState_reg_rFC sA sB s]; exact hF
    have h7 : (contState sA sB s).reg rTC = Glyph.bit true := by
      rw [contState_reg_rTC sA sB s]; exact hT
    obtain ⟨s', c', hev', hc', h1', h2', h3', hrIn', hK', hF', hT', hrC', hoth'⟩ :=
      ih (n - 2) (by omega) (w + 1) belowA Y Z (contState sA sB s)
        h1 h2 h3 h4 h5 h6 h7
    have hloop : Eval main (Cmd.loop rIn gA (halveInner sA sB mA)) s s' (8 + c' + 1) :=
      Eval.loopT hIn hev hev'
    refine ⟨s', 8 + c' + 1, hloop, ?_, h1', ?_, ?_, hrIn', hK', hF', hT', ?_, ?_⟩
    · have hc := hc'; omega
    · rw [h2']
      congr 1
      rw [show w + 1 + (n - 2) / 2 = w + ((n - 2) / 2 + 1) by omega, sub_two_div_two hn]
    · rw [h3', bodd_sub_two hn]
    · rw [hrC', contState_reg_rCond]
    · intro k hk1 hk2 hk3
      rw [hoth' k hk1 hk2 hk3]
      exact contState_stk_ne sA sB s hk1 hk2 hk3

/-! ## The halving step -/

theorem halve_eval (main : Cmd) (sA sB : Stk) (mA : Glyph)
    (hAB : sA ≠ sB) (hA3 : sA ≠ 3) (hB3 : sB ≠ 3) (hmA : gTok ≠ mA) :
    ∀ (m w : ℕ) (belowA Y Z : List Glyph) (s : State),
      s.stk sA = toks m ++ mA :: belowA → s.stk sB = toks w ++ Y → s.stk 3 = Z →
      s.reg rKC = gTok → s.reg rFC = Glyph.bit false → s.reg rTC = Glyph.bit true →
      ∃ (s' : State) (c : ℕ), Eval main (halve sA sB mA) s s' c ∧ c ≤ 9 * (m + 1) + 3 ∧
        s'.stk sA = mA :: belowA ∧ s'.stk sB = toks (w + m / 2) ++ Y ∧
        s'.stk 3 = Glyph.bit m.bodd :: Z ∧ s'.reg rIn = Glyph.eos ∧
        s'.reg rKC = gTok ∧ s'.reg rFC = Glyph.bit false ∧ s'.reg rTC = Glyph.bit true ∧
        s'.reg rCond = s.reg rCond ∧
        (∀ k : Stk, k ≠ sA → k ≠ sB → k ≠ 3 → s'.stk k = s.stk k) := by
  intro m w belowA Y Z s hsA hsB hs3 hK hF hT
  have h1 : Eval main (Cmd.set rIn gA) s (s.updReg rIn gA) 1 := Eval.set rIn gA s
  have hIn : (s.updReg rIn gA).reg rIn = gA := by simp [State.updReg_apply]
  have hsA' : (s.updReg rIn gA).stk sA = toks m ++ mA :: belowA := by
    simp [State.updReg_stk, hsA]
  have hsB' : (s.updReg rIn gA).stk sB = toks w ++ Y := by simp [State.updReg_stk, hsB]
  have hs3' : (s.updReg rIn gA).stk 3 = Z := by simp [State.updReg_stk, hs3]
  have hK' : (s.updReg rIn gA).reg rKC = gTok := by
    rw [State.updReg_apply, if_neg (by decide : ¬ (rKC = rIn))]; exact hK
  have hF' : (s.updReg rIn gA).reg rFC = Glyph.bit false := by
    rw [State.updReg_apply, if_neg (by decide : ¬ (rFC = rIn))]; exact hF
  have hT' : (s.updReg rIn gA).reg rTC = Glyph.bit true := by
    rw [State.updReg_apply, if_neg (by decide : ¬ (rTC = rIn))]; exact hT
  obtain ⟨s', c', hev, hc, h1', h2', h3', hrIn, hK'', hF'', hT'', hrCond, hoth⟩ :=
    halveInner_eval main sA sB mA hAB hA3 hB3 hmA m w belowA Y Z (s.updReg rIn gA)
      hsA' hsB' hs3' hIn hK' hF' hT'
  exact ⟨s', 1 + c', Eval.seq h1 hev, by omega, h1', h2', h3', hrIn, hK'', hF'', hT'',
    by rw [hrCond, State.updReg_apply, if_neg (by decide : ¬ (rCond = rIn))], hoth⟩

/-! ## The rounds of the outer loop -/

theorem loopBody_zero (main : Cmd) (below1 below2 X : List Glyph) (s : State)
    (hs1 : s.stk 1 = gA :: below1) (hs2 : s.stk 2 = gB :: below2) (hs3 : s.stk 3 = X)
    (hC : s.reg rCond = gA) (hK : s.reg rKC = gTok) (hF : s.reg rFC = Glyph.bit false)
    (hT : s.reg rTC = Glyph.bit true) :
    ∃ (s' : State) (c : ℕ), Eval main loopBody s s' c ∧ c ≤ 7 ∧
      s'.stk 1 = gA :: below1 ∧ s'.stk 2 = gB :: below2 ∧ s'.stk 3 = X ∧
      s'.reg rCond = Glyph.eos ∧ s'.reg rKC = gTok ∧ s'.reg rFC = Glyph.bit false ∧
      s'.reg rTC = Glyph.bit true ∧
      (∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  let s1 : State := s.updReg rCond Glyph.eos
  let u1 : State := State.tPeek s1 1 rX1
  let u2 : State := State.tPeek u1 2 rX1
  have e0 : Eval main (Cmd.set rCond Glyph.eos) s s1 1 := Eval.set rCond Glyph.eos s
  have ep1 : Eval main (Cmd.peek 1 rX1) s1 u1 1 := Eval.peek 1 rX1 s1
  have hs1s1 : s1.stk 1 = gA :: below1 := by simp [s1, State.updReg_stk, hs1]
  have hu1 : u1.reg rX1 = gA := by
    simp [u1, State.tPeek, State.updReg_apply, hs1s1]
  have esk1 : Eval main Cmd.skip u1 u1 1 := Eval.skip u1
  have eite1 : Eval main (Cmd.ite rX1 gA Cmd.skip (Cmd.seq (halve 1 2 gA) (Cmd.set rCond gA)))
      u1 u1 2 := Eval.iteT hu1 esk1
  have ep2 : Eval main (Cmd.peek 2 rX1) u1 u2 1 := Eval.peek 2 rX1 u1
  have hs2u1 : u1.stk 2 = gB :: below2 := by simp [u1, State.tPeek, State.updReg_stk, s1, hs2]
  have hu2 : u2.reg rX1 = gB := by
    simp [u2, State.tPeek, State.updReg_apply, hs2u1]
  have esk2 : Eval main Cmd.skip u2 u2 1 := Eval.skip u2
  have eite2 : Eval main (Cmd.ite rX1 gB Cmd.skip (Cmd.seq (halve 2 1 gB) (Cmd.set rCond gA)))
      u2 u2 2 := Eval.iteT hu2 esk2
  have estep12 : Eval main step12 s1 u1 3 := Eval.seq ep1 eite1
  have estep21 : Eval main step21 u1 u2 3 := Eval.seq ep2 eite2
  have ebody : Eval main loopBody s u2 7 := Eval.seq e0 (Eval.seq estep12 estep21)
  refine ⟨u2, 7, ebody, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_stk, State.updStk_apply, hs1]
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_stk, State.updStk_apply, hs2]
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_stk, State.updStk_apply, hs3]
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_apply]
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_apply, hK]
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_apply, hF]
  · simp +decide [u2, u1, s1, State.tPeek, State.updReg_apply, hT]
  · intro k hk1 hk2 hk3
    simp +decide [u2, u1, s1, State.tPeek, State.updReg_stk, State.updStk_apply, hk1, hk2, hk3]

theorem loopBody_one (main : Cmd) (below1 below2 X : List Glyph) (s : State)
    (hs1 : s.stk 1 = toks 1 ++ gA :: below1) (hs2 : s.stk 2 = gB :: below2) (hs3 : s.stk 3 = X)
    (hC : s.reg rCond = gA) (hK : s.reg rKC = gTok) (hF : s.reg rFC = Glyph.bit false)
    (hT : s.reg rTC = Glyph.bit true) :
    ∃ (s' : State) (c : ℕ), Eval main loopBody s s' c ∧ c ≤ 28 ∧
      s'.stk 1 = gA :: below1 ∧ s'.stk 2 = gB :: below2 ∧
      s'.stk 3 = Glyph.bit true :: X ∧ s'.reg rCond = gA ∧
      s'.reg rKC = gTok ∧ s'.reg rFC = Glyph.bit false ∧ s'.reg rTC = Glyph.bit true ∧
      (∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  let s1 : State := s.updReg rCond Glyph.eos
  let u1 : State := State.tPeek s1 1 rX1
  have e0 : Eval main (Cmd.set rCond Glyph.eos) s s1 1 := Eval.set rCond Glyph.eos s
  have ep1 : Eval main (Cmd.peek 1 rX1) s1 u1 1 := Eval.peek 1 rX1 s1
  have hs1s1 : s1.stk 1 = toks 1 ++ gA :: below1 := by simp [s1, State.updReg_stk, hs1]
  have hu1 : u1.reg rX1 = gTok := by
    simp [u1, State.tPeek, State.updReg_apply, hs1s1, toks_one]
  have hu1' : u1.reg rX1 ≠ gA := by rw [hu1]; exact gTok_ne_gA
  obtain ⟨h1, c1, hev1, hc1, hA, hB, hC3, hrIn, hK1, hF1, hT1, hrCond1, hoth1⟩ :=
    halve_eval main 1 2 gA (by decide) (by decide) (by decide) gTok_ne_gA 1 0 below1
      (gB :: below2) X u1
      (by simp [u1, State.tPeek, State.updReg_stk, hs1s1])
      (by simp [u1, State.tPeek, State.updReg_stk, s1, hs2])
      (by simp [u1, State.tPeek, State.updReg_stk, s1, hs3])
      (by simp +decide [u1, State.tPeek, State.updReg_apply, s1, hK])
      (by simp +decide [u1, State.tPeek, State.updReg_apply, s1, hF])
      (by simp +decide [u1, State.tPeek, State.updReg_apply, s1, hT])
  let v : State := h1.updReg rCond gA
  have eset : Eval main (Cmd.set rCond gA) h1 v 1 := Eval.set rCond gA h1
  have estep12 : Eval main step12 s1 v (1 + (c1 + 1 + 1)) :=
    Eval.seq ep1 (Eval.iteF hu1' (Eval.seq hev1 eset))
  -- second half-step: stack 2 holds gB :: below2, so it is empty and the step is skipped
  let u2 : State := State.tPeek v 2 rX1
  have ep2 : Eval main (Cmd.peek 2 rX1) v u2 1 := Eval.peek 2 rX1 v
  have hv2 : v.stk 2 = gB :: below2 := by
    simp [v, State.updReg_stk, hB, one_div_two]
  have hu2 : u2.reg rX1 = gB := by
    simp [u2, State.tPeek, State.updReg_apply, hv2]
  have esk2 : Eval main Cmd.skip u2 u2 1 := Eval.skip u2
  have estep21 : Eval main step21 v u2 3 :=
    Eval.seq ep2 (Eval.iteT hu2 esk2)
  have ebody : Eval main loopBody s u2 (1 + ((1 + (c1 + 1 + 1)) + 3)) :=
    Eval.seq e0 (Eval.seq estep12 estep21)
  have hv1 : v.stk 1 = gA :: below1 := by simp [v, State.updReg_stk, hA]
  have hv3 : v.stk 3 = Glyph.bit true :: X := by simp [v, State.updReg_stk, hC3]
  have hvC : v.reg rCond = gA := by simp [v, State.updReg_apply]
  have hvK : v.reg rKC = gTok := by simp +decide [v, State.updReg_apply, hK1]
  have hvF : v.reg rFC = Glyph.bit false := by simp +decide [v, State.updReg_apply, hF1]
  have hvT : v.reg rTC = Glyph.bit true := by simp +decide [v, State.updReg_apply, hT1]
  refine ⟨u2, 1 + ((1 + (c1 + 1 + 1)) + 3), ebody, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [u2, State.tPeek, State.updReg_stk, hv1]
  · simp +decide [u2, State.tPeek, State.updReg_stk, hv2]
  · simp +decide [u2, State.tPeek, State.updReg_stk, hv3]
  · simp +decide [u2, State.tPeek, State.updReg_apply, hvC]
  · simp +decide [u2, State.tPeek, State.updReg_apply, hvK]
  · simp +decide [u2, State.tPeek, State.updReg_apply, hvF]
  · simp +decide [u2, State.tPeek, State.updReg_apply, hvT]
  · intro k hk1 hk2 hk3
    rw [show u2.stk k = v.stk k by simp +decide [u2, State.tPeek, State.updReg_stk],
      show v.stk k = h1.stk k by simp [v, State.updReg_stk],
      show h1.stk k = u1.stk k by exact hoth1 k hk1 hk2 hk3]
    simp +decide [u1, State.tPeek, State.updReg_stk, s1, State.updStk_apply, hk1, hk2, hk3]

theorem loopBody_two (main : Cmd) (a : ℕ) (below1 below2 X : List Glyph) (s : State)
    (ha : 2 ≤ a)
    (hs1 : s.stk 1 = toks a ++ gA :: below1) (hs2 : s.stk 2 = gB :: below2) (hs3 : s.stk 3 = X)
    (hC : s.reg rCond = gA) (hK : s.reg rKC = gTok) (hF : s.reg rFC = Glyph.bit false)
    (hT : s.reg rTC = Glyph.bit true) :
    ∃ (s' : State) (c : ℕ), Eval main loopBody s s' c ∧
      c ≤ 9 * (a + 1) + 9 * (a / 2 + 1) + 40 ∧
      s'.stk 1 = toks (a / 4) ++ gA :: below1 ∧ s'.stk 2 = gB :: below2 ∧
      s'.stk 3 = Glyph.bit (a / 2).bodd :: Glyph.bit a.bodd :: X ∧
      s'.reg rCond = gA ∧ s'.reg rKC = gTok ∧ s'.reg rFC = Glyph.bit false ∧
      s'.reg rTC = Glyph.bit true ∧
      (∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  let s1 : State := s.updReg rCond Glyph.eos
  let u1 : State := State.tPeek s1 1 rX1
  have e0 : Eval main (Cmd.set rCond Glyph.eos) s s1 1 := Eval.set rCond Glyph.eos s
  have ep1 : Eval main (Cmd.peek 1 rX1) s1 u1 1 := Eval.peek 1 rX1 s1
  have hs1s1 : s1.stk 1 = toks a ++ gA :: below1 := by simp [s1, State.updReg_stk, hs1]
  have hu1 : u1.reg rX1 = gTok := by
    show (State.tPeek s1 1 rX1).reg rX1 = gTok
    exact tPeek_reg_eq s1 1 rX1 gTok (by rw [hs1s1]; exact toks_headD_ne (by omega) gA below1)
  have hu1' : u1.reg rX1 ≠ gA := by rw [hu1]; exact gTok_ne_gA
  obtain ⟨h1, c1, hev1, hc1, hA, hB, hC3, hrIn, hK1, hF1, hT1, hrCond1, hoth1⟩ :=
    halve_eval main 1 2 gA (by decide) (by decide) (by decide) gTok_ne_gA a 0 below1
      (gB :: below2) X u1
      (by simp [u1, State.tPeek, State.updReg_stk, hs1s1])
      (by simp [u1, State.tPeek, State.updReg_stk, s1, hs2])
      (by simp [u1, State.tPeek, State.updReg_stk, s1, hs3])
      (by simp +decide [u1, State.tPeek, State.updReg_apply, s1, hK])
      (by simp +decide [u1, State.tPeek, State.updReg_apply, s1, hF])
      (by simp +decide [u1, State.tPeek, State.updReg_apply, s1, hT])
  let v : State := h1.updReg rCond gA
  have eset : Eval main (Cmd.set rCond gA) h1 v 1 := Eval.set rCond gA h1
  have estep12 : Eval main step12 s1 v (1 + (c1 + 1 + 1)) :=
    Eval.seq ep1 (Eval.iteF hu1' (Eval.seq hev1 eset))
  have hv1 : v.stk 1 = gA :: below1 := by simp [v, State.updReg_stk, hA]
  have hv2 : v.stk 2 = toks (a / 2) ++ gB :: below2 := by
    simp [v, State.updReg_stk, hB]
  have hv3 : v.stk 3 = Glyph.bit a.bodd :: X := by simp [v, State.updReg_stk, hC3]
  have hvC : v.reg rCond = gA := by simp [v, State.updReg_apply]
  have hvK : v.reg rKC = gTok := by simp +decide [v, State.updReg_apply, hK1]
  have hvF : v.reg rFC = Glyph.bit false := by simp +decide [v, State.updReg_apply, hF1]
  have hvT : v.reg rTC = Glyph.bit true := by simp +decide [v, State.updReg_apply, hT1]
  -- second half-step: stack 2 carries a/2 ≥ 1 tokens
  let u2 : State := State.tPeek v 2 rX1
  have ep2 : Eval main (Cmd.peek 2 rX1) v u2 1 := Eval.peek 2 rX1 v
  have hu2 : u2.reg rX1 = gTok := by
    show (State.tPeek v 2 rX1).reg rX1 = gTok
    exact tPeek_reg_eq v 2 rX1 gTok (by rw [hv2]; exact toks_headD_ne (by omega) gB below2)
  have hu2' : u2.reg rX1 ≠ gB := by rw [hu2]; exact gTok_ne_gB
  obtain ⟨h2s, c2, hev2, hc2, hA2, hB2, hC32, hrIn2, hK2, hF2, hT2, hrCond2, hoth2⟩ :=
    halve_eval main 2 1 gB (by decide) (by decide) (by decide) gTok_ne_gB (a / 2) 0 below2
      (gA :: below1) (Glyph.bit a.bodd :: X) u2
      (by simp [u2, State.tPeek, State.updReg_stk, hv2])
      (by simp [u2, State.tPeek, State.updReg_stk, hv1])
      (by simp [u2, State.tPeek, State.updReg_stk, hv3])
      (by simp +decide [u2, State.tPeek, State.updReg_apply, hvK])
      (by simp +decide [u2, State.tPeek, State.updReg_apply, hvF])
      (by simp +decide [u2, State.tPeek, State.updReg_apply, hvT])
  let w : State := h2s.updReg rCond gA
  have eset2 : Eval main (Cmd.set rCond gA) h2s w 1 := Eval.set rCond gA h2s
  have estep21 : Eval main step21 v w (1 + (c2 + 1 + 1)) :=
    Eval.seq ep2 (Eval.iteF hu2' (Eval.seq hev2 eset2))
  have ebody : Eval main loopBody s w (1 + ((1 + (c1 + 1 + 1)) + (1 + (c2 + 1 + 1)))) :=
    Eval.seq e0 (Eval.seq estep12 estep21)
  have hw1 : w.stk 1 = toks ((a / 2) / 2) ++ gA :: below1 := by
    simp [w, State.updReg_stk, hB2]
  have hw2 : w.stk 2 = gB :: below2 := by simp [w, State.updReg_stk, hA2]
  have hw3 : w.stk 3 = Glyph.bit (a / 2).bodd :: Glyph.bit a.bodd :: X := by
    simp [w, State.updReg_stk, hC32]
  have hwC : w.reg rCond = gA := by simp [w, State.updReg_apply]
  have hwK : w.reg rKC = gTok := by simp +decide [w, State.updReg_apply, hK2]
  have hwF : w.reg rFC = Glyph.bit false := by simp +decide [w, State.updReg_apply, hF2]
  have hwT : w.reg rTC = Glyph.bit true := by simp +decide [w, State.updReg_apply, hT2]
  refine ⟨w, 1 + ((1 + (c1 + 1 + 1)) + (1 + (c2 + 1 + 1))), ebody, by omega,
    ?_, hw2, hw3, hwC, hwK, hwF, hwT, ?_⟩
  · rw [hw1, div2_div2]
  · intro k hk1 hk2 hk3
    rw [show w.stk k = h2s.stk k by simp [w, State.updReg_stk],
      show h2s.stk k = u2.stk k by exact hoth2 k hk2 hk1 hk3,
      show u2.stk k = v.stk k by simp +decide [u2, State.tPeek, State.updReg_stk],
      show v.stk k = h1.stk k by simp [v, State.updReg_stk],
      show h1.stk k = u1.stk k by exact hoth1 k hk1 hk2 hk3]
    simp +decide [u1, State.tPeek, State.updReg_stk, s1, State.updStk_apply, hk1, hk2, hk3]

/-! ## The outer loop -/

theorem loop_eval (main : Cmd) :
    ∀ (a : ℕ) (below1 below2 X : List Glyph) (s : State),
      s.stk 1 = toks a ++ gA :: below1 → s.stk 2 = gB :: below2 → s.stk 3 = X →
      s.reg rCond = gA → s.reg rKC = gTok → s.reg rFC = Glyph.bit false →
      s.reg rTC = Glyph.bit true →
      ∃ (s' : State) (c : ℕ), Eval main loopProg s s' c ∧ c ≤ 200 * (a + 1) ∧
        s'.stk 1 = gA :: below1 ∧ s'.stk 2 = gB :: below2 ∧
        s'.stk 3 = (a.bits).reverse.map Glyph.bit ++ X ∧
        (∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  intro a
  refine Nat.strong_induction_on a ?_
  intro n ih below1 below2 X s hs1 hs2 hs3 hC hK hF hT
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · obtain ⟨s', c', hev, hc, h1', h2', h3', hC', hK', hF', hT', hoth⟩ :=
        loopBody_zero main below1 below2 X s (by simpa using hs1) hs2 hs3 hC hK hF hT
      have hstop : s'.reg rCond ≠ gA := by rw [hC']; exact eos_ne_gA
      refine ⟨s', c' + 2, Eval.loopT hC hev (Eval.loopF hstop), by omega, h1', h2', ?_, ?_⟩
      · rw [h3', Nat.zero_bits]; simp
      · intro k hk1 hk2 hk3; exact hoth k hk1 hk2 hk3
    · obtain ⟨s', c', hev, hc, h1', h2', h3', hC', hK', hF', hT', hoth⟩ :=
        loopBody_one main below1 below2 X s hs1 hs2 hs3 hC hK hF hT
      obtain ⟨s'', c'', hev2, hc2, h1'', h2'', h3'', hoth2⟩ :=
        ih 0 (by omega) below1 below2 (Glyph.bit true :: X) s' h1' h2' h3' hC' hK' hF' hT'
      refine ⟨s'', c' + c'' + 1, Eval.loopT hC hev hev2, by omega, h1'', h2'', ?_, ?_⟩
      · rw [h3'', Nat.zero_bits, Nat.one_bits]
        simp
      · intro k hk1 hk2 hk3; rw [hoth2 k hk1 hk2 hk3]; exact hoth k hk1 hk2 hk3
  · obtain ⟨s', c', hev, hc, h1', h2', h3', hC', hK', hF', hT', hoth⟩ :=
      loopBody_two main n below1 below2 X s hn hs1 hs2 hs3 hC hK hF hT
    obtain ⟨s'', c'', hev2, hc2, h1'', h2'', h3'', hoth2⟩ :=
      ih (n / 4) (by omega) below1 below2 (Glyph.bit (n / 2).bodd :: Glyph.bit n.bodd :: X)
        s' h1' h2' h3' hC' hK' hF' hT'
    refine ⟨s'', c' + c'' + 1, Eval.loopT hC hev hev2, by omega, h1'', h2'', ?_, ?_⟩
    · rw [h3'', bits_reverse_map_eq n hn]
      simp
    · intro k hk1 hk2 hk3; rw [hoth2 k hk1 hk2 hk3]; exact hoth k hk1 hk2 hk3

end SizeHalve

open SizeHalve
open Work.IntLib.Size

/-- **The `sizeHalve` piece**: halve the unary counter `u` on stack 1, writing the bits of `u`
(most significant first) on stack 3 above a fresh marker `gC`, in time `O(u)`. -/
theorem sizeHalvePiece : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (u : ℕ)
    (below1 below2 below3 : List HvdH.Glyph) (s : HvdH.State),
  s.stk 1 = Work.IntLib.Size.toks u ++ Work.IntLib.Size.gA :: below1 → s.stk 2 = below2 →
  s.stk 3 = below3 →
  ∃ (s' : HvdH.State) (c : ℕ), HvdH.Eval main prog s s' c ∧ c ≤ K * (u + 1) ∧
    s'.stk 1 = Work.IntLib.Size.gA :: below1 ∧ s'.stk 2 = below2 ∧
    s'.stk 3 = (u.bits).reverse.map HvdH.Glyph.bit ++ Work.IntLib.Size.gC :: below3 ∧
    ∀ k : HvdH.Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k := by
  refine ⟨SizeHalve.prog, 250, ?_⟩
  intro main u below1 below2 below3 s hs1 hs2 hs3
  let t1 : State := s.updReg rMC gB
  let t2 : State := t1.updStk 2 (gB :: below2)
  let t3 : State := t2.updReg rSC gC
  let t4 : State := t3.updStk 3 (gC :: below3)
  let t5 : State := t4.updReg rKC gTok
  let t6 : State := t5.updReg rFC (Glyph.bit false)
  let t7 : State := t6.updReg rTC (Glyph.bit true)
  let t8 : State := t7.updReg rCond gA
  have e1 : Eval main (Cmd.set rMC gB) s t1 1 := Eval.set rMC gB s
  have e2 : Eval main (Cmd.push 2 rMC) t1 t2 1 := by
    have h : Eval main (Cmd.push 2 rMC) t1 (State.tPush t1 2 rMC) 1 := Eval.push 2 rMC t1
    have hreg : t1.reg rMC = gB := by simp [t1, State.updReg_apply]
    have hstk : t1.stk 2 = below2 := by simp [t1, State.updReg_stk, hs2]
    simpa [t2, State.tPush, hreg, hstk] using h
  have e3 : Eval main (Cmd.set rSC gC) t2 t3 1 := Eval.set rSC gC t2
  have e4 : Eval main (Cmd.push 3 rSC) t3 t4 1 := by
    have h : Eval main (Cmd.push 3 rSC) t3 (State.tPush t3 3 rSC) 1 := Eval.push 3 rSC t3
    have hreg : t3.reg rSC = gC := by simp [t3, State.updReg_apply]
    have hstk : t3.stk 3 = below3 := by
      simp +decide [t3, t2, t1, State.updReg_stk, State.updStk_apply, hs3]
    simpa [t4, State.tPush, hreg, hstk] using h
  have e5 : Eval main (Cmd.set rKC gTok) t4 t5 1 := Eval.set rKC gTok t4
  have e6 : Eval main (Cmd.set rFC (Glyph.bit false)) t5 t6 1 :=
    Eval.set rFC (Glyph.bit false) t5
  have e7 : Eval main (Cmd.set rTC (Glyph.bit true)) t6 t7 1 :=
    Eval.set rTC (Glyph.bit true) t6
  have e8 : Eval main (Cmd.set rCond gA) t7 t8 1 := Eval.set rCond gA t7
  have hevInit : Eval main initProg s t8 (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
      (Eval.seq e7 e8))))))
  have ht1 : t8.stk 1 = toks u ++ gA :: below1 := by
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_stk, State.updStk_apply, hs1]
  have ht2 : t8.stk 2 = gB :: below2 := by
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_stk, State.updStk_apply]
  have ht3 : t8.stk 3 = gC :: below3 := by
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_stk, State.updStk_apply]
  have htC : t8.reg rCond = gA := by simp [t8, State.updReg_apply]
  have htK : t8.reg rKC = gTok := by
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_apply, State.updReg_stk]
  have htF : t8.reg rFC = Glyph.bit false := by
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_apply, State.updReg_stk]
  have htT : t8.reg rTC = Glyph.bit true := by
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_apply, State.updReg_stk]
  have htFrame : ∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → t8.stk k = s.stk k := by
    intro k hk1 hk2 hk3
    simp +decide [t8, t7, t6, t5, t4, t3, t2, t1, State.updReg_stk, State.updStk_apply,
      hk1, hk2, hk3]
  obtain ⟨s2, c2, hevLoop, hc2, hl1, hl2, hl3, hlFrame⟩ :=
    loop_eval main u below1 below2 (gC :: below3) t8 ht1 ht2 ht3 htC htK htF htT
  let s3 : State := (s2.updStk 2 (s2.stk 2).tail).updReg rSC ((s2.stk 2).headD Glyph.eos)
  have epop : Eval main finishProg s2 s3 1 := by
    have h : Eval main (Cmd.pop 2 rSC) s2 (State.tPop s2 2 rSC) 1 := Eval.pop 2 rSC s2
    simpa [finishProg, s3, State.tPop] using h
  have hs2stk2 : s2.stk 2 = gB :: below2 := hl2
  have hf1 : s3.stk 1 = gA :: below1 := by
    simp +decide [s3, State.updReg_stk, State.updStk_apply, hs2stk2, hl1]
  have hf2 : s3.stk 2 = below2 := by
    simp +decide [s3, State.updReg_stk, State.updStk_apply, hs2stk2]
  have hf3 : s3.stk 3 = (u.bits).reverse.map Glyph.bit ++ gC :: below3 := by
    simp +decide [s3, State.updReg_stk, State.updStk_apply, hl3]
  have hfFrame : ∀ k : Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → s3.stk k = s.stk k := by
    intro k hk1 hk2 hk3
    rw [show s3.stk k = s2.stk k by
          simp +decide [s3, State.updReg_stk, State.updStk_apply, hk2],
      hlFrame k hk1 hk2 hk3]
    exact htFrame k hk1 hk2 hk3
  have hAll : Eval main prog s s3 ((1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) + (c2 + 1)) :=
    Eval.seq hevInit (Eval.seq hevLoop epop)
  exact ⟨s3, (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) + (c2 + 1), hAll, by omega,
    hf1, hf2, hf3, hfFrame⟩

end Work.IntLib
