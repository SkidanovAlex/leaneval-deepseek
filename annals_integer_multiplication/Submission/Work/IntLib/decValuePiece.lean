import Mathlib
import Submission.Work.IntLib.SizeShared
import Submission.Work.IntLib.eval_mvRevOnto

/-!
# `IntLib` piece `decValuePiece`: subtracting one from a positive integer value

A `WordR`-level program that replaces the value `int (n+1)` on top of the value stack by `int n`,
at cost `O(isz)`.

Encoding reminder: `(Val.int z).enc = [pos|neg] ++ bits(|z|) ++ [iend]`, the bits least
significant first (`Computability.encodeNat = Nat.bits`).  Since the argument is positive, the
sign glyph is `pos`; the bits of `n+1` are read off stack 0 one by one and the bits of `n` are
written on stack 1 with the borrow chain that "subtracts one": as long as the incoming borrow is
`true`, the bit is complemented, and a `true` bit clears the borrow.  Bits are written least
significant first, so the resulting number is correct; the only leading zero that can appear is
the (complemented) most significant bit of a power of two, which is stripped.  Finally the bits
are moved back onto stack 0 in correct order.

## Layout

1. pure bit-level layer: `decOutAux`, `stripFirstFalse`, `decBitsM` and the arithmetic fact
   `decBitsM bs = (ofBits bs - 1).bits` for canonical nonempty `bs`;
2. registers, glyphs and the program;
3. `Eval` lemmas for one loop step, the whole loop, and the leading-zero strip;
4. assembly of the `WordR` statement.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

/-! ## 1. Pure bit layer -/

/-- Output bits (least significant first) of the borrow chain subtracting one: with incoming
borrow `c`, bit `b` is complemented while the borrow is still `true`, and the borrow is cleared by
the first `true` bit. -/
def decOutAux (c : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => (if c then !b else b) :: decOutAux (c && !b) bs

theorem decOutAux_false (bs : List Bool) : decOutAux false bs = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [decOutAux, ih]

theorem decOutAux_true_true (bs : List Bool) : decOutAux true (true :: bs) = false :: bs := by
  simp [decOutAux, decOutAux_false]

theorem decOutAux_true_false (bs : List Bool) :
    decOutAux true (false :: bs) = true :: decOutAux true bs := by
  simp [decOutAux]

theorem decOutAux_length (c : Bool) (bs : List Bool) : (decOutAux c bs).length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [decOutAux, ih]

/-- Drop the first element of a list if it is `false` (the machine drops the top of stack 1 when
it is a `bit false` glyph). -/
def stripFirstFalse : List Bool → List Bool
  | [] => []
  | b :: bs => if b then b :: bs else bs

theorem stripFirstFalse_of_head_true {Q : List Bool} (h : Q.head? = some true) :
    stripFirstFalse Q = Q := by
  cases Q with
  | nil => simp at h
  | cons b bs =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp [stripFirstFalse]

theorem stripFirstFalse_append_true (Q : List Bool) :
    stripFirstFalse (Q ++ [true]) = stripFirstFalse Q ++ [true] := by
  cases Q with
  | nil => rfl
  | cons b bs => cases b <;> simp [stripFirstFalse]

theorem stripFirstFalse_length_le (Q : List Bool) : (stripFirstFalse Q).length ≤ Q.length := by
  cases Q with
  | nil => simp [stripFirstFalse]
  | cons b bs => cases b <;> simp [stripFirstFalse]

/-- The bit list (least significant first) produced by the decrement word. -/
def decBitsM (bs : List Bool) : List Bool :=
  (stripFirstFalse ((decOutAux true bs).reverse)).reverse

theorem decBitsM_true_nil : decBitsM [true] = [] := by
  simp [decBitsM, decOutAux, stripFirstFalse]

/-- Canonical bit lists are `[]` or end with a `true`. -/
theorem dvIsBits_iff' {xs : List Bool} : IsBits xs ↔ xs = [] ∨ ∃ ys, xs = ys ++ [true] := by
  rw [isBits_iff, List.getLast?_eq_some_iff]

theorem dvIsBits_of_cons {b : Bool} {bs : List Bool} (h : IsBits (b :: bs)) : IsBits bs := by
  rw [dvIsBits_iff'] at h ⊢
  rcases h with h | ⟨ys, hys⟩
  · simp at h
  · cases ys with
    | nil =>
      have h' : b = true ∧ bs = [] := by simpa using hys
      exact Or.inl h'.2
    | cons y ys' =>
      have h' : b = y ∧ bs = ys' ++ [true] := by simpa using hys
      exact Or.inr ⟨ys', h'.2⟩

theorem decBitsM_true_cons {bs : List Bool} (hne : bs ≠ []) (hb : IsBits bs) :
    decBitsM (true :: bs) = false :: bs := by
  have hhead : ((false :: bs).reverse).head? = some true := by
    obtain ⟨ys, rfl⟩ := (dvIsBits_iff'.mp hb).resolve_left hne
    simp
  rw [decBitsM, decOutAux_true_true, stripFirstFalse_of_head_true hhead, List.reverse_reverse]

theorem decBitsM_false_cons (bs : List Bool) :
    decBitsM (false :: bs) = true :: decBitsM bs := by
  rw [decBitsM, decOutAux_true_false, List.reverse_cons, stripFirstFalse_append_true,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
  rfl

/-- **Pure correctness of the bit-level decrement.** -/
theorem decBitsM_eq (bs : List Bool) (hb : IsBits bs) (hne : bs ≠ []) :
    decBitsM bs = (ofBits bs - 1).bits := by
  induction bs with
  | nil => exact absurd rfl hne
  | cons b bs ih =>
    have hb' : IsBits bs := dvIsBits_of_cons hb
    cases b with
    | true =>
      rcases eq_or_ne bs [] with h | hbs
      · subst h
        rw [decBitsM_true_nil]
        have h1 : ofBits [true] = 1 := by simp [ofBits]
        rw [h1, Nat.zero_bits]
      · rw [decBitsM_true_cons hbs hb']
        have hpos : ofBits bs ≠ 0 := fun h0 => hbs ((ofBits_eq_zero_iff_of_isBits bs hb').mp h0)
        have harith : ofBits (true :: bs) - 1 = 2 * ofBits bs := by
          rw [ofBits_cons, Bool.toNat_true]
          omega
        rw [harith, Nat.bit0_bits (ofBits bs) hpos, bits_ofBits_of_isBits bs hb']
    | false =>
      have hne' : bs ≠ [] := by
        intro h; subst h
        rw [isBits_iff] at hb
        rcases hb with h | h <;> simp at h
      have hpos : 1 ≤ ofBits bs := by
        have h0 : ofBits bs ≠ 0 := fun h0 => hne' ((ofBits_eq_zero_iff_of_isBits bs hb').mp h0)
        omega
      rw [decBitsM_false_cons, ih hb' hne']
      have harith : ofBits (false :: bs) - 1 = 2 * (ofBits bs - 1) + 1 := by
        rw [ofBits_cons, Bool.toNat_false, Nat.zero_add]
        omega
      rw [harith, Nat.bit1_bits]

/-! ## 2. Registers, glyphs, program -/

/-- Frame marker used on stack 1. -/
abbrev dvMark : Glyph := .mk 1
/-- Loop-stop flag. -/
abbrev dvStop : Glyph := .mk 0

theorem dvMark_ne_eos : dvMark ≠ Glyph.eos := by decide
theorem dvStop_ne_eos : dvStop ≠ Glyph.eos := by decide
theorem bit_ne_dvMark (b : Bool) : Glyph.bit b ≠ dvMark := by cases b <;> decide
theorem dvMark_ne_bit (b : Bool) : dvMark ≠ Glyph.bit b := fun h => bit_ne_dvMark b h.symm
theorem dvMark_ne_iend : dvMark ≠ Glyph.iend := by decide
theorem dvMark_ne_pos : dvMark ≠ Glyph.pos := by decide
theorem dvBit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := by cases b <;> decide
theorem iend_ne_bit (b : Bool) : Glyph.iend ≠ Glyph.bit b := fun h => dvBit_ne_iend b h.symm

abbrev dvTest : Reg := 0
abbrev dvGlyph : Reg := 1
abbrev dvCarry : Reg := 2
abbrev dvOut : Reg := 3
abbrev dvSign : Reg := 4
abbrev dvPeek : Reg := 5
abbrev dvMarkR : Reg := 6

theorem dvTest_ne_dvGlyph : dvTest ≠ dvGlyph := by decide
theorem dvTest_ne_dvCarry : dvTest ≠ dvCarry := by decide
theorem dvTest_ne_dvOut : dvTest ≠ dvOut := by decide
theorem dvTest_ne_dvSign : dvTest ≠ dvSign := by decide
theorem dvTest_ne_dvPeek : dvTest ≠ dvPeek := by decide
theorem dvTest_ne_dvMarkR : dvTest ≠ dvMarkR := by decide
theorem dvGlyph_ne_dvCarry : dvGlyph ≠ dvCarry := by decide
theorem dvGlyph_ne_dvOut : dvGlyph ≠ dvOut := by decide
theorem dvGlyph_ne_dvSign : dvGlyph ≠ dvSign := by decide
theorem dvGlyph_ne_dvPeek : dvGlyph ≠ dvPeek := by decide
theorem dvGlyph_ne_dvMarkR : dvGlyph ≠ dvMarkR := by decide
theorem dvCarry_ne_dvGlyph : dvCarry ≠ dvGlyph := by decide
theorem dvCarry_ne_dvOut : dvCarry ≠ dvOut := by decide
theorem dvCarry_ne_dvSign : dvCarry ≠ dvSign := by decide
theorem dvCarry_ne_dvPeek : dvCarry ≠ dvPeek := by decide
theorem dvCarry_ne_dvMarkR : dvCarry ≠ dvMarkR := by decide
theorem dvOut_ne_dvSign : dvOut ≠ dvSign := by decide
theorem dvOut_ne_dvPeek : dvOut ≠ dvPeek := by decide
theorem dvOut_ne_dvMarkR : dvOut ≠ dvMarkR := by decide
theorem dvSign_ne_dvPeek : dvSign ≠ dvPeek := by decide
theorem dvSign_ne_dvMarkR : dvSign ≠ dvMarkR := by decide
theorem dvPeek_ne_dvMarkR : dvPeek ≠ dvMarkR := by decide
theorem dvCarry_ne_dvTest : dvCarry ≠ dvTest := fun h => dvTest_ne_dvCarry h.symm
theorem dvGlyph_ne_dvTest : dvGlyph ≠ dvTest := fun h => dvTest_ne_dvGlyph h.symm
theorem dvOut_ne_dvTest : dvOut ≠ dvTest := fun h => dvTest_ne_dvOut h.symm
theorem dvSign_ne_dvTest : dvSign ≠ dvTest := fun h => dvTest_ne_dvSign h.symm
theorem dvPeek_ne_dvTest : dvPeek ≠ dvTest := fun h => dvTest_ne_dvPeek h.symm
theorem dvMarkR_ne_dvTest : dvMarkR ≠ dvTest := fun h => dvTest_ne_dvMarkR h.symm
theorem dvOut_ne_dvCarry : dvOut ≠ dvCarry := fun h => dvCarry_ne_dvOut h.symm
theorem dvSign_ne_dvCarry : dvSign ≠ dvCarry := fun h => dvCarry_ne_dvSign h.symm
theorem dvPeek_ne_dvCarry : dvPeek ≠ dvCarry := fun h => dvCarry_ne_dvPeek h.symm
theorem dvMarkR_ne_dvCarry : dvMarkR ≠ dvCarry := fun h => dvCarry_ne_dvMarkR h.symm
theorem dvOut_ne_dvGlyph : dvOut ≠ dvGlyph := fun h => dvGlyph_ne_dvOut h.symm
theorem dvSign_ne_dvGlyph : dvSign ≠ dvGlyph := fun h => dvGlyph_ne_dvSign h.symm
theorem dvPeek_ne_dvGlyph : dvPeek ≠ dvGlyph := fun h => dvGlyph_ne_dvPeek h.symm
theorem dvMarkR_ne_dvGlyph : dvMarkR ≠ dvGlyph := fun h => dvGlyph_ne_dvMarkR h.symm
theorem dvSign_ne_dvOut : dvSign ≠ dvOut := fun h => dvOut_ne_dvSign h.symm
theorem dvPeek_ne_dvOut : dvPeek ≠ dvOut := fun h => dvOut_ne_dvPeek h.symm
theorem dvMarkR_ne_dvOut : dvMarkR ≠ dvOut := fun h => dvOut_ne_dvMarkR h.symm
theorem dvPeek_ne_dvSign : dvPeek ≠ dvSign := fun h => dvSign_ne_dvPeek h.symm
theorem dvMarkR_ne_dvSign : dvMarkR ≠ dvSign := fun h => dvSign_ne_dvMarkR h.symm
theorem dvMarkR_ne_dvPeek : dvMarkR ≠ dvPeek := fun h => dvPeek_ne_dvMarkR h.symm

/-- Output glyph of one step with incoming borrow `c` and input bit `b`. -/
def dvOutGlyph (c b : Bool) : Glyph := Glyph.bit (if c then !b else b)

/-- The borrow after processing bit `b` with incoming borrow `c`. -/
def dvCarryG (c b : Bool) : Glyph := Glyph.bit (c && !b)

/-- Flip branch: complement the bit, push it, and clear the borrow if the bit was `true`. -/
def dvFlip : Cmd :=
  .seq (.ite dvGlyph (Glyph.bit true) (.set dvOut (Glyph.bit false)) (.set dvOut (Glyph.bit true)))
    (.seq (.push 1 dvOut) (.ite dvGlyph (Glyph.bit true) (.set dvCarry (Glyph.bit false)) .skip))

/-- Copy branch: the bit is pushed unchanged. -/
def dvCopy : Cmd := .push 1 dvGlyph

/-- Stop branch: push the closing `iend` back and set the stop flag. -/
def dvStopB : Cmd := .seq (.push 0 dvGlyph) (.set dvTest dvStop)

def dvCarrier : Cmd := .ite dvCarry (Glyph.bit true) dvFlip dvCopy

def dvCont : Cmd := .seq dvCarrier (.set dvTest Glyph.eos)

def dvStepBody : Cmd := .seq (.pop 0 dvGlyph) (.ite dvGlyph Glyph.iend dvStopB dvCont)

def dvLoop : Cmd := .loop dvTest Glyph.eos dvStepBody

/-- Drop the top glyph of stack 1 if it is a `bit false` (leading zero of the result). -/
def dvStrip : Cmd := .seq (.peek 1 dvPeek) (.ite dvPeek (Glyph.bit false) (.pop 1 dvPeek) .skip)

def dvProg : Cmd :=
  .seq (.pop 0 dvSign)
    (.seq (.set dvMarkR dvMark)
      (.seq (.push 1 dvMarkR)
        (.seq (.set dvCarry (Glyph.bit true))
          (.seq (.set dvTest Glyph.eos)
            (.seq dvLoop
              (.seq dvStrip
                (.seq (mvRevOnto 1 dvMark 0 dvTest)
                  (.seq (.set dvSign Glyph.pos) (.push 0 dvSign)))))))))

/-! ## 3. `Eval` lemmas -/

theorem dvEval_pop (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Eval main (.pop k r) s (State.tPop s k r) 1 := Eval.pop k r s

theorem dvEval_push (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Eval main (.push k r) s (State.tPush s k r) 1 := Eval.push k r s

theorem dvEval_set (main : Cmd) (r : Reg) (g : Glyph) (s : State) :
    Eval main (.set r g) s (State.tSet s r g) 1 := Eval.set r g s

theorem dvEval_peek (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Eval main (.peek k r) s (State.tPeek s k r) 1 := Eval.peek k r s

theorem dvEval_seq {main : Cmd} {c₁ c₂ : Cmd} {s₁ s₂ s₃ : State} {n₁ n₂ : ℕ}
    (h₁ : Eval main c₁ s₁ s₂ n₁) (h₂ : Eval main c₂ s₂ s₃ n₂) :
    Eval main (.seq c₁ c₂) s₁ s₃ (n₁ + n₂) := Eval.seq h₁ h₂

theorem dvEval_iteT {main : Cmd} {r : Reg} {c : Glyph} {c₁ c₂ : Cmd} {s s' : State} {n : ℕ}
    (h : s.reg r = c) (h₁ : Eval main c₁ s s' n) :
    Eval main (.ite r c c₁ c₂) s s' (n + 1) := Eval.iteT h h₁

theorem dvEval_iteF {main : Cmd} {r : Reg} {c : Glyph} {c₁ c₂ : Cmd} {s s' : State} {n : ℕ}
    (h : s.reg r ≠ c) (h₁ : Eval main c₂ s s' n) :
    Eval main (.ite r c c₁ c₂) s s' (n + 1) := Eval.iteF h h₁

/-- One "continue" step of the loop body. -/
theorem dvStep_cont (main : Cmd) (s : State) (c b : Bool) (rest : List Glyph)
    (h0 : s.stk 0 = Glyph.bit b :: rest) (hC : s.reg dvCarry = Glyph.bit c)
    (hT : s.reg dvTest = Glyph.eos) :
    ∃ (s' : State) (n : ℕ), Eval main dvStepBody s s' n ∧ n ≤ 10 ∧
      s'.stk 0 = rest ∧ s'.stk 1 = dvOutGlyph c b :: s.stk 1 ∧
      s'.reg dvCarry = dvCarryG c b ∧ s'.reg dvTest = Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  let u1 : State := State.tPop s 0 dvGlyph
  have e1 : Eval main (.pop 0 dvGlyph) s u1 1 := dvEval_pop main 0 dvGlyph s
  have h1g : u1.reg dvGlyph = Glyph.bit b := by simp [u1, State.tPop, h0]
  have h1c : u1.reg dvCarry = Glyph.bit c := by
    simp [u1, State.tPop, hC, dvCarry_ne_dvGlyph]
  have h1t : u1.reg dvTest = Glyph.eos := by simp [u1, State.tPop, hT, dvTest_ne_dvGlyph]
  have h1s0 : u1.stk 0 = rest := by simp [u1, State.tPop, h0]
  have h1s1 : u1.stk 1 = s.stk 1 := by simp [u1, State.tPop]
  have h1oth : ∀ k : Stk, k ≠ 0 → u1.stk k = s.stk k := by
    intro k hk; simp [u1, State.tPop, hk]
  have hOut : u1.reg dvGlyph ≠ Glyph.iend := by rw [h1g]; exact dvBit_ne_iend b
  cases c with
  | false =>
    have hc : u1.reg dvCarry ≠ Glyph.bit true := by rw [h1c]; decide
    cases b with
    | false =>
      let u2 : State := State.tPush u1 1 dvGlyph
      let u3 : State := State.tSet u2 dvTest Glyph.eos
      have e2 : Eval main dvCopy u1 u2 1 := dvEval_push main 1 dvGlyph u1
      have e3 : Eval main (.set dvTest Glyph.eos) u2 u3 1 := dvEval_set main dvTest Glyph.eos u2
      have eC : Eval main dvCarrier u1 u2 2 := dvEval_iteF hc e2
      have eCt : Eval main dvCont u1 u3 3 := dvEval_seq eC e3
      have eIt : Eval main (.ite dvGlyph Glyph.iend dvStopB dvCont) u1 u3 4 :=
        dvEval_iteF hOut eCt
      refine ⟨u3, 5, dvEval_seq e1 eIt, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
      · simp [u3, u2, State.tSet, State.tPush, h1s0]
      · simp [u3, u2, State.tSet, State.tPush, dvOutGlyph, h1g, h1s1]
      · simp [u3, u2, State.tSet, State.tPush, dvCarryG, h1c, dvCarry_ne_dvTest]
      · simp [u3, State.tSet]
      · intro k hk0 hk1
        simp [u3, u2, State.tSet, State.tPush, hk0, hk1, h1oth k hk0]
    | true =>
      let u2 : State := State.tPush u1 1 dvGlyph
      let u3 : State := State.tSet u2 dvTest Glyph.eos
      have e2 : Eval main dvCopy u1 u2 1 := dvEval_push main 1 dvGlyph u1
      have e3 : Eval main (.set dvTest Glyph.eos) u2 u3 1 := dvEval_set main dvTest Glyph.eos u2
      have eC : Eval main dvCarrier u1 u2 2 := dvEval_iteF hc e2
      have eCt : Eval main dvCont u1 u3 3 := dvEval_seq eC e3
      have eIt : Eval main (.ite dvGlyph Glyph.iend dvStopB dvCont) u1 u3 4 :=
        dvEval_iteF hOut eCt
      refine ⟨u3, 5, dvEval_seq e1 eIt, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
      · simp [u3, u2, State.tSet, State.tPush, h1s0]
      · simp [u3, u2, State.tSet, State.tPush, dvOutGlyph, h1g, h1s1]
      · simp [u3, u2, State.tSet, State.tPush, dvCarryG, h1c, dvCarry_ne_dvTest]
      · simp [u3, State.tSet]
      · intro k hk0 hk1
        simp [u3, u2, State.tSet, State.tPush, hk0, hk1, h1oth k hk0]
  | true =>
    have hc : u1.reg dvCarry = Glyph.bit true := h1c
    cases b with
    | false =>
      -- flip branch, bit false
      let w1 : State := State.tSet u1 dvOut (Glyph.bit true)
      let w2 : State := State.tPush w1 1 dvOut
      let u3 : State := State.tSet w2 dvTest Glyph.eos
      have e2 : Eval main (.set dvOut (Glyph.bit true)) u1 w1 1 :=
        dvEval_set main dvOut (Glyph.bit true) u1
      have h2g : u1.reg dvGlyph ≠ Glyph.bit true := by rw [h1g]; decide
      have e3 : Eval main (.ite dvGlyph (Glyph.bit true) (.set dvOut (Glyph.bit false))
          (.set dvOut (Glyph.bit true))) u1 w1 2 := dvEval_iteF h2g e2
      have e4 : Eval main (.push 1 dvOut) w1 w2 1 := dvEval_push main 1 dvOut w1
      have h4g : w2.reg dvGlyph ≠ Glyph.bit true := by
        rw [show w2.reg dvGlyph = u1.reg dvGlyph from by
          simp [w2, w1, State.tPush, State.tSet, dvGlyph_ne_dvOut]]
        rw [h1g]; decide
      have e5 : Eval main (.ite dvGlyph (Glyph.bit true) (.set dvCarry (Glyph.bit false))
          .skip) w2 w2 2 := dvEval_iteF h4g (Eval.skip w2)
      have eFlip : Eval main dvFlip u1 w2 5 := dvEval_seq e3 (dvEval_seq e4 e5)
      have eC : Eval main dvCarrier u1 w2 6 := dvEval_iteT hc eFlip
      have e6 : Eval main (.set dvTest Glyph.eos) w2 u3 1 := dvEval_set main dvTest Glyph.eos w2
      have eCt : Eval main dvCont u1 u3 7 := dvEval_seq eC e6
      have eIt : Eval main (.ite dvGlyph Glyph.iend dvStopB dvCont) u1 u3 8 :=
        dvEval_iteF hOut eCt
      refine ⟨u3, 9, dvEval_seq e1 eIt, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
      · simp [u3, w2, w1, State.tSet, State.tPush, h1s0]
      · simp [u3, w2, w1, State.tSet, State.tPush, dvOutGlyph, h1g, h1s1]
      · simp [u3, w2, w1, State.tSet, State.tPush, dvCarryG, h1c, dvCarry_ne_dvOut,
          dvCarry_ne_dvTest]
      · simp [u3, State.tSet]
      · intro k hk0 hk1
        simp [u3, w2, w1, State.tSet, State.tPush, hk0, hk1, h1oth k hk0]
    | true =>
      -- flip branch, bit true
      let w1 : State := State.tSet u1 dvOut (Glyph.bit false)
      let w2 : State := State.tPush w1 1 dvOut
      let w3 : State := State.tSet w2 dvCarry (Glyph.bit false)
      let u3 : State := State.tSet w3 dvTest Glyph.eos
      have e2 : Eval main (.set dvOut (Glyph.bit false)) u1 w1 1 :=
        dvEval_set main dvOut (Glyph.bit false) u1
      have h2g : u1.reg dvGlyph = Glyph.bit true := h1g
      have e3 : Eval main (.ite dvGlyph (Glyph.bit true) (.set dvOut (Glyph.bit false))
          (.set dvOut (Glyph.bit true))) u1 w1 2 := dvEval_iteT h2g e2
      have e4 : Eval main (.push 1 dvOut) w1 w2 1 := dvEval_push main 1 dvOut w1
      have h4g : w2.reg dvGlyph = Glyph.bit true := by
        rw [show w2.reg dvGlyph = u1.reg dvGlyph from by
          simp [w2, w1, State.tPush, State.tSet, dvGlyph_ne_dvOut]]
        exact h1g
      have e5 : Eval main (.ite dvGlyph (Glyph.bit true) (.set dvCarry (Glyph.bit false))
          .skip) w2 w3 2 := dvEval_iteT h4g (dvEval_set main dvCarry (Glyph.bit false) w2)
      have eFlip : Eval main dvFlip u1 w3 5 := dvEval_seq e3 (dvEval_seq e4 e5)
      have eC : Eval main dvCarrier u1 w3 6 := dvEval_iteT hc eFlip
      have e6 : Eval main (.set dvTest Glyph.eos) w3 u3 1 := dvEval_set main dvTest Glyph.eos w3
      have eCt : Eval main dvCont u1 u3 7 := dvEval_seq eC e6
      have eIt : Eval main (.ite dvGlyph Glyph.iend dvStopB dvCont) u1 u3 8 :=
        dvEval_iteF hOut eCt
      refine ⟨u3, 9, dvEval_seq e1 eIt, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
      · simp [u3, w3, w2, w1, State.tSet, State.tPush, h1s0]
      · simp [u3, w3, w2, w1, State.tSet, State.tPush, dvOutGlyph, h1g, h1s1]
      · simp [u3, w3, w2, w1, State.tSet, State.tPush, dvCarryG, h1c, dvCarry_ne_dvOut,
          dvCarry_ne_dvTest]
      · simp [u3, State.tSet]
      · intro k hk0 hk1
        simp [u3, w3, w2, w1, State.tSet, State.tPush, hk0, hk1, h1oth k hk0]

/-- The "stop" step of the loop body (the closing `iend` is on top of stack 0). -/
theorem dvStep_stop (main : Cmd) (s : State) (below0 : List Glyph)
    (h0 : s.stk 0 = Glyph.iend :: below0) (hT : s.reg dvTest = Glyph.eos) :
    ∃ (s' : State) (n : ℕ), Eval main dvStepBody s s' n ∧ n ≤ 5 ∧
      s'.stk 0 = Glyph.iend :: below0 ∧ s'.stk 1 = s.stk 1 ∧
      s'.reg dvTest = dvStop ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  let u1 : State := State.tPop s 0 dvGlyph
  have e1 : Eval main (.pop 0 dvGlyph) s u1 1 := dvEval_pop main 0 dvGlyph s
  have h1g : u1.reg dvGlyph = Glyph.iend := by simp [u1, State.tPop, h0]
  have h1s0 : u1.stk 0 = below0 := by simp [u1, State.tPop, h0]
  let u2 : State := State.tPush u1 0 dvGlyph
  let u3 : State := State.tSet u2 dvTest dvStop
  have e2 : Eval main (.push 0 dvGlyph) u1 u2 1 := dvEval_push main 0 dvGlyph u1
  have e3 : Eval main (.set dvTest dvStop) u2 u3 1 := dvEval_set main dvTest dvStop u2
  have eIt : Eval main (.ite dvGlyph Glyph.iend dvStopB dvCont) u1 u3 3 :=
    dvEval_iteT h1g (dvEval_seq e2 e3)
  have hstk0 : u3.stk 0 = u1.reg dvGlyph :: u1.stk 0 := by
    simp [u3, u2, State.tSet, State.tPush]
  refine ⟨u3, 4, dvEval_seq e1 eIt, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [hstk0, h1g, h1s0]
  · simp [u3, u2, u1, State.tSet, State.tPush, State.tPop]
  · simp [u3, State.tSet]
  · intro k hk0 hk1
    simp [u3, u2, u1, State.tSet, State.tPush, State.tPop, hk0, hk1]

/-- **The transformation loop**: reads the bits of `bs` off stack 0 (down to the closing `iend`)
and pushes the decremented bits (least significant first, so reversed on stack 1) above `acc`.
`acc` is what is already on stack 1 above the frame marker; the closing `iend` of stack 0 is left
in place. -/
theorem dvLoop_eval (main : Cmd) (bs : List Bool) (c : Bool) (acc below0 below1 : List Glyph)
    (s : State)
    (h0 : s.stk 0 = bs.map Glyph.bit ++ [Glyph.iend] ++ below0)
    (h1 : s.stk 1 = acc ++ below1)
    (hC : s.reg dvCarry = Glyph.bit c) (hT : s.reg dvTest = Glyph.eos) :
    ∃ (s' : State) (n : ℕ), Eval main dvLoop s s' n ∧ n ≤ 11 * (bs.length + 1) ∧
      s'.stk 0 = [Glyph.iend] ++ below0 ∧
      s'.stk 1 = (decOutAux c bs).reverse.map Glyph.bit ++ acc ++ below1 ∧
      s'.reg dvTest ≠ Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  induction bs generalizing acc s c with
  | nil =>
    have h0' : s.stk 0 = Glyph.iend :: below0 := by simpa using h0
    obtain ⟨s', n', hev, hn, hs0, hs1, hreg, hoth⟩ := dvStep_stop main s below0 h0' hT
    have hstop : s'.reg dvTest ≠ Glyph.eos := by rw [hreg]; exact dvStop_ne_eos
    refine ⟨s', n' + 1 + 1, Eval.loopT hT hev (Eval.loopF hstop), ?_, ?_, ?_, hstop, hoth⟩
    · omega
    · simpa using hs0
    · rw [hs1, h1]; simp [decOutAux]
  | cons b bs ih =>
    have h0' : s.stk 0 = Glyph.bit b :: (bs.map Glyph.bit ++ [Glyph.iend] ++ below0) := by
      simpa using h0
    obtain ⟨s2, n2, hev2, hn2, hs20, hs21, hreg2, hregt2, hoth2⟩ :=
      dvStep_cont main s c b (bs.map Glyph.bit ++ [Glyph.iend] ++ below0) h0' hC hT
    have h1' : s2.stk 1 = (dvOutGlyph c b :: acc) ++ below1 := by
      rw [hs21, h1]; rfl
    obtain ⟨s3, n3, hev3, hn3, hs30, hs31, hregt3, hoth3⟩ :=
      ih (acc := dvOutGlyph c b :: acc) (s := s2) (c := c && !b) (by simpa using hs20) h1'
        hreg2 hregt2
    have hkey : (decOutAux (c && !b) bs).reverse.map Glyph.bit ++
        (dvOutGlyph c b :: acc) ++ below1 =
        (decOutAux c (b :: bs)).reverse.map Glyph.bit ++ acc ++ below1 := by
      rw [show decOutAux c (b :: bs) =
          (if c then !b else b) :: decOutAux (c && !b) bs from rfl]
      simp [dvOutGlyph, List.reverse_cons, List.map_append, List.append_assoc]
    refine ⟨s3, n2 + n3 + 1, Eval.loopT hT hev2 hev3, ?_, ?_, ?_, hregt3, ?_⟩
    · have h2 := hn2
      have h3 := hn3
      simp only [List.length_cons] at h3 ⊢
      omega
    · simpa using hs30
    · rw [hs31, hkey]
    · intro k hk0 hk1
      rw [hoth3 k hk0 hk1, hoth2 k hk0 hk1]

/-- **The leading-zero strip**: if stack 1 is `Q.map bit ++ acc` with `acc` not starting with a
`bit false`, the program drops the first glyph of the region when it is a `bit false`. -/
theorem dvStrip_eval (main : Cmd) (Q : List Bool) (acc : List Glyph) (s : State)
    (hacc : acc.headD Glyph.eos ≠ Glyph.bit false)
    (h1 : s.stk 1 = Q.map Glyph.bit ++ acc) :
    ∃ (s' : State) (n : ℕ), Eval main dvStrip s s' n ∧ n ≤ 4 ∧
      s'.stk 1 = (stripFirstFalse Q).map Glyph.bit ++ acc ∧
      (∀ k : Stk, k ≠ 1 → s'.stk k = s.stk k) := by
  cases Q with
  | nil =>
    have hpeek : (State.tPeek s 1 dvPeek).reg dvPeek = acc.headD Glyph.eos := by
      rw [show (State.tPeek s 1 dvPeek).reg dvPeek = (s.stk 1).headD Glyph.eos from rfl, h1]
      rfl
    have hne : (State.tPeek s 1 dvPeek).reg dvPeek ≠ Glyph.bit false := by
      rw [hpeek]; exact hacc
    have e1 : Eval main (.peek 1 dvPeek) s (State.tPeek s 1 dvPeek) 1 := dvEval_peek main 1 dvPeek s
    have e2 : Eval main (.ite dvPeek (Glyph.bit false) (.pop 1 dvPeek) .skip)
        (State.tPeek s 1 dvPeek) (State.tPeek s 1 dvPeek) 2 :=
      dvEval_iteF hne (Eval.skip _)
    refine ⟨State.tPeek s 1 dvPeek, 3, dvEval_seq e1 e2, by norm_num, ?_, ?_⟩
    · rw [show (State.tPeek s 1 dvPeek).stk 1 = s.stk 1 from rfl, h1]
      simp [stripFirstFalse]
    · intro k hk; rfl
  | cons b bs =>
    have hpeek : (State.tPeek s 1 dvPeek).reg dvPeek = Glyph.bit b := by
      rw [show (State.tPeek s 1 dvPeek).reg dvPeek = (s.stk 1).headD Glyph.eos from rfl, h1]
      simp
    have e1 : Eval main (.peek 1 dvPeek) s (State.tPeek s 1 dvPeek) 1 := dvEval_peek main 1 dvPeek s
    cases b with
    | false =>
      have hpeek' : (State.tPeek s 1 dvPeek).reg dvPeek = Glyph.bit false := hpeek
      have e2 : Eval main (.pop 1 dvPeek) (State.tPeek s 1 dvPeek)
          (State.tPop (State.tPeek s 1 dvPeek) 1 dvPeek) 1 :=
        dvEval_pop main 1 dvPeek (State.tPeek s 1 dvPeek)
      have e3 : Eval main (.ite dvPeek (Glyph.bit false) (.pop 1 dvPeek) .skip)
          (State.tPeek s 1 dvPeek) (State.tPop (State.tPeek s 1 dvPeek) 1 dvPeek) 2 :=
        dvEval_iteT hpeek' e2
      refine ⟨State.tPop (State.tPeek s 1 dvPeek) 1 dvPeek, 3, dvEval_seq e1 e3, by norm_num,
        ?_, ?_⟩
      · rw [show (State.tPop (State.tPeek s 1 dvPeek) 1 dvPeek).stk 1
            = ((State.tPeek s 1 dvPeek).stk 1).tail from rfl,
          show (State.tPeek s 1 dvPeek).stk 1 = s.stk 1 from rfl, h1]
        simp [stripFirstFalse]
      · intro k hk
        rw [show (State.tPop (State.tPeek s 1 dvPeek) 1 dvPeek).stk k
            = (State.tPeek s 1 dvPeek).stk k from by simp [State.tPop, State.updStk_apply, hk]]
        rfl
    | true =>
      have hpeek' : (State.tPeek s 1 dvPeek).reg dvPeek ≠ Glyph.bit false := by
        rw [hpeek]; decide
      have e3 : Eval main (.ite dvPeek (Glyph.bit false) (.pop 1 dvPeek) .skip)
          (State.tPeek s 1 dvPeek) (State.tPeek s 1 dvPeek) 2 :=
        dvEval_iteF hpeek' (Eval.skip _)
      refine ⟨State.tPeek s 1 dvPeek, 3, dvEval_seq e1 e3, by norm_num, ?_, ?_⟩
      · rw [show (State.tPeek s 1 dvPeek).stk 1 = s.stk 1 from rfl, h1]
        simp [stripFirstFalse]
      · intro k hk; rfl

/-! ## 4. Assembly of the `WordR` statement -/

theorem decValuePiece : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd), HvdH.WordR main prog
  (fun vs => ∃ (n : ℕ) (rest : List HvdH.Val), vs = HvdH.Val.int (n + 1) :: rest)
  (fun vs out => ∃ (n : ℕ) (rest : List HvdH.Val), vs = HvdH.Val.int (n + 1) :: rest ∧ out = HvdH.Val.int n :: rest)
  (fun vs => K * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) := by
  refine ⟨dvProg, 100, ?_⟩
  intro main vs hpre s R hR
  obtain ⟨n, rest, rfl⟩ := hpre
  -- stack 0 in glyph form
  have hnz : (↑n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have hR0 : s.stk 0 = Glyph.pos :: (Computability.encodeNat (n + 1)).map Glyph.bit ++
      [Glyph.iend] ++ (encs rest ++ R) := by
    rw [hR, Work.Kernel.encs_cons, Size.enc_int_pos (by positivity : (0 : ℤ) ≤ (↑n + 1 : ℤ)),
      hnz, Int.natAbs_natCast]
    simp [List.append_assoc]
  -- prologue
  let s1 : State := State.tPop s 0 dvSign
  have e1 : Eval main (.pop 0 dvSign) s s1 1 := dvEval_pop main 0 dvSign s
  have hs1_0 : s1.stk 0 = (Computability.encodeNat (n + 1)).map Glyph.bit ++ [Glyph.iend] ++
      (encs rest ++ R) := by
    simp [s1, State.tPop, hR0]
  have hs1_1 : s1.stk 1 = s.stk 1 := by simp [s1, State.tPop]
  have hs1_oth : ∀ k : Stk, k ≠ 0 → s1.stk k = s.stk k := by
    intro k hk; simp [s1, State.tPop, hk]
  let s2 : State := State.tSet s1 dvMarkR dvMark
  let s3 : State := State.tPush s2 1 dvMarkR
  let s4 : State := State.tSet s3 dvCarry (Glyph.bit true)
  let s5 : State := State.tSet s4 dvTest Glyph.eos
  have e2 : Eval main (.set dvMarkR dvMark) s1 s2 1 := dvEval_set main dvMarkR dvMark s1
  have e3 : Eval main (.push 1 dvMarkR) s2 s3 1 := dvEval_push main 1 dvMarkR s2
  have e4 : Eval main (.set dvCarry (Glyph.bit true)) s3 s4 1 :=
    dvEval_set main dvCarry (Glyph.bit true) s3
  have e5 : Eval main (.set dvTest Glyph.eos) s4 s5 1 := dvEval_set main dvTest Glyph.eos s4
  have hs5_0 : s5.stk 0 = (Computability.encodeNat (n + 1)).map Glyph.bit ++ [Glyph.iend] ++
      (encs rest ++ R) := by
    simp [s5, s4, s3, s2, State.tSet, State.tPush, hs1_0]
  have hs5_1 : s5.stk 1 = dvMark :: s.stk 1 := by
    simp [s5, s4, s3, s2, State.tSet, State.tPush, hs1_1]
  have hs5_c : s5.reg dvCarry = Glyph.bit true := by
    simp [s5, s4, State.tSet, dvCarry_ne_dvTest]
  have hs5_t : s5.reg dvTest = Glyph.eos := by simp [s5, State.tSet]
  have hs5_oth : ∀ k : Stk, k ≠ 0 → k ≠ 1 → s5.stk k = s.stk k := by
    intro k hk0 hk1
    have h := hs1_oth k hk0
    simp [s5, s4, s3, s2, State.tSet, State.tPush, hk0, hk1, h]
  -- the loop
  obtain ⟨s6, n6, hev6, hn6, hs6_0, hs6_1, hregt6, hoth6⟩ :=
    dvLoop_eval main (Computability.encodeNat (n + 1)) true [] (encs rest ++ R)
      (dvMark :: s.stk 1) s5 hs5_0 (by rw [hs5_1]; rfl) hs5_c hs5_t
  set Q : List Bool := (decOutAux true (Computability.encodeNat (n + 1))).reverse with hQ
  have hs6_1' : s6.stk 1 = Q.map Glyph.bit ++ dvMark :: s.stk 1 := by
    rw [hs6_1]; simp
  -- the strip
  obtain ⟨s7, n7, hev7, hn7, hs7_1, hoth7⟩ :=
    dvStrip_eval main Q (dvMark :: s.stk 1) s6
      (by simp [dvMark_ne_bit]) hs6_1'
  have hs7_0 : s7.stk 0 = [Glyph.iend] ++ (encs rest ++ R) := by
    rw [hoth7 0 (by decide)]
    exact hs6_0
  -- the reverse pass
  have hnoMark : ∀ g ∈ (stripFirstFalse Q).map Glyph.bit, g ≠ dvMark := by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
    exact bit_ne_dvMark b
  obtain ⟨s8, n8, hev8, hn8, hs8_1, hs8_0, hs8_oth⟩ :=
    eval_mvRevOnto main 1 dvMark 0 dvTest ((stripFirstFalse Q).map Glyph.bit)
      (s.stk 1) (s7.stk 0) s7 hnoMark hs7_1 rfl (by decide)
  -- set the sign and push it back
  let s8' : State := State.tSet s8 dvSign Glyph.pos
  have e8 : Eval main (.set dvSign Glyph.pos) s8 s8' 1 := dvEval_set main dvSign Glyph.pos s8
  let s9 : State := State.tPush s8' 0 dvSign
  have e9 : Eval main (.push 0 dvSign) s8' s9 1 := dvEval_push main 0 dvSign s8'
  have hs9_0 : s9.stk 0 = Glyph.pos :: s8.stk 0 := by
    simp [s9, s8', State.tPush, State.tSet]
  have hbits : decBitsM (Computability.encodeNat (n + 1)) = Computability.encodeNat n := by
    have hIsB : IsBits (Computability.encodeNat (n + 1)) := by
      rw [encodeNat_eq_bits]; exact isBits_bits (n + 1)
    have hne : Computability.encodeNat (n + 1) ≠ [] := by
      rw [encodeNat_eq_bits]; exact bits_ne_nil_iff.mpr (by omega)
    have hof : ofBits (Computability.encodeNat (n + 1)) = n + 1 := by
      rw [encodeNat_eq_bits]; exact ofBits_bits (n + 1)
    rw [decBitsM_eq _ hIsB hne, hof, Nat.add_sub_cancel, encodeNat_eq_bits]
  have hfinal : s9.stk 0 = encs (HvdH.Val.int (n : ℤ) :: rest) ++ R := by
    have hQeq : (stripFirstFalse Q).reverse = decBitsM (Computability.encodeNat (n + 1)) := by
      rw [hQ]; rfl
    have h8 : s8.stk 0 = (decBitsM (Computability.encodeNat (n + 1))).map Glyph.bit ++
        [Glyph.iend] ++ (encs rest ++ R) := by
      rw [hs8_0, hs7_0, ← List.map_reverse, hQeq]
      simp [List.append_assoc]
    rw [hs9_0, h8, hbits, Work.Kernel.encs_cons,
      Size.enc_int_pos (by positivity : (0 : ℤ) ≤ (n : ℤ)), Int.natAbs_natCast]
    simp [List.append_assoc]
  have hs9_oth : ∀ k : Stk, k ≠ 0 → s9.stk k = s.stk k := by
    intro k hk0
    have hk9 : s9.stk k = s8.stk k := by
      rw [show s9.stk k = s8'.stk k from by simp [s9, s8', State.tPush, State.tSet, hk0]]
      simp [s8', State.tSet]
    by_cases hk1 : k = 1
    · subst hk1; rw [hk9, hs8_1]
    · rw [hk9, hs8_oth k hk1 hk0, hoth7 k hk1, hoth6 k hk0 hk1, hs5_oth k hk0 hk1]
  refine ⟨HvdH.Val.int (n : ℤ) :: rest, s9,
    1 + (1 + (1 + (1 + (1 + (n6 + (n7 + (n8 + (1 + 1)))))))), ⟨n, rest, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact dvEval_seq e1 (dvEval_seq e2 (dvEval_seq e3 (dvEval_seq e4 (dvEval_seq e5
      (dvEval_seq hev6 (dvEval_seq hev7 (dvEval_seq hev8 (dvEval_seq e8 e9))))))))
  · -- cost bound
    have hn6' : n6 ≤ 11 * ((Computability.encodeNat (n + 1)).length + 1) := hn6
    have hn7' : n7 ≤ 4 := hn7
    have hn8' : n8 ≤ 6 * (((stripFirstFalse Q).map Glyph.bit).length + 1) + 9 := hn8
    have hQlen : Q.length = (Computability.encodeNat (n + 1)).length := by
      rw [hQ, List.length_reverse, decOutAux_length]
    have hlen : ((stripFirstFalse Q).map Glyph.bit).length ≤
        (Computability.encodeNat (n + 1)).length := by
      rw [List.length_map]
      exact le_trans (stripFirstFalse_length_le Q) (le_of_eq hQlen)
    have hvsz : HvdH.vsz (HvdH.Val.int (↑n + 1 : ℤ)) = (n + 1).size + 2 := by
      show ((HvdH.Val.int (↑n + 1 : ℤ)).enc.length) = (n + 1).size + 2
      rw [vsz_int, isz_eq, hnz, Int.natAbs_natCast]
    rw [encodeNat_length] at hn6' hlen
    simp only [List.headD_cons]
    rw [hvsz]
    omega
  · rw [hfinal]
  · exact hs9_oth

end Work.IntLib
