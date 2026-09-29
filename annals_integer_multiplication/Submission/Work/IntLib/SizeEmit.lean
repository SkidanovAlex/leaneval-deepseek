import Mathlib
import Submission.Work.IntLib.SizeShared
import Submission.Work.IntLib.SizeCount

/-!
# `size` / `pow2`, the emitting pieces

* `sizeEmit`: turn a most-significant-first bit region on stack 3 into the encoding of the
  corresponding integer value on stack 0 (`pos :: bits ++ [iend]`);
* `sizeEmitZeros`: turn a unary counter `k` on stack 1 into the encoding of `2^k`
  (`pos :: k·false ++ [true, iend]`).
-/

set_option autoImplicit false

namespace Work.IntLib
namespace Size

open HvdH

/-- Register receiving the constant `iend`. -/
def rIend : Reg := 5
/-- Register receiving the constant `pos`. -/
def rPos : Reg := 6
/-- Register receiving the constant `bit true`. -/
def rTrue : Reg := 7
/-- Register receiving the constant `bit false`. -/
def rZero : Reg := 8
/-- Scratch register (e.g. to discard a glyph). -/
def rScr : Reg := 9

theorem rIend_ne_rT : rIend ≠ rT := by decide
theorem rIend_ne_rFlag : rIend ≠ rFlag := by decide
theorem rPos_ne_rFlag : rPos ≠ rFlag := by decide
theorem rZero_ne_rFlag : rZero ≠ rFlag := by decide
theorem rScr_ne_rFlag : rScr ≠ rFlag := by decide
theorem rTrue_ne_rFlag : rTrue ≠ rFlag := by decide
theorem rIend_ne_rSign : rIend ≠ rSign := by decide
theorem rPos_ne_rSign : rPos ≠ rSign := by decide
theorem rZero_ne_rSign : rZero ≠ rSign := by decide
theorem rIend_ne_rPos : rIend ≠ rPos := by decide
theorem rSign_ne_rIend : rSign ≠ rIend := by decide
theorem m1 : (1 : Stk) ≠ 0 := by decide
theorem m2 : (2 : Stk) ≠ 0 := by decide
theorem m3 : (3 : Stk) ≠ 0 := by decide
theorem m12 : (1 : Stk) ≠ 2 := by decide
theorem m13 : (1 : Stk) ≠ 3 := by decide
theorem m23 : (2 : Stk) ≠ 3 := by decide
theorem rIend_ne_rTok : rIend ≠ rTok := by decide
theorem rPos_ne_rT : rPos ≠ rT := by decide
theorem rZero_ne_rT : rZero ≠ rT := by decide
theorem rScr_ne_rT : rScr ≠ rT := by decide
theorem rTrue_ne_rT : rTrue ≠ rT := by decide

/-! ## `sizeEmit`: bit region on stack 3 → encoded value on stack 0 -/

/-- One iteration: pop a glyph from stack 3; the marker `gC` stops the loop (and is consumed),
anything else is pushed onto stack 0. -/
def emitBody : Cmd :=
  .seq (.pop 3 rT)
    (.ite rT gC (.set rT gA) (.seq (.push 0 rT) (.set rT Glyph.eos)))

def emitLoop : Cmd := .loop rT Glyph.eos emitBody

def emitProg : Cmd :=
  .seq (.set rIend Glyph.iend)
    (.seq (.push 0 rIend)
      (.seq (.set rT Glyph.eos)
        (.seq emitLoop
          (.seq (.set rPos Glyph.pos)
            (.seq (.push 0 rPos)
              (.pop 1 rScr))))))

/-- State after one `emitBody` iteration that consumed a bit. -/
def emitStepState (s : State) (rest : List Glyph) (g : Glyph) : State :=
  (((s.updStk 3 rest).updReg rT g).updStk 0 (g :: ((s.updStk 3 rest).updReg rT g).stk 0)).updReg rT Glyph.eos

/-- State after the iteration that consumed the marker `gC`. -/
def emitEndState (s : State) (rest : List Glyph) : State :=
  ((s.updStk 3 rest).updReg rT gC).updReg rT gA

@[simp] theorem emitStepState_stk3 (s : State) (rest : List Glyph) (g : Glyph) :
    (emitStepState s rest g).stk 3 = rest := by simp [emitStepState, State.updStk]

@[simp] theorem emitStepState_stk0 (s : State) (rest : List Glyph) (g : Glyph) :
    (emitStepState s rest g).stk 0 = g :: s.stk 0 := by
  simp [emitStepState, State.updStk, State.updReg]

@[simp] theorem emitStepState_regT (s : State) (rest : List Glyph) (g : Glyph) :
    (emitStepState s rest g).reg rT = Glyph.eos := by simp [emitStepState, State.updReg]

theorem emitStepState_stk (s : State) (rest : List Glyph) (g : Glyph) {k : Stk}
    (hk0 : k ≠ 0) (hk3 : k ≠ 3) : (emitStepState s rest g).stk k = s.stk k := by
  simp [emitStepState, State.updStk, State.updReg, hk0, hk3]

@[simp] theorem emitEndState_stk3 (s : State) (rest : List Glyph) :
    (emitEndState s rest).stk 3 = rest := by simp [emitEndState, State.updStk]

@[simp] theorem emitEndState_stk0 (s : State) (rest : List Glyph) :
    (emitEndState s rest).stk 0 = s.stk 0 := by simp [emitEndState, State.updStk, State.updReg]

@[simp] theorem emitEndState_regT (s : State) (rest : List Glyph) :
    (emitEndState s rest).reg rT = gA := by simp [emitEndState, State.updReg]

theorem emitEndState_stk (s : State) (rest : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    (emitEndState s rest).stk k = s.stk k := by
  simp [emitEndState, State.updStk, State.updReg, hk0, hk3]

theorem emitBody_cont (main : Cmd) (s : State) (g : Glyph) (rest : List Glyph)
    (h3 : s.stk 3 = g :: rest) (hg : g ≠ gC) (hrT : s.reg rT = Glyph.eos) :
    Eval main emitBody s (emitStepState s rest g) 4 := by
  have h1 : Eval main (.pop 3 rT) s ((s.updStk 3 rest).updReg rT g) 1 := by
    simpa [h3, State.updStk, State.updReg] using Eval.pop (main := main) 3 rT s
  have h2 : Eval main (.push 0 rT) ((s.updStk 3 rest).updReg rT g)
      (((s.updStk 3 rest).updReg rT g).updStk 0
        (g :: ((s.updStk 3 rest).updReg rT g).stk 0)) 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [State.updReg]
  have h3' : Eval main (.set rT Glyph.eos)
      (((s.updStk 3 rest).updReg rT g).updStk 0
        (g :: ((s.updStk 3 rest).updReg rT g).stk 0))
      (emitStepState s rest g) 1 := by
    have hh := Eval.set (main := main) rT Glyph.eos
      (((s.updStk 3 rest).updReg rT g).updStk 0
        (g :: ((s.updStk 3 rest).updReg rT g).stk 0))
    simpa [emitStepState, State.updStk, State.updReg] using hh
  have h23 := Eval.seq h2 h3'
  have hite : Eval main (.ite rT gC (.set rT gA)
      (.seq (.push 0 rT) (.set rT Glyph.eos))) ((s.updStk 3 rest).updReg rT g)
      (emitStepState s rest g) 3 := by
    refine Eval.iteF ?_ h23
    simp [State.updReg, hg]
  exact Eval.seq h1 hite

theorem emitBody_end (main : Cmd) (s : State) (rest : List Glyph)
    (h3 : s.stk 3 = gC :: rest) (hrT : s.reg rT = Glyph.eos) :
    Eval main emitBody s (emitEndState s rest) 3 := by
  have h1 : Eval main (.pop 3 rT) s ((s.updStk 3 rest).updReg rT gC) 1 := by
    simpa [h3, State.updStk, State.updReg] using Eval.pop (main := main) 3 rT s
  have h2 : Eval main (.set rT gA) ((s.updStk 3 rest).updReg rT gC)
      (emitEndState s rest) 1 := by
    have hh := Eval.set (main := main) rT gA ((s.updStk 3 rest).updReg rT gC)
    simpa [emitEndState, State.updStk, State.updReg] using hh
  have hite : Eval main (.ite rT gC (.set rT gA)
      (.seq (.push 0 rT) (.set rT Glyph.eos))) ((s.updStk 3 rest).updReg rT gC)
      (emitEndState s rest) 2 := by
    refine Eval.iteT ?_ h2
    simp [State.updReg]
  exact Eval.seq h1 hite

/-- The emitting loop: `bits` (most significant first) is on stack 3 above `gC`; the reverse
(prepended, least significant first) lands on stack 0. -/
theorem emitLoop_eval (main : Cmd) (bits : List Bool) (acc below0 below3 : List Glyph) (s : State)
    (h0 : s.stk 0 = acc ++ below0)
    (h3 : s.stk 3 = bits.map Glyph.bit ++ gC :: below3)
    (hrT : s.reg rT = Glyph.eos) :
    ∃ (s' : State) (c : ℕ), Eval main emitLoop s s' c ∧ c ≤ 6 * (bits.length + 1) ∧
      s'.stk 0 = (bits.reverse.map Glyph.bit) ++ acc ++ below0 ∧
      s'.stk 3 = below3 ∧ s'.reg rT = gA ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 3 → s'.stk k = s.stk k) := by
  induction bits generalizing acc s with
  | nil =>
    have h3' : s.stk 3 = gC :: below3 := by simpa using h3
    have hb := emitBody_end main s below3 h3' hrT
    have hstop : (emitEndState s below3).reg rT ≠ Glyph.eos := by
      rw [emitEndState_regT]; exact gA_ne_eos
    have hloop : Eval main emitLoop s (emitEndState s below3) (3 + 1 + 1) :=
      Eval.loopT (main := main) (by simpa using hrT) hb (Eval.loopF (main := main) hstop)
    refine ⟨emitEndState s below3, 5, hloop, by norm_num, ?_, emitEndState_stk3 s below3,
      emitEndState_regT s below3, ?_⟩
    · rw [emitEndState_stk0]; simpa using h0
    · intro k hk0 hk3; exact emitEndState_stk s below3 hk0 hk3
  | cons b rest ih =>
    have h3' : s.stk 3 = Glyph.bit b :: (rest.map Glyph.bit ++ gC :: below3) := by
      simpa using h3
    have hb := emitBody_cont main s (Glyph.bit b)
      (rest.map Glyph.bit ++ gC :: below3) h3' (bit_ne_gC b) hrT
    have hAcc : (emitStepState s (rest.map Glyph.bit ++ gC :: below3) (Glyph.bit b)).stk 0
        = (Glyph.bit b :: acc) ++ below0 := by
      rw [emitStepState_stk0]; simp [h0]
    obtain ⟨s', c', hev', hc', hs0, hs3, hreg', hoth'⟩ :=
      ih (Glyph.bit b :: acc) (emitStepState s (rest.map Glyph.bit ++ gC :: below3) (Glyph.bit b))
        hAcc (by rw [emitStepState_stk3]) (emitStepState_regT _ _ _)
    refine ⟨s', 4 + c' + 1, Eval.loopT (main := main) (by simpa using hrT) hb hev', ?_, ?_,
      hs3, hreg', ?_⟩
    · have hc1 : c' ≤ 6 * (rest.length + 1) := hc'
      rw [List.length_cons]
      omega
    · rw [hs0]
      have : (rest.reverse.map Glyph.bit) ++ (Glyph.bit b :: acc) ++ below0
          = ((b :: rest).reverse.map Glyph.bit) ++ acc ++ below0 := by
        simp [List.reverse_cons]
      exact this
    · intro k hk0 hk3
      rw [hoth' k hk0 hk3]
      exact emitStepState_stk s _ _ hk0 hk3

theorem sizeEmit : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (bits : List Bool)
    (below0 below1 below3 : List Glyph) (s : State), IsBits bits.reverse →
  s.stk 0 = below0 → s.stk 1 = gA :: below1 → s.stk 3 = bits.map Glyph.bit ++ gC :: below3 →
  ∃ (s' : State) (c : ℕ), Eval main prog s s' c ∧ c ≤ K * (bits.length + 1) ∧
    s'.stk 0 = (Val.int ((ofBits bits.reverse : ℕ) : ℤ)).enc ++ below0 ∧
    s'.stk 1 = below1 ∧ s'.stk 3 = below3 ∧
    ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 3 → s'.stk k = s.stk k := by
  refine ⟨emitProg, 16, ?_⟩
  intro main bits below0 below1 below3 s his h0 h1 h3
  let s0 : State := s.updReg rIend Glyph.iend
  let s1 : State := s0.updStk 0 (Glyph.iend :: s0.stk 0)
  let s2 : State := s1.updReg rT Glyph.eos
  have e0 : Eval main (.set rIend Glyph.iend) s s0 1 := Eval.set_eq
  have e1 : Eval main (.push 0 rIend) s0 s1 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [s0, State.updReg]
  have e2 : Eval main (.set rT Glyph.eos) s1 s2 1 := Eval.set_eq
  have hs2stk0 : s2.stk 0 = ([Glyph.iend] : List Glyph) ++ below0 := by
    simp [s1, s2, s0, State.updStk, State.updReg, h0]
  obtain ⟨s', c', hev', hc', hs0, hs3, hreg', hoth'⟩ :=
    emitLoop_eval main bits (Glyph.iend :: []) below0 below3 s2 hs2stk0
      (by simp [s1, s2, s0, State.updStk, State.updReg, h3]) (by simp [s2, State.updReg])
  let s3 : State := s'.updReg rPos Glyph.pos
  let s4 : State := s3.updStk 0 (Glyph.pos :: s3.stk 0)
  have e3 : Eval main (.set rPos Glyph.pos) s' s3 1 := Eval.set_eq
  have e4 : Eval main (.push 0 rPos) s3 s4 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [s3, State.updReg]
  have hs4stk1 : s4.stk 1 = gA :: below1 := by
    simp [s4, s3, State.updStk, State.updReg, hoth' 1 (by decide) (by decide),
      s1, s2, s0, h1]
  let s5 : State := (s4.updStk 1 (s4.stk 1).tail).updReg rScr ((s4.stk 1).headD .eos)
  have e5 : Eval main (.pop 1 rScr) s4 s5 1 := by
    have hh := Eval.pop (main := main) 1 rScr s4
    simpa [s5, hs4stk1, State.updStk, State.updReg] using hh
  have hbits : (ofBits bits.reverse).bits = bits.reverse := bits_ofBits_of_isBits bits.reverse his
  have henc : (Val.int ((ofBits bits.reverse : ℕ) : ℤ)).enc
      = Glyph.pos :: bits.reverse.map Glyph.bit ++ [Glyph.iend] := by
    rw [enc_int_pos (by positivity : (0 : ℤ) ≤ ((ofBits bits.reverse : ℕ) : ℤ))]
    simp only [Int.natAbs_natCast]
    rw [encodeNat_eq_bits, hbits]
  refine ⟨s5, 1 + (1 + (1 + (c' + (1 + (1 + 1))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq hev' (Eval.seq e3 (Eval.seq e4 e5)))))
  · have hc1 : c' ≤ 6 * (bits.length + 1) := hc'
    have hm : 1 ≤ bits.length + 1 := Nat.le_add_left 1 _
    nlinarith
  · -- stack 0
    rw [henc]
    simp [s5, s4, s3, hs0]
  · -- stack 1
    simp [s5, hs4stk1]
  · -- stack 3
    simp [s5, s4, s3, hs3]
  · -- other stacks
    intro k hk0 hk1 hk3
    simp [s5, s4, s3, s2, s1, s0, State.updStk_apply, State.updReg_stk,
      hoth' k hk0 hk3, hk0, hk1]

/-! ## `sizeEmitZeros`: unary counter `k` on stack 1 → encoding of `2^k` on stack 0 -/

theorem replicate_false_cons (j : ℕ) (acc : List Glyph) :
    List.replicate j (Glyph.bit false) ++ (Glyph.bit false :: acc)
      = List.replicate (j + 1) (Glyph.bit false) ++ acc := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, ih]
    conv_rhs => rw [List.replicate_succ, List.cons_append]

/-- One iteration of the "write `k` zeros" loop: pop a token from stack 1; the marker `gA` stops
the loop (and is consumed), anything else pushes one `bit false` onto stack 0. -/
def zerosBody : Cmd :=
  .seq (.pop 1 rT)
    (.ite rT gA (.set rT gA) (.seq (.push 0 rZero) (.set rT Glyph.eos)))

def zerosLoop : Cmd := .loop rT Glyph.eos zerosBody

def zerosProg : Cmd :=
  .seq (.set rIend Glyph.iend)
    (.seq (.push 0 rIend)
      (.seq (.set rTrue (Glyph.bit true))
        (.seq (.push 0 rTrue)
          (.seq (.set rZero (Glyph.bit false))
            (.seq (.set rT Glyph.eos)
              (.seq zerosLoop
                (.seq (.set rPos Glyph.pos) (.push 0 rPos))))))))

/-- State after one iteration that consumed a token. -/
def zerosStepState (s : State) (rest : List Glyph) : State :=
  (((s.updStk 1 rest).updReg rT gTok).updStk 0
    (Glyph.bit false :: ((s.updStk 1 rest).updReg rT gTok).stk 0)).updReg rT Glyph.eos

/-- State after the iteration that consumed the marker `gA`. -/
def zerosEndState (s : State) (rest : List Glyph) : State :=
  ((s.updStk 1 rest).updReg rT gA).updReg rT gA

@[simp] theorem zerosStepState_stk1 (s : State) (rest : List Glyph) :
    (zerosStepState s rest).stk 1 = rest := by simp [zerosStepState, State.updStk]

@[simp] theorem zerosStepState_stk0 (s : State) (rest : List Glyph) :
    (zerosStepState s rest).stk 0 = Glyph.bit false :: s.stk 0 := by
  simp [zerosStepState, State.updStk, State.updReg]

@[simp] theorem zerosStepState_regT (s : State) (rest : List Glyph) :
    (zerosStepState s rest).reg rT = Glyph.eos := by simp [zerosStepState, State.updReg]

theorem zerosStepState_stk (s : State) (rest : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (zerosStepState s rest).stk k = s.stk k := by
  simp [zerosStepState, State.updStk, State.updReg, hk0, hk1]

@[simp] theorem zerosEndState_stk1 (s : State) (rest : List Glyph) :
    (zerosEndState s rest).stk 1 = rest := by simp [zerosEndState, State.updStk]

@[simp] theorem zerosEndState_stk0 (s : State) (rest : List Glyph) :
    (zerosEndState s rest).stk 0 = s.stk 0 := by simp [zerosEndState, State.updStk, State.updReg]

@[simp] theorem zerosEndState_regT (s : State) (rest : List Glyph) :
    (zerosEndState s rest).reg rT = gA := by simp [zerosEndState, State.updReg]

theorem zerosEndState_stk (s : State) (rest : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (zerosEndState s rest).stk k = s.stk k := by
  simp [zerosEndState, State.updStk, State.updReg, hk0, hk1]

theorem zerosBody_cont (main : Cmd) (s : State) (g : Glyph) (rest : List Glyph)
    (h1 : s.stk 1 = g :: rest) (hg : g ≠ gA) (hrT : s.reg rT = Glyph.eos)
    (hZero : s.reg rZero = Glyph.bit false) :
    Eval main zerosBody s (zerosStepState s rest) 4 := by
  have h1' : Eval main (.pop 1 rT) s ((s.updStk 1 rest).updReg rT g) 1 := by
    simpa [h1, State.updStk, State.updReg] using Eval.pop (main := main) 1 rT s
  have h2 : Eval main (.push 0 rZero) ((s.updStk 1 rest).updReg rT g)
      (((s.updStk 1 rest).updReg rT g).updStk 0
        (Glyph.bit false :: ((s.updStk 1 rest).updReg rT g).stk 0)) 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [State.updReg, State.updStk, Function.update_apply, rZero_ne_rT, hZero]
  have h3 : Eval main (.set rT Glyph.eos)
      (((s.updStk 1 rest).updReg rT g).updStk 0
        (Glyph.bit false :: ((s.updStk 1 rest).updReg rT g).stk 0))
      (zerosStepState s rest) 1 := by
    have hh := Eval.set (main := main) rT Glyph.eos
      (((s.updStk 1 rest).updReg rT g).updStk 0
        (Glyph.bit false :: ((s.updStk 1 rest).updReg rT g).stk 0))
    simpa [zerosStepState, State.updStk, State.updReg] using hh
  have h23 := Eval.seq h2 h3
  have hite : Eval main (.ite rT gA (.set rT gA)
      (.seq (.push 0 rZero) (.set rT Glyph.eos))) ((s.updStk 1 rest).updReg rT g)
      (zerosStepState s rest) 3 := by
    refine Eval.iteF ?_ h23
    simp [State.updReg, hg]
  exact Eval.seq h1' hite

theorem zerosBody_end (main : Cmd) (s : State) (rest : List Glyph)
    (h1 : s.stk 1 = gA :: rest) (hrT : s.reg rT = Glyph.eos) :
    Eval main zerosBody s (zerosEndState s rest) 3 := by
  have h1' : Eval main (.pop 1 rT) s ((s.updStk 1 rest).updReg rT gA) 1 := by
    simpa [h1, State.updStk, State.updReg] using Eval.pop (main := main) 1 rT s
  have h2 : Eval main (.set rT gA) ((s.updStk 1 rest).updReg rT gA) (zerosEndState s rest) 1 := by
    have hh := Eval.set (main := main) rT gA ((s.updStk 1 rest).updReg rT gA)
    simpa [zerosEndState, State.updStk, State.updReg] using hh
  have hite : Eval main (.ite rT gA (.set rT gA)
      (.seq (.push 0 rZero) (.set rT Glyph.eos))) ((s.updStk 1 rest).updReg rT gA)
      (zerosEndState s rest) 2 := by
    refine Eval.iteT ?_ h2
    simp [State.updReg]
  exact Eval.seq h1' hite

theorem zerosLoop_eval (main : Cmd) (j : ℕ) (below1 : List Glyph) (acc : List Glyph) (s : State)
    (h0 : s.stk 0 = acc) (h1 : s.stk 1 = toks j ++ gA :: below1)
    (hrT : s.reg rT = Glyph.eos) (hZero : s.reg rZero = Glyph.bit false) :
    ∃ (s' : State) (c : ℕ), Eval main zerosLoop s s' c ∧ c ≤ 6 * (j + 1) ∧
      s'.stk 0 = List.replicate j (Glyph.bit false) ++ acc ∧
      s'.stk 1 = below1 ∧ s'.reg rT = gA ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  induction j generalizing acc s with
  | zero =>
    have h1' : s.stk 1 = gA :: below1 := by simpa using h1
    have hb := zerosBody_end main s below1 h1' hrT
    have hstop : (zerosEndState s below1).reg rT ≠ Glyph.eos := by
      rw [zerosEndState_regT]; exact gA_ne_eos
    have hloop : Eval main zerosLoop s (zerosEndState s below1) (3 + 1 + 1) :=
      Eval.loopT (main := main) (by simpa using hrT) hb (Eval.loopF (main := main) hstop)
    refine ⟨zerosEndState s below1, 5, hloop, by norm_num, ?_, zerosEndState_stk1 s below1,
      zerosEndState_regT s below1, ?_⟩
    · rw [zerosEndState_stk0]; simpa using h0
    · intro k hk0 hk1; exact zerosEndState_stk s below1 hk0 hk1
  | succ j ih =>
    have h1' : s.stk 1 = gTok :: (toks j ++ gA :: below1) := by
      rw [h1, toks_succ, List.cons_append]
    have hb := zerosBody_cont main s gTok (toks j ++ gA :: below1) h1' gTok_ne_gA hrT hZero
    have hAcc : (zerosStepState s (toks j ++ gA :: below1)).stk 0
        = (Glyph.bit false :: acc) := by
      rw [zerosStepState_stk0]; simp [h0]
    obtain ⟨s', c', hev', hc', hs0, hs1, hreg', hoth'⟩ :=
      ih (Glyph.bit false :: acc) (zerosStepState s (toks j ++ gA :: below1)) hAcc
        (by rw [zerosStepState_stk1]) (zerosStepState_regT _ _)
        (by simp [zerosStepState, State.updReg, State.updStk, Function.update_apply,
          rZero_ne_rT, hZero])
    refine ⟨s', 4 + c' + 1, Eval.loopT (main := main) (by simpa using hrT) hb hev', ?_, ?_,
      hs1, hreg', ?_⟩
    · have hc1 : c' ≤ 6 * (j + 1) := hc'
      omega
    · rw [hs0]
      exact replicate_false_cons j acc
    · intro k hk0 hk1
      rw [hoth' k hk0 hk1]
      exact zerosStepState_stk s _ hk0 hk1

theorem sizeEmitZeros : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ)
    (below0 below1 : List Glyph) (s : State),
  s.stk 0 = below0 → s.stk 1 = toks k ++ gA :: below1 →
  ∃ (s' : State) (c : ℕ), Eval main prog s s' c ∧ c ≤ K * (k + 1) ∧
    s'.stk 0 = Glyph.pos :: List.replicate k (Glyph.bit false) ++
      [Glyph.bit true, Glyph.iend] ++ below0 ∧
    s'.stk 1 = below1 ∧
    ∀ j : Stk, j ≠ 0 → j ≠ 1 → s'.stk j = s.stk j := by
  refine ⟨zerosProg, 16, ?_⟩
  intro main k below0 below1 s h0 h1
  let s0 : State := s.updReg rIend Glyph.iend
  let s1 : State := s0.updStk 0 (Glyph.iend :: s0.stk 0)
  let s2 : State := s1.updReg rTrue (Glyph.bit true)
  let s3 : State := s2.updStk 0 (Glyph.bit true :: s2.stk 0)
  let s4 : State := s3.updReg rZero (Glyph.bit false)
  let s5 : State := s4.updReg rT Glyph.eos
  have e0 : Eval main (.set rIend Glyph.iend) s s0 1 := Eval.set_eq
  have e1 : Eval main (.push 0 rIend) s0 s1 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [s0, State.updReg]
  have e2 : Eval main (.set rTrue (Glyph.bit true)) s1 s2 1 := Eval.set_eq
  have e3 : Eval main (.push 0 rTrue) s2 s3 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [s2, State.updReg]
  have e4 : Eval main (.set rZero (Glyph.bit false)) s3 s4 1 := Eval.set_eq
  have e5 : Eval main (.set rT Glyph.eos) s4 s5 1 := Eval.set_eq
  have hs5stk0 : s5.stk 0 = ([Glyph.bit true, Glyph.iend] : List Glyph) ++ below0 := by
    simp [s5, s4, s3, s2, s1, s0, State.updStk, State.updReg, h0]
  have hs5stk1 : s5.stk 1 = toks k ++ gA :: below1 := by
    simp [s5, s4, s3, s2, s1, s0, State.updStk, State.updReg, h1]
  obtain ⟨s', c', hev', hc', hs0, hs1, hreg', hoth'⟩ :=
    zerosLoop_eval main k below1 ([Glyph.bit true, Glyph.iend] ++ below0) s5 hs5stk0 hs5stk1
      (by simp [s5, State.updReg])
      (by simp [s5, s4, s3, State.updReg, State.updStk, Function.update_apply, rZero_ne_rT])
  let s6 : State := s'.updReg rPos Glyph.pos
  let s7 : State := s6.updStk 0 (Glyph.pos :: s6.stk 0)
  have e6 : Eval main (.set rPos Glyph.pos) s' s6 1 := Eval.set_eq
  have e7 : Eval main (.push 0 rPos) s6 s7 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [s6, State.updReg]
  refine ⟨s7, 1 + (1 + (1 + (1 + (1 + (1 + (c' + (1 + 1))))))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
      (Eval.seq hev' (Eval.seq e6 e7)))))))
  · have hc1 : c' ≤ 6 * (k + 1) := hc'
    have hm : 1 ≤ k + 1 := Nat.le_add_left 1 _
    nlinarith
  · -- stack 0
    simp [s7, s6, hs0]
  · -- stack 1
    simp [s7, s6, s5, s4, s3, s2, s1, s0, hs1]
  · -- other stacks
    intro j hj0 hj1
    simp [s7, s6, s5, s4, s3, s2, s1, s0, State.updStk_apply, State.updReg_stk,
      hoth' j hj0 hj1, hj0, hj1]

end Size
end Work.IntLib
