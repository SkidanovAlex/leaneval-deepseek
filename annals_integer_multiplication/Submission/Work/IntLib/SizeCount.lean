import Mathlib
import Submission.Work.IntLib.SizeShared

/-!
# `size` / `clog 2`, piece 1: counting the bit glyphs of the top value into a unary counter

`countProg` consumes the bit glyphs of stack 0 (the sign has already been popped by the caller)
down to and including the closing `iend`, pushing one counter token per bit onto stack 1, above
the frame marker `gA`.  The cost is linear in the number of bits.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace Size

open HvdH

/-! ## Registers -/

/-- Loop/test register of the counting loop. -/
def rT : Reg := 0
/-- Register holding the counter token. -/
def rTok : Reg := 1
/-- Register used by the caller to discard the sign. -/
def rSign : Reg := 2
/-- A flag register. -/
def rFlag : Reg := 3

theorem rTok_ne_rT : rTok ≠ rT := by decide
theorem rSign_ne_rT : rSign ≠ rT := by decide
theorem rSign_ne_rTok : rSign ≠ rTok := by decide
theorem rFlag_ne_rT : rFlag ≠ rT := by decide
theorem rFlag_ne_rTok : rFlag ≠ rTok := by decide
theorem rFlag_ne_rSign : rFlag ≠ rSign := by decide
theorem rSign_ne_rFlag : rSign ≠ rFlag := by decide

/-! ## The loop body -/

/-- One iteration of the counting loop: pop a glyph; if it is the closing `iend` push it back and
set the test register to `gA` (stop), otherwise push one token and keep going. -/
def countBody : Cmd :=
  .seq (.pop 0 rT)
    (.ite rT Glyph.iend
      (.seq (.push 0 rT) (.set rT gA))
      (.seq (.push 1 rTok) (.set rT Glyph.eos)))

/-- `countProg`: marker, loop, discard the `iend`. -/
def countLoop : Cmd := .loop rT Glyph.eos countBody

def countProg0 : Cmd :=
  .seq (.set rT gA)
    (.seq (.push 1 rT)
      (.seq (.set rT Glyph.eos)
        (.seq countLoop (.pop 0 rT))))

/-! ## The states of one iteration -/

/-- State after consuming one bit (`rest` is what is left of stack 0). -/
def countStepState (s : State) (rest : List Glyph) : State :=
  (((s.updStk 0 rest).updReg rT gTok).updStk 1
    (gTok :: ((s.updStk 0 rest).updReg rT gTok).stk 1)).updReg rT Glyph.eos

/-- State after consuming the closing `iend`. -/
def countEndState (s : State) (rest : List Glyph) : State :=
  ((s.updStk 0 (Glyph.iend :: rest)).updReg rT Glyph.iend).updReg rT gA

@[simp] theorem countStepState_stk0 (s : State) (rest : List Glyph) :
    (countStepState s rest).stk 0 = rest := by simp [countStepState, State.updStk]

@[simp] theorem countStepState_stk1 (s : State) (rest : List Glyph) :
    (countStepState s rest).stk 1 = gTok :: s.stk 1 := by
  simp [countStepState, State.updStk, State.updReg]

@[simp] theorem countStepState_regT (s : State) (rest : List Glyph) :
    (countStepState s rest).reg rT = Glyph.eos := by simp [countStepState, State.updReg]

theorem countStepState_regTok (s : State) (rest : List Glyph) (h : s.reg rTok = gTok) :
    (countStepState s rest).reg rTok = gTok := by
  simp [countStepState, State.updReg, State.updStk, rTok_ne_rT, h]

theorem countStepState_stk (s : State) (rest : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (countStepState s rest).stk k = s.stk k := by
  simp [countStepState, State.updStk, State.updReg, hk0, hk1]

@[simp] theorem countEndState_stk0 (s : State) (rest : List Glyph) :
    (countEndState s rest).stk 0 = Glyph.iend :: rest := by
  simp [countEndState, State.updStk]

@[simp] theorem countEndState_stk1 (s : State) (rest : List Glyph) :
    (countEndState s rest).stk 1 = s.stk 1 := by simp [countEndState, State.updStk, State.updReg]

@[simp] theorem countEndState_regT (s : State) (rest : List Glyph) :
    (countEndState s rest).reg rT = gA := by simp [countEndState, State.updReg]

theorem countEndState_stk (s : State) (rest : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (countEndState s rest).stk k = s.stk k := by
  simp [countEndState, State.updStk, State.updReg, hk0, hk1]

/-! ## One iteration -/

theorem countBody_cont (main : Cmd) (s : State) (g : Glyph) (rest : List Glyph)
    (h0 : s.stk 0 = g :: rest) (hg : g ≠ Glyph.iend) (hrT : s.reg rT = Glyph.eos)
    (hTok : s.reg rTok = gTok) :
    Eval main countBody s (countStepState s rest) 4 := by
  have h1 : Eval main (.pop 0 rT) s ((s.updStk 0 rest).updReg rT g) 1 := by
    simpa [h0, State.updStk, State.updReg] using Eval.pop (main := main) 0 rT s
  have h2 : Eval main (.push 1 rTok) ((s.updStk 0 rest).updReg rT g)
      (((s.updStk 0 rest).updReg rT g).updStk 1
        (gTok :: ((s.updStk 0 rest).updReg rT g).stk 1)) 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [State.updReg, hTok, rTok_ne_rT]
  have h3 : Eval main (.set rT Glyph.eos)
      (((s.updStk 0 rest).updReg rT g).updStk 1
        (gTok :: ((s.updStk 0 rest).updReg rT g).stk 1))
      (countStepState s rest) 1 := by
    have hh := Eval.set (main := main) rT Glyph.eos
      (((s.updStk 0 rest).updReg rT g).updStk 1
        (gTok :: ((s.updStk 0 rest).updReg rT g).stk 1))
    simpa [countStepState, State.updStk, State.updReg] using hh
  have h23 := Eval.seq h2 h3
  have hite : Eval main (.ite rT Glyph.iend
      (.seq (.push 0 rT) (.set rT gA))
      (.seq (.push 1 rTok) (.set rT Glyph.eos))) ((s.updStk 0 rest).updReg rT g)
      (countStepState s rest) 3 := by
    refine Eval.iteF ?_ h23
    simp [State.updReg, hg]
  exact Eval.seq h1 hite

theorem countBody_end (main : Cmd) (s : State) (rest : List Glyph)
    (h0 : s.stk 0 = Glyph.iend :: rest) (hrT : s.reg rT = Glyph.eos) :
    Eval main countBody s (countEndState s rest) 4 := by
  have h1 : Eval main (.pop 0 rT) s ((s.updStk 0 rest).updReg rT Glyph.iend) 1 := by
    simpa [h0, State.updStk, State.updReg] using Eval.pop (main := main) 0 rT s
  have h2 : Eval main (.push 0 rT) ((s.updStk 0 rest).updReg rT Glyph.iend)
      (((s.updStk 0 rest).updReg rT Glyph.iend).updStk 0
        (Glyph.iend :: ((s.updStk 0 rest).updReg rT Glyph.iend).stk 0)) 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [State.updReg]
  have h3 : Eval main (.set rT gA)
      (((s.updStk 0 rest).updReg rT Glyph.iend).updStk 0
        (Glyph.iend :: ((s.updStk 0 rest).updReg rT Glyph.iend).stk 0))
      (countEndState s rest) 1 := by
    have hh := Eval.set (main := main) rT gA
      (((s.updStk 0 rest).updReg rT Glyph.iend).updStk 0
        (Glyph.iend :: ((s.updStk 0 rest).updReg rT Glyph.iend).stk 0))
    simpa [countEndState, State.updStk, State.updReg] using hh
  have h23 := Eval.seq h2 h3
  have hite : Eval main (.ite rT Glyph.iend
      (.seq (.push 0 rT) (.set rT gA))
      (.seq (.push 1 rTok) (.set rT Glyph.eos))) ((s.updStk 0 rest).updReg rT Glyph.iend)
      (countEndState s rest) 3 := by
    refine Eval.iteT ?_ h23
    simp [State.updReg]
  exact Eval.seq h1 hite

/-! ## The loop -/

theorem countLoop_eval (main : Cmd) (bits : List Bool) (m : ℕ) (below0 below1 : List Glyph)
    (s : State)
    (h0 : s.stk 0 = bits.map Glyph.bit ++ [Glyph.iend] ++ below0)
    (h1 : s.stk 1 = toks m ++ gA :: below1)
    (hrT : s.reg rT = Glyph.eos) (hTok : s.reg rTok = gTok) :
    ∃ (s' : State) (c : ℕ), Eval main countLoop s s' c ∧ c ≤ 6 * (bits.length + 1) ∧
      s'.stk 0 = [Glyph.iend] ++ below0 ∧
      s'.stk 1 = toks (m + bits.length) ++ gA :: below1 ∧
      s'.reg rT = gA ∧ (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  induction bits generalizing m s with
  | nil =>
    have hEnd : s.stk 0 = Glyph.iend :: below0 := by simpa using h0
    have hb := countBody_end main s below0 hEnd hrT
    have hstop : (countEndState s below0).reg rT ≠ Glyph.eos := by
      rw [countEndState_regT]; exact gA_ne_eos
    have hloop : Eval main countLoop s (countEndState s below0) (4 + 1 + 1) :=
      Eval.loopT (main := main) (by simpa using hrT) hb (Eval.loopF (main := main) hstop)
    refine ⟨countEndState s below0, 6, hloop, by norm_num, ?_, ?_, countEndState_regT s below0, ?_⟩
    · simp
    · rw [countEndState_stk1]; simpa using h1
    · intro k hk0 hk1; exact countEndState_stk s below0 hk0 hk1
  | cons b rest ih =>
    have h0' : s.stk 0 = Glyph.bit b :: (rest.map Glyph.bit ++ [Glyph.iend] ++ below0) := by
      simpa using h0
    have hb := countBody_cont main s (Glyph.bit b)
      (rest.map Glyph.bit ++ [Glyph.iend] ++ below0) h0' (bit_ne_iend b) hrT hTok
    have hs1 : countStepState s (rest.map Glyph.bit ++ [Glyph.iend] ++ below0) = _ := rfl
    obtain ⟨s', c', hev', hc', hstk0', hstk1', hreg', hoth'⟩ :=
      ih (m + 1) (countStepState s (rest.map Glyph.bit ++ [Glyph.iend] ++ below0))
        (by simp) (by rw [countStepState_stk1, h1]; simp [toks_succ])
        (countStepState_regT _ _) (countStepState_regTok s _ hTok)
    refine ⟨s', 4 + c' + 1, Eval.loopT (main := main) (by simpa using hrT) hb hev', ?_, hstk0', ?_,
      hreg', ?_⟩
    · have hc1 : c' ≤ 6 * (rest.length + 1) := hc'
      rw [List.length_cons]
      omega
    · rw [hstk1']
      have hlen : (m + 1) + rest.length = m + (b :: rest).length := by
        simp only [List.length_cons]; omega
      rw [hlen]
    · intro k hk0 hk1
      rw [hoth' k hk0 hk1]
      exact countStepState_stk s _ hk0 hk1

/-! ## The piece -/

def countProg : Cmd :=
  .seq (.set rTok gTok)
    (.seq (.set rT gA)
      (.seq (.push 1 rT)
        (.seq (.set rT Glyph.eos)
          (.seq countLoop (.pop 0 rT)))))

theorem sizeCountPiece : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (bits : List Bool)
    (below0 below1 : List Glyph) (s : State),
  s.stk 0 = bits.map Glyph.bit ++ [Glyph.iend] ++ below0 → s.stk 1 = below1 →
  ∃ (s' : State) (c : ℕ), Eval main prog s s' c ∧ c ≤ K * (bits.length + 1) ∧
    s'.stk 0 = below0 ∧ s'.stk 1 = toks bits.length ++ gA :: below1 ∧
    ∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k := by
  refine ⟨countProg, 12, ?_⟩
  intro main bits below0 below1 s h0 h1
  let s1 : State := s.updReg rTok gTok
  let s2 : State := s1.updReg rT gA
  let s3 : State := s2.updStk 1 (gA :: s2.stk 1)
  let s4 : State := s3.updReg rT Glyph.eos
  have e0 : Eval main (.set rTok gTok) s s1 1 := Eval.set_eq
  have e1 : Eval main (.set rT gA) s1 s2 1 := Eval.set_eq
  have e2 : Eval main (.push 1 rT) s2 s3 1 := by
    refine Eval.push_eq (main := main) ?_
    simp [s1, s2, State.updReg]
  have e3 : Eval main (.set rT Glyph.eos) s3 s4 1 := Eval.set_eq
  have hs4stk0 : s4.stk 0 = bits.map Glyph.bit ++ [Glyph.iend] ++ below0 := by
    simp [s3, s4, s2, s1, State.updStk, State.updReg, h0]
  have hs4stk1 : s4.stk 1 = toks 0 ++ gA :: below1 := by
    simp [s3, s4, s2, s1, State.updStk, State.updReg, h1]
  have hs4regT : s4.reg rT = Glyph.eos := by simp [s4, State.updReg]
  have hs4regTok : s4.reg rTok = gTok := by
    simp [s3, s4, s2, s1, State.updReg, State.updStk, rTok_ne_rT]
  obtain ⟨s', c', hev', hc', hs0, hs1, hreg', hoth'⟩ :=
    countLoop_eval main bits 0 below0 below1 s4 hs4stk0 hs4stk1 hs4regT hs4regTok
  let s5 : State := (s'.updStk 0 below0).updReg rT Glyph.iend
  have e4 : Eval main (.pop 0 rT) s' s5 1 := by
    have hh := Eval.pop (main := main) 0 rT s'
    simpa [s5, hs0, State.updStk, State.updReg] using hh
  refine ⟨s5, 1 + (1 + (1 + (1 + (c' + 1)))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq hev' e4))))
  · have hc1 : c' ≤ 6 * (bits.length + 1) := hc'
    have hm : 1 ≤ bits.length + 1 := Nat.le_add_left 1 _
    nlinarith [hc1, hm]
  · simp [s5, State.updStk, State.updReg]
  · simp [s5, hs1, State.updStk, State.updReg]
  · intro k hk0 hk1
    show ((s'.updStk 0 below0).updReg rT Glyph.iend).stk k = s.stk k
    rw [State.updReg_stk, State.updStk_apply]
    simp only [if_neg hk0]
    have h1' := hoth' k hk0 hk1
    rw [h1']
    simp [s3, s4, s2, s1, State.updStk, State.updReg, hk0, hk1]

end Size
end Work.IntLib
