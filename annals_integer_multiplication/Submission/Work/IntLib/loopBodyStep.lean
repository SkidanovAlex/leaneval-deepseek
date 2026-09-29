import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.dropZeros
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.IntLib.outOrderStepProved
import Submission.Work.IntLib.sSdropZerosProof
import Submission.Work.IntLib.loopCounterArith

/-!
# `IntLib` / `chunk`: one iteration of the main loop

`loopBodyStep` is the one-step invariant of the `chunk` word's main loop: from the loop state
`lSt x b N Y k` (after `k` consumed bit positions) the loop body reaches `lSt x b N Y (k+1)` at cost
at most `cstep b KC k`.

The body has fourteen commands, grouped into four blocks:

1. `peek sX rA` … `push sZ rA` — read the next bit (or the padding zero), push it onto `sR`, save
   it on `sZ` (`loopBodyFront`);
2. `peek sCW rB` … `ite rE gCont copyProg skip` — open a new group if the working counter is empty,
   refilling it with `copyProg` (`loopBodyCounter`);
3. `pop sZ rA` … `ite rB gEnd …` — push the bit onto `sS`, decrement the working counter, close the
   group (`loopBodySS`);
4. `resetRegs` … `ite rG gEnd …` — reset the register file and decide whether the loop continues
   (`loopBodyTail`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## Composition of `Ev` along `seqs` -/

/-- `Eval` of `.skip` does not move the state. -/
theorem Ev_skip_eq {main : Cmd} {s t : State} {C : ℕ} (h : Ev main .skip s t C) : t = s := by
  obtain ⟨n, he, -⟩ := h
  cases he
  rfl

/-- Splitting an `Ev` of a sequence into its two halves. -/
theorem Ev_seq_inv {main : Cmd} {p q : Cmd} {s u : State} {C : ℕ}
    (h : Ev main (.seq p q) s u C) :
    ∃ (t : State) (C₁ C₂ : ℕ), Ev main p s t C₁ ∧ Ev main q t u C₂ ∧ C₁ + C₂ ≤ C := by
  obtain ⟨n, he, hn⟩ := h
  cases he with
  | seq h₁ h₂ => exact ⟨_, _, _, ⟨_, h₁, le_rfl⟩, ⟨_, h₂, le_rfl⟩, hn⟩

/-- `Ev` is compositional in the concatenation of command lists (`seqs` is right-nested). -/
theorem seqsAppend {main : Cmd} {l₁ l₂ : List Cmd} {s t u : State} {C₁ C₂ : ℕ}
    (h₁ : Ev main (seqs l₁) s t C₁) (h₂ : Ev main (seqs l₂) t u C₂) :
    Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
  have aux : ∀ (l₁ l₂ : List Cmd) (s t u : State) (C₁ C₂ : ℕ),
      Ev main (seqs l₁) s t C₁ → Ev main (seqs l₂) t u C₂ →
      Ev main (seqs (l₁ ++ l₂)) s u (C₁ + C₂) := by
    intro l₁
    induction l₁ with
    | nil =>
        intro l₂ s t u C₁ C₂ h₁ h₂
        have hts : t = s := Ev_skip_eq h₁
        rw [hts] at h₂
        exact h₂.mono (by omega)
    | cons c cs ih =>
        intro l₂ s t u C₁ C₂ h₁ h₂
        cases l₂ with
        | nil =>
            have htu : u = t := Ev_skip_eq h₂
            subst htu
            rw [List.append_nil]
            exact h₁.mono (by omega)
        | cons d ds =>
            cases cs with
            | nil => exact Ev.seq' h₁ h₂ (by omega)
            | cons e es =>
                have h₁' : Ev main (.seq c (seqs (e :: es))) s t C₁ := h₁
                obtain ⟨t', C₁', C₂', hc, hrest, hle⟩ := Ev_seq_inv h₁'
                have hrec : Ev main (seqs ((e :: es) ++ (d :: ds))) t' u (C₂' + C₂) :=
                  ih (d :: ds) t' t u C₂' C₂ hrest h₂
                exact Ev.seq' hc hrec (by omega)
  exact aux l₁ l₂ s t u C₁ C₂ h₁ h₂

/-! ## Component lemmas for the canonical step states -/

@[simp] theorem tPeek_stk (s : State) (k : Stk) (r : Reg) : (s.tPeek k r).stk = s.stk := rfl

@[simp] theorem tPeek_reg_self (s : State) (k : Stk) (r : Reg) :
    (s.tPeek k r).reg r = (s.stk k).headD Glyph.eos := by simp [State.tPeek]

@[simp] theorem tPeek_reg_ne (s : State) (k : Stk) (r : Reg) {r' : Reg} (h : r' ≠ r) :
    (s.tPeek k r).reg r' = s.reg r' := by simp [State.tPeek, h]

@[simp] theorem tPop_reg_self (s : State) (k : Stk) (r : Reg) :
    (s.tPop k r).reg r = (s.stk k).headD Glyph.eos := by simp [State.tPop]

@[simp] theorem tPop_stk_self (s : State) (k : Stk) (r : Reg) :
    (s.tPop k r).stk k = (s.stk k).tail := by simp [State.tPop]

@[simp] theorem tPop_stk_ne (s : State) (k : Stk) (r : Reg) {j : Stk} (h : j ≠ k) :
    (s.tPop k r).stk j = s.stk j := by simp [State.tPop, h]

@[simp] theorem tPush_reg (s : State) (k : Stk) (r : Reg) : (s.tPush k r).reg = s.reg := rfl

@[simp] theorem tPush_stk_self (s : State) (k : Stk) (r : Reg) :
    (s.tPush k r).stk k = s.reg r :: s.stk k := by simp [State.tPush]

@[simp] theorem tPush_stk_ne (s : State) (k : Stk) (r : Reg) {j : Stk} (h : j ≠ k) :
    (s.tPush k r).stk j = s.stk j := by simp [State.tPush, h]

@[simp] theorem tSet_reg_self (s : State) (r : Reg) (c : Glyph) : (s.tSet r c).reg r = c := by
  simp [State.tSet]

@[simp] theorem tSet_reg_ne (s : State) (r : Reg) (c : Glyph) {r' : Reg} (h : r' ≠ r) :
    (s.tSet r c).reg r' = s.reg r' := by simp [State.tSet, h]

@[simp] theorem tSet_stk (s : State) (r : Reg) (c : Glyph) : (s.tSet r c).stk = s.stk := rfl

/-! ## `Unary` counters -/

theorem Unary_headD_eos (v : ℕ) (rest : List Glyph) :
    (Unary v rest).headD Glyph.eos = if v = 0 then gEnd else gTok := by
  cases v with
  | zero => simp [Unary]
  | succ v => simp [Unary_succ]

theorem Unary_headD_gTok {v : ℕ} (hv : v ≠ 0) (rest : List Glyph) :
    (Unary v rest).headD Glyph.eos = gTok := by
  rw [Unary_headD_eos, if_neg hv]

theorem Unary_tail_of_ne_zero {v : ℕ} (hv : v ≠ 0) (rest : List Glyph) :
    (Unary v rest).tail = Unary (v - 1) rest := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv
  rw [Unary_succ]; simp

/-! ## The fourteen commands of the loop body -/

abbrev lbC1 : Cmd := .peek sX rA

abbrev lbC2 : Cmd :=
  .ite rA (Shift.gmk sX) (.set rA (Glyph.bit false))
    (.seq (.pop sX rA)
      (.ite rA Glyph.iend (.seq (.push sR rA) (.set rA (Glyph.bit false))) (.push sR rA)))

abbrev lbC3 : Cmd := .push sZ rA

abbrev lbC4 : Cmd := .peek sCW rB

abbrev lbC5 : Cmd := .ite rB gEnd
    (seqs [.set rC_ch Glyph.cons, .push sS rC_ch, .set rC_ch Glyph.pos, .push sS rC_ch, .set rE gCont])
    (.set rE gStop)

abbrev lbC6 (copyProg : Cmd) : Cmd := .ite rE gCont copyProg .skip

abbrev lbC7 : Cmd := .pop sZ rA

abbrev lbC8 : Cmd := .push sS rA

abbrev lbC9 : Cmd := .pop sCW rB

abbrev lbC10 : Cmd := .peek sCW rB

abbrev lbC11 : Cmd := .ite rB gEnd
    (seqs [dropZerosProg sS rD, .set rC_ch Glyph.iend, .push sS rC_ch, .pop sCN rB]) .skip

abbrev lbC12 : Cmd := resetRegs

abbrev lbC13 : Cmd := .peek sCN rG

abbrev lbC14 : Cmd := .ite rG gEnd (.set rG gStop) (.set rG gCont)

theorem loopBody_eq (copyProg : Cmd) :
    loopBody copyProg =
      seqs [lbC1, lbC2, lbC3, lbC4, lbC5, lbC6 copyProg, lbC7, lbC8, lbC9, lbC10, lbC11, lbC12,
        lbC13, lbC14] := rfl

/-! ## List abbreviations for the loop-body state -/

/-- The bit pushed at position `k`. -/
abbrev lbBit (x b N k : ℕ) : Bool := (pbits x b N).getD k false

/-- The `[cons, pos]` header pushed when `k` opens a new group. -/
abbrev lbOpts (b k : ℕ) : List Glyph := if k % b = 0 then [Glyph.cons, Glyph.pos] else []

/-- The push order after consuming `k` positions and pushing the bit at position `k`. -/
abbrev lbL (x b N k : ℕ) : List Glyph :=
  outOrder (pbits x b N) b k ++ lbOpts b k ++ [Glyph.bit (lbBit x b N k)]

/-- The region of stack `sS` above its marker after `k` consumed positions. -/
abbrev lbSSrev (x b N k : ℕ) : List Glyph := (outOrder (pbits x b N) b k).reverse

/-- The region of stack `sS` above its marker once the bit at position `k` has been pushed, read
bottom-up (so the top of the stack is what was pushed last). -/
abbrev lbSSbody (x b N k : ℕ) : List Glyph :=
  if k % b = 0 then Glyph.pos :: Glyph.cons :: lbSSrev x b N k else lbSSrev x b N k

theorem lbL_reverse (x b N k : ℕ) :
    (lbL x b N k).reverse = Glyph.bit (lbBit x b N k) :: lbSSbody x b N k := by
  unfold lbL lbSSbody lbSSrev lbOpts
  by_cases h : k % b = 0
  · simp only [h, if_pos, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.singleton_append]
  · rw [if_neg h, if_neg h]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append]


/-! ## Block 1: reading one bit position -/

/-- Commands 1–3: read the next bit position, push it onto `sR`, save it on `sZ`. -/
theorem loopBodyFront (main : Cmd) (x b N k : ℕ) (Y : Stk → List Glyph) :
    ∃ (s : State) (n : ℕ), Ev main (seqs [lbC1, lbC2, lbC3]) (lSt x b N Y k) s n ∧ n ≤ 8 ∧
      s.stk sX = (streamOf x).drop (cg x (k + 1)) ++ Shift.gmk sX :: Y sX ∧
      s.stk sR = ((streamOf x).take (cg x (k + 1))).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR ∧
      s.stk sZ = Glyph.bit ((pbits x b N).getD k false) :: Shift.gmk sZ :: Y sZ ∧
      s.reg rA = Glyph.bit ((pbits x b N).getD k false) ∧
      (∀ r : Reg, r ≠ rA → s.reg r = lRegs x b N k r) ∧
      (∀ j : Stk, j ≠ sX → j ≠ sR → j ≠ sZ → s.stk j = lStk x b N Y k j) := by
  rcases lt_trichotomy k x.size with hlt | heq | hgt
  · -- k < x.size: a real bit is read off the stream
    have hd : (streamOf x).drop (cg x k) =
        Glyph.bit (x.bits.getD k false) :: (streamOf x).drop (k + 1) := by
      rw [cg_of_lt hlt]; exact streamOf_drop_lt hlt
    have hcg : cg x (k + 1) = k + 1 := by rw [cg_succ (le_of_lt hlt), cg_of_lt hlt]
    have hget : (pbits x b N).getD k false = x.bits.getD k false := pbits_getD_lt hlt
    have hrev : ((streamOf x).take (cg x (k + 1))).reverse =
        Glyph.bit (x.bits.getD k false) :: ((streamOf x).take (cg x k)).reverse := by
      rw [streamOf_take_succ_lt (b := b) (N := N) hlt, List.reverse_append,
        List.reverse_singleton, List.singleton_append, hget]
    have hsR0 : lStk x b N Y k sR =
        ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR :=
      lStk_sR x b N Y k
    have hsZ0 : lStk x b N Y k sZ = Shift.gmk sZ :: Y sZ := lStk_sZ x b N Y k
    let s0 : State := lSt x b N Y k
    let s1 : State := s0.tPeek sX rA
    let s2a : State := s1.tPop sX rA
    let s2 : State := s2a.tPush sR rA
    let s3 : State := s2.tPush sZ rA
    have hs0X : s0.stk sX = (streamOf x).drop (cg x k) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s0, lSt_stk]
    have hs0R : s0.stk sR = ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s0, lSt_stk, hsR0]
    have hs0Z : s0.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s0, lSt_stk, hsZ0]
    have hev1 : Ev main lbC1 s0 s1 1 := ⟨1, Eval.peek sX rA s0, le_rfl⟩
    have hs1rA : s1.reg rA = Glyph.bit (x.bits.getD k false) := by
      rw [show s1.reg rA = (s0.stk sX).headD Glyph.eos from by simp +decide [s1, State.tPeek],
        hs0X, hd]
      simp
    have hs1ne : s1.reg rA ≠ Shift.gmk sX := by rw [hs1rA]; exact Shift.bit_ne_gmk sX _
    have hs1X : s1.stk sX = (streamOf x).drop (cg x k) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s1, State.tPeek, hs0X]
    have hs1R : s1.stk sR = ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s1, State.tPeek, hs0R]
    have hs1Z : s1.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s1, State.tPeek, hs0Z]
    have hpop : Ev main (.pop sX rA) s1 s2a 1 := ⟨1, Eval.pop sX rA s1, le_rfl⟩
    have hs2arA : s2a.reg rA = Glyph.bit (x.bits.getD k false) := by
      rw [show s2a.reg rA = (s1.stk sX).headD Glyph.eos from by simp +decide [s2a, State.tPop],
        hs1X, hd]
      simp
    have hs2ane : s2a.reg rA ≠ Glyph.iend := by rw [hs2arA]; intro h; cases h
    have hs2aX : s2a.stk sX = (streamOf x).drop (k + 1) ++ Shift.gmk sX :: Y sX := by
      rw [show s2a.stk sX = (s1.stk sX).tail from by simp +decide [s2a, State.tPop], hs1X, hd]
      simp
    have hs2aR : s2a.stk sR = ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s2a, State.tPop, hs1R]
    have hs2aZ : s2a.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s2a, State.tPop, hs1Z]
    have hpushR : Ev main (.push sR rA) s2a s2 1 := ⟨1, Eval.push sR rA s2a, le_rfl⟩
    have hite2 : Ev main (.ite rA Glyph.iend
        (.seq (.push sR rA) (.set rA (Glyph.bit false))) (.push sR rA)) s2a s2 2 :=
      Ev.iteF hs2ane hpushR
    have hpopite : Ev main (.seq (.pop sX rA)
        (.ite rA Glyph.iend (.seq (.push sR rA) (.set rA (Glyph.bit false)))
          (.push sR rA))) s1 s2 3 := Ev.seq hpop hite2
    have hev2 : Ev main lbC2 s1 s2 4 := Ev.iteF hs1ne hpopite
    have hs2X : s2.stk sX = (streamOf x).drop (k + 1) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s2, State.tPush, hs2aX]
    have hs2rA : s2.reg rA = Glyph.bit (x.bits.getD k false) := by
      simp +decide [s2, State.tPush, hs2arA]
    have hs2R : s2.stk sR = Glyph.bit (x.bits.getD k false) ::
        (((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR) := by
      simp +decide [s2, State.tPush, hs2arA, hs2aR]
    have hs2Z : s2.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s2, State.tPush, hs2aZ]
    have hev3 : Ev main lbC3 s2 s3 1 := ⟨1, Eval.push sZ rA s2, le_rfl⟩
    have hs3X : s3.stk sX = (streamOf x).drop (cg x (k + 1)) ++ Shift.gmk sX :: Y sX := by
      rw [show s3.stk sX = s2.stk sX from by simp +decide [s3, State.tPush], hs2X, hcg]
    have hs3R : s3.stk sR = ((streamOf x).take (cg x (k + 1))).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by
      rw [show s3.stk sR = s2.stk sR from by simp +decide [s3, State.tPush], hs2R, hrev]
      simp
    have hs3Z : s3.stk sZ = Glyph.bit (x.bits.getD k false) :: Shift.gmk sZ :: Y sZ := by
      simp +decide [s3, State.tPush, hs2rA, hs2Z]
    have hs3rA : s3.reg rA = Glyph.bit (x.bits.getD k false) := by
      simp +decide [s3, State.tPush, hs2rA]
    have hs3reg : ∀ r : Reg, r ≠ rA → s3.reg r = lRegs x b N k r := by
      intro r hr
      have e1 : s3.reg r = s2.reg r := by simp +decide [s3, State.tPush]
      have e2 : s2.reg r = s2a.reg r := by simp +decide [s2, State.tPush]
      have e3 : s2a.reg r = s1.reg r := by simp +decide [s2a, State.tPop, hr]
      have e4 : s1.reg r = s0.reg r := by simp +decide [s1, State.tPeek, hr]
      have e5 : s0.reg r = lRegs x b N k r := by simp +decide [s0, lSt_reg]
      rw [e1, e2, e3, e4, e5]
    have hs3oth : ∀ j : Stk, j ≠ sX → j ≠ sR → j ≠ sZ → s3.stk j = lStk x b N Y k j := by
      intro j h1 h2 h3
      have e1 : s3.stk j = s2.stk j := by simp +decide [s3, State.tPush, h3]
      have e2 : s2.stk j = s2a.stk j := by simp +decide [s2, State.tPush, h2]
      have e3 : s2a.stk j = s1.stk j := by simp +decide [s2a, State.tPop, h1]
      have e4 : s1.stk j = s0.stk j := by simp +decide [s1, State.tPeek]
      have e5 : s0.stk j = lStk x b N Y k j := by simp +decide [s0, lSt_stk]
      rw [e1, e2, e3, e4, e5]
    have hchain : Ev main (seqs [lbC1, lbC2, lbC3]) s0 s3 (1 + (4 + 1)) :=
      Ev.seqs_cons hev1 (Ev.seqs_cons hev2 hev3)
    exact ⟨s3, 8, hchain.mono (by omega), by omega, hs3X, hs3R, by rw [hs3Z, hget], by rw [hs3rA, hget],
      hs3reg, hs3oth⟩
  · -- k = x.size: the stream is exhausted, `iend` is read
    subst heq
    have hd : (streamOf x).drop (cg x x.size) = [Glyph.iend] := streamOf_drop_eq x
    have hcg : cg x (x.size + 1) = x.size + 1 := by rw [cg_succ (le_refl x.size), cg_of_eq]
    have hdropnil : (streamOf x).drop (x.size + 1) = [] := streamOf_drop_gt (Nat.lt_succ_self _)
    have hget : (pbits x b N).getD x.size false = false := pbits_getD_ge (le_refl x.size)
    have htake : (streamOf x).take (cg x (x.size + 1)) =
        (streamOf x).take (cg x x.size) ++ [Glyph.iend] := streamOf_take_succ_eq x
    have hrev2 : ((streamOf x).take (cg x (x.size + 1))).reverse = Glyph.iend ::
        ((streamOf x).take (cg x x.size)).reverse := by
      rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append]
    have hsR0 : lStk x b N Y x.size sR =
        ((streamOf x).take (cg x x.size)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR :=
      lStk_sR x b N Y x.size
    have hsZ0 : lStk x b N Y x.size sZ = Shift.gmk sZ :: Y sZ := lStk_sZ x b N Y x.size
    let s0 : State := lSt x b N Y x.size
    let s1 : State := s0.tPeek sX rA
    let s2a : State := s1.tPop sX rA
    let s2b : State := s2a.tPush sR rA
    let s2 : State := s2b.tSet rA (Glyph.bit false)
    let s3 : State := s2.tPush sZ rA
    have hs0X : s0.stk sX = (streamOf x).drop (cg x x.size) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s0, lSt_stk]
    have hs0R : s0.stk sR = ((streamOf x).take (cg x x.size)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s0, lSt_stk, hsR0]
    have hs0Z : s0.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s0, lSt_stk, hsZ0]
    have hev1 : Ev main lbC1 s0 s1 1 := ⟨1, Eval.peek sX rA s0, le_rfl⟩
    have hs1rA : s1.reg rA = Glyph.iend := by
      rw [show s1.reg rA = (s0.stk sX).headD Glyph.eos from by simp +decide [s1, State.tPeek],
        hs0X, hd]
      simp
    have hs1ne : s1.reg rA ≠ Shift.gmk sX := by rw [hs1rA]; exact (Shift.gmk_ne_iend sX).symm
    have hs1X : s1.stk sX = (streamOf x).drop (cg x x.size) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s1, State.tPeek, hs0X]
    have hs1R : s1.stk sR = ((streamOf x).take (cg x x.size)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s1, State.tPeek, hs0R]
    have hs1Z : s1.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s1, State.tPeek, hs0Z]
    have hpop : Ev main (.pop sX rA) s1 s2a 1 := ⟨1, Eval.pop sX rA s1, le_rfl⟩
    have hs2arA : s2a.reg rA = Glyph.iend := by
      rw [show s2a.reg rA = (s1.stk sX).headD Glyph.eos from by simp +decide [s2a, State.tPop],
        hs1X, hd]
      simp
    have hs2aX : s2a.stk sX = Shift.gmk sX :: Y sX := by
      rw [show s2a.stk sX = (s1.stk sX).tail from by simp +decide [s2a, State.tPop], hs1X, hd]
      simp
    have hs2aR : s2a.stk sR = ((streamOf x).take (cg x x.size)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s2a, State.tPop, hs1R]
    have hs2aZ : s2a.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s2a, State.tPop, hs1Z]
    have hpushR : Ev main (.push sR rA) s2a s2b 1 := ⟨1, Eval.push sR rA s2a, le_rfl⟩
    have hset : Ev main (.set rA (Glyph.bit false)) s2b s2 1 := ⟨1, Eval.set rA _ s2b, le_rfl⟩
    have hite2 : Ev main (.ite rA Glyph.iend
        (.seq (.push sR rA) (.set rA (Glyph.bit false))) (.push sR rA)) s2a s2 3 :=
      Ev.iteT hs2arA (Ev.seq hpushR hset)
    have hpopite : Ev main (.seq (.pop sX rA)
        (.ite rA Glyph.iend (.seq (.push sR rA) (.set rA (Glyph.bit false)))
          (.push sR rA))) s1 s2 4 := Ev.seq hpop hite2
    have hev2 : Ev main lbC2 s1 s2 5 := Ev.iteF hs1ne hpopite
    have hs2bR : s2b.stk sR = Glyph.iend ::
        (((streamOf x).take (cg x x.size)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR) := by
      simp +decide [s2b, State.tPush, hs2arA, hs2aR]
    have hs2X : s2.stk sX = Shift.gmk sX :: Y sX := by
      simp +decide [s2, s2b, State.tSet, State.tPush, hs2aX]
    have hs2R : s2.stk sR = Glyph.iend ::
        (((streamOf x).take (cg x x.size)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR) := by
      simp +decide [s2, State.tSet, hs2bR]
    have hs2rA : s2.reg rA = Glyph.bit false := by simp +decide [s2, State.tSet]
    have hs2Z : s2.stk sZ = Shift.gmk sZ :: Y sZ := by
      simp +decide [s2, s2b, State.tSet, State.tPush, hs2aZ]
    have hev3 : Ev main lbC3 s2 s3 1 := ⟨1, Eval.push sZ rA s2, le_rfl⟩
    have hs3X : s3.stk sX = (streamOf x).drop (cg x (x.size + 1)) ++ Shift.gmk sX :: Y sX := by
      rw [show s3.stk sX = s2.stk sX from by simp +decide [s3, State.tPush], hs2X, hcg,
        hdropnil, List.nil_append]
    have hs3R : s3.stk sR = ((streamOf x).take (cg x (x.size + 1))).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by
      rw [show s3.stk sR = s2.stk sR from by simp +decide [s3, State.tPush], hs2R, hrev2]
      simp
    have hs3Z : s3.stk sZ = Glyph.bit false :: Shift.gmk sZ :: Y sZ := by
      simp +decide [s3, State.tPush, hs2rA, hs2Z]
    have hs3rA : s3.reg rA = Glyph.bit false := by simp +decide [s3, State.tPush, hs2rA]
    have hs3reg : ∀ r : Reg, r ≠ rA → s3.reg r = lRegs x b N x.size r := by
      intro r hr
      have e1 : s3.reg r = s2.reg r := by simp +decide [s3, State.tPush]
      have e2 : s2.reg r = s2b.reg r := by simp +decide [s2, State.tSet, hr]
      have e3 : s2b.reg r = s2a.reg r := by simp +decide [s2b, State.tPush]
      have e4 : s2a.reg r = s1.reg r := by simp +decide [s2a, State.tPop, hr]
      have e5 : s1.reg r = s0.reg r := by simp +decide [s1, State.tPeek, hr]
      have e6 : s0.reg r = lRegs x b N x.size r := by simp +decide [s0, lSt_reg]
      rw [e1, e2, e3, e4, e5, e6]
    have hs3oth : ∀ j : Stk, j ≠ sX → j ≠ sR → j ≠ sZ → s3.stk j = lStk x b N Y x.size j := by
      intro j h1 h2 h3
      have e1 : s3.stk j = s2.stk j := by simp +decide [s3, State.tPush, h3]
      have e2 : s2.stk j = s2b.stk j := by simp +decide [s2, State.tSet]
      have e3 : s2b.stk j = s2a.stk j := by simp +decide [s2b, State.tPush, h2]
      have e4 : s2a.stk j = s1.stk j := by simp +decide [s2a, State.tPop, h1]
      have e5 : s1.stk j = s0.stk j := by simp +decide [s1, State.tPeek]
      have e6 : s0.stk j = lStk x b N Y x.size j := by simp +decide [s0, lSt_stk]
      rw [e1, e2, e3, e4, e5, e6]
    have hchain : Ev main (seqs [lbC1, lbC2, lbC3]) s0 s3 (1 + (5 + 1)) :=
      Ev.seqs_cons hev1 (Ev.seqs_cons hev2 hev3)
    exact ⟨s3, 8, hchain.mono (by omega), by omega, hs3X, hs3R, by rw [hs3Z, hget],
      by rw [hs3rA, hget], hs3reg, hs3oth⟩
  · -- x.size < k: the stream is done, a padding zero is pushed
    have hd : (streamOf x).drop (cg x k) = [] := by
      rw [cg_of_gt hgt]; exact streamOf_drop_gt (Nat.lt_succ_self _)
    have hcg : cg x (k + 1) = cg x k := cg_succ_gt hgt
    have hget : (pbits x b N).getD k false = false := pbits_getD_ge (le_of_lt hgt)
    have hsR0 : lStk x b N Y k sR =
        ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++ Shift.gmk sR :: Y sR :=
      lStk_sR x b N Y k
    have hsZ0 : lStk x b N Y k sZ = Shift.gmk sZ :: Y sZ := lStk_sZ x b N Y k
    let s0 : State := lSt x b N Y k
    let s1 : State := s0.tPeek sX rA
    let s2 : State := s1.tSet rA (Glyph.bit false)
    let s3 : State := s2.tPush sZ rA
    have hs0X : s0.stk sX = (streamOf x).drop (cg x k) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s0, lSt_stk]
    have hs0R : s0.stk sR = ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by simp +decide [s0, lSt_stk, hsR0]
    have hs0Z : s0.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s0, lSt_stk, hsZ0]
    have hev1 : Ev main lbC1 s0 s1 1 := ⟨1, Eval.peek sX rA s0, le_rfl⟩
    have hs1rA : s1.reg rA = Shift.gmk sX := by
      rw [show s1.reg rA = (s0.stk sX).headD Glyph.eos from by simp +decide [s1, State.tPeek],
        hs0X, hd, List.nil_append]
      simp
    have hset : Ev main (.set rA (Glyph.bit false)) s1 s2 1 := ⟨1, Eval.set rA _ s1, le_rfl⟩
    have hev2 : Ev main lbC2 s1 s2 2 := Ev.iteT hs1rA hset
    have hs2X : s2.stk sX = (streamOf x).drop (cg x k) ++ Shift.gmk sX :: Y sX := by
      simp +decide [s2, State.tSet, hs0X, s1, State.tPeek]
    have hs2R : s2.stk sR = ((streamOf x).take (cg x k)).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by
      simp +decide [s2, State.tSet, hs0R, s1, State.tPeek]
    have hs2rA : s2.reg rA = Glyph.bit false := by simp +decide [s2, State.tSet]
    have hs2Z : s2.stk sZ = Shift.gmk sZ :: Y sZ := by
      simp +decide [s2, State.tSet, hs0Z, s1, State.tPeek]
    have hev3 : Ev main lbC3 s2 s3 1 := ⟨1, Eval.push sZ rA s2, le_rfl⟩
    have hs3X : s3.stk sX = (streamOf x).drop (cg x (k + 1)) ++ Shift.gmk sX :: Y sX := by
      rw [show s3.stk sX = s2.stk sX from by simp +decide [s3, State.tPush], hs2X, hcg]
    have hs3R : s3.stk sR = ((streamOf x).take (cg x (k + 1))).reverse ++ [Glyph.pos] ++
        Shift.gmk sR :: Y sR := by
      rw [show s3.stk sR = s2.stk sR from by simp +decide [s3, State.tPush], hs2R, hcg]
    have hs3Z : s3.stk sZ = Glyph.bit false :: Shift.gmk sZ :: Y sZ := by
      simp +decide [s3, State.tPush, hs2rA, hs2Z]
    have hs3rA : s3.reg rA = Glyph.bit false := by simp +decide [s3, State.tPush, hs2rA]
    have hs3reg : ∀ r : Reg, r ≠ rA → s3.reg r = lRegs x b N k r := by
      intro r hr
      have e1 : s3.reg r = s2.reg r := by simp +decide [s3, State.tPush]
      have e2 : s2.reg r = s1.reg r := by simp +decide [s2, State.tSet, hr]
      have e3 : s1.reg r = s0.reg r := by simp +decide [s1, State.tPeek, hr]
      have e4 : s0.reg r = lRegs x b N k r := by simp +decide [s0, lSt_reg]
      rw [e1, e2, e3, e4]
    have hs3oth : ∀ j : Stk, j ≠ sX → j ≠ sR → j ≠ sZ → s3.stk j = lStk x b N Y k j := by
      intro j h1 h2 h3
      have e1 : s3.stk j = s2.stk j := by simp +decide [s3, State.tPush, h3]
      have e2 : s2.stk j = s1.stk j := by simp +decide [s2, State.tSet]
      have e3 : s1.stk j = s0.stk j := by simp +decide [s1, State.tPeek]
      have e4 : s0.stk j = lStk x b N Y k j := by simp +decide [s0, lSt_stk]
      rw [e1, e2, e3, e4]
    have hchain : Ev main (seqs [lbC1, lbC2, lbC3]) s0 s3 (1 + (2 + 1)) :=
      Ev.seqs_cons hev1 (Ev.seqs_cons hev2 hev3)
    exact ⟨s3, 8, hchain.mono (by omega), by omega, hs3X, hs3R, by rw [hs3Z, hget],
      by rw [hs3rA, hget], hs3reg, hs3oth⟩

/-! ## Block 2: opening a new group and refilling the working counter -/

/-- Commands 4–6: if the working counter is empty, push the group header `[cons, pos]` and refill
the counter with `copyProg` (copying it from the counter `sCB`); otherwise set `rE` so that
`copyProg` is skipped. -/
theorem loopBodyCounter (main copyProg : Cmd) (KC : ℕ)
    (hcopy : ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (m : ℕ) (Ca Cb : List Glyph),
      X sCB = Unary m Ca → X sCW = gEnd :: Cb →
      ∃ (s' : State) (n : ℕ), Ev main copyProg ⟨g, X⟩ s' n ∧ n ≤ KC * (m + 1) ∧
        s'.stk sCB = Unary m Ca ∧ s'.stk sCW = Unary m Cb ∧
        (∀ k : Stk, k ≠ sCB → k ≠ sCW → s'.stk k = X k))
    (x b N k : ℕ) (hb : 1 ≤ b) (Ca : List Glyph) (Y : Stk → List Glyph) (s : State)
    (hsS : s.stk sS = lbSSrev x b N k ++ Shift.gmk sS :: Y sS)
    (hsCW : s.stk sCW = Unary (wcnt b k) (Shift.gmk sCW :: Y sCW))
    (hsCB : s.stk sCB = Unary b Ca) :
    ∃ (s' : State) (n : ℕ), Ev main (seqs [lbC4, lbC5, lbC6 copyProg]) s s' n ∧
      n ≤ 8 + (if k % b = 0 then KC * (b + 1) else 0) ∧
      s'.stk sS = lbSSbody x b N k ++ Shift.gmk sS :: Y sS ∧
      s'.stk sCW = (if k % b = 0 then Unary b (Shift.gmk sCW :: Y sCW)
        else Unary (wcnt b k) (Shift.gmk sCW :: Y sCW)) ∧
      s'.stk sCB = Unary b Ca ∧
      (∀ j : Stk, j ≠ sS → j ≠ sCW → j ≠ sCB → s'.stk j = s.stk j) := by
  by_cases hmod : k % b = 0
  · -- the working counter is exhausted: open a group and refill it
    have hw0 : wcnt b k = 0 := wcnt_eq_of_eq hmod
    let s4 : State := s.tPeek sCW rB
    let s5a : State := s4.tSet rC_ch Glyph.cons
    let s5b : State := s5a.tPush sS rC_ch
    let s5c : State := s5b.tSet rC_ch Glyph.pos
    let s5d : State := s5c.tPush sS rC_ch
    let s5 : State := s5d.tSet rE gCont
    have h4rB : s4.reg rB = gEnd := by
      rw [show s4.reg rB = (s.stk sCW).headD Glyph.eos from by simp +decide [s4, State.tPeek],
        hsCW, hw0]
      simp
    have h4S : s4.stk sS = lbSSrev x b N k ++ Shift.gmk sS :: Y sS := by
      simp +decide [s4, State.tPeek, hsS]
    have h4CW : s4.stk sCW = Unary (wcnt b k) (Shift.gmk sCW :: Y sCW) := by
      simp +decide [s4, State.tPeek, hsCW]
    have h4CB : s4.stk sCB = Unary b Ca := by simp +decide [s4, State.tPeek, hsCB]
    have h5rE : s5.reg rE = gCont := by simp +decide [s5, State.tSet]
    have h5S : s5.stk sS = lbSSbody x b N k ++ Shift.gmk sS :: Y sS := by
      simp +decide [s5, s5d, s5c, s5b, s5a, State.tSet, State.tPush, h4S, lbSSbody, if_pos hmod]
    have h5CW : s5.stk sCW = gEnd :: (Shift.gmk sCW :: Y sCW) := by
      simp +decide [s5, s5d, s5c, s5b, s5a, State.tSet, State.tPush, h4CW, hw0]
    have h5CB : s5.stk sCB = Unary b Ca := by
      simp +decide [s5, s5d, s5c, s5b, s5a, State.tSet, State.tPush, h4CB]
    obtain ⟨s6, n6, hev6, hn6, h6CB, h6CW, h6oth⟩ :=
      hcopy s5.reg s5.stk b Ca (Shift.gmk sCW :: Y sCW) h5CB h5CW
    have hev4 : Ev main lbC4 s s4 1 := ⟨1, Eval.peek sCW rB s, le_rfl⟩
    have hev5 : Ev main lbC5 s4 s5 6 := by
      have e1 : Ev main (.set rC_ch Glyph.cons) s4 s5a 1 := ⟨1, Eval.set rC_ch _ s4, le_rfl⟩
      have e2 : Ev main (.push sS rC_ch) s5a s5b 1 := ⟨1, Eval.push sS rC_ch s5a, le_rfl⟩
      have e3 : Ev main (.set rC_ch Glyph.pos) s5b s5c 1 := ⟨1, Eval.set rC_ch _ s5b, le_rfl⟩
      have e4 : Ev main (.push sS rC_ch) s5c s5d 1 := ⟨1, Eval.push sS rC_ch s5c, le_rfl⟩
      have e5 : Ev main (.set rE gCont) s5d s5 1 := ⟨1, Eval.set rE _ s5d, le_rfl⟩
      have hE : Ev main (seqs [.set rC_ch Glyph.cons, .push sS rC_ch, .set rC_ch Glyph.pos, .push sS rC_ch,
          .set rE gCont]) s4 s5 5 :=
        Ev.seq e1 (Ev.seq e2 (Ev.seq e3 (Ev.seq e4 e5)))
      exact Ev.iteT h4rB hE
    have hev6' : Ev main (lbC6 copyProg) s5 s6 (n6 + 1) := Ev.iteT h5rE hev6
    have h6S : s6.stk sS = lbSSbody x b N k ++ Shift.gmk sS :: Y sS := by
      rw [h6oth sS (by decide) (by decide), h5S]
    have h6CWu : s6.stk sCW = Unary b (Shift.gmk sCW :: Y sCW) := h6CW
    have h6frame : ∀ j : Stk, j ≠ sS → j ≠ sCW → j ≠ sCB → s6.stk j = s.stk j := by
      intro j h1 h2 h3
      have h6j : s6.stk j = s5.stk j := h6oth j h3 h2
      simp +decide [s4, State.tPeek, s5, s5d, s5c, s5b, s5a, State.tSet, State.tPush, h1, h6j]
    have hchain : Ev main (seqs [lbC4, lbC5, lbC6 copyProg]) s s6 (1 + (6 + (n6 + 1))) :=
      Ev.seqs_cons hev4 (Ev.seqs_cons hev5 hev6')
    refine ⟨s6, 8 + (if k % b = 0 then KC * (b + 1) else 0), hchain.mono (by rw [if_pos hmod]; omega),
      ?_, h6S, ?_, h6CB, h6frame⟩
    · exact le_rfl
    · rw [if_pos hmod]; exact h6CWu
  · -- the working counter still has units: nothing to do
    have hw0 : wcnt b k ≠ 0 := fun h0 => hmod ((wcnt_zero_iff hb).mp h0)
    let s4 : State := s.tPeek sCW rB
    let s5 : State := s4.tSet rE gStop
    let s6 : State := s5
    have h4rB : s4.reg rB = gTok := by
      rw [show s4.reg rB = (s.stk sCW).headD Glyph.eos from by simp +decide [s4, State.tPeek],
        hsCW, Unary_headD_gTok hw0]
    have h4rBne : s4.reg rB ≠ gEnd := by rw [h4rB]; exact gTok_ne_gEnd
    have h5rE : s5.reg rE = gStop := by simp +decide [s5, State.tSet]
    have h5ne : s5.reg rE ≠ gCont := by rw [h5rE]; exact gCont_ne_gStop.symm
    have h4S : s4.stk sS = lbSSrev x b N k ++ Shift.gmk sS :: Y sS := by
      simp +decide [s4, State.tPeek, hsS]
    have h4CW : s4.stk sCW = Unary (wcnt b k) (Shift.gmk sCW :: Y sCW) := by
      simp +decide [s4, State.tPeek, hsCW]
    have h4CB : s4.stk sCB = Unary b Ca := by simp +decide [s4, State.tPeek, hsCB]
    have hev4 : Ev main lbC4 s s4 1 := ⟨1, Eval.peek sCW rB s, le_rfl⟩
    have hev5 : Ev main lbC5 s4 s5 2 := Ev.iteF h4rBne (⟨1, Eval.set rE gStop s4, le_rfl⟩)
    have hev6 : Ev main (lbC6 copyProg) s5 s6 2 := Ev.iteF h5ne (⟨1, Eval.skip s5, le_rfl⟩)
    have h6S : s6.stk sS = lbSSbody x b N k ++ Shift.gmk sS :: Y sS := by
      simp +decide [s6, s5, State.tSet, h4S, lbSSbody, if_neg hmod]
    have h6CW : s6.stk sCW = (if k % b = 0 then Unary b (Shift.gmk sCW :: Y sCW)
        else Unary (wcnt b k) (Shift.gmk sCW :: Y sCW)) := by
      simp +decide [s6, s5, s4, State.tSet, State.tPeek, hsCW, if_neg hmod]
    have h6CB : s6.stk sCB = Unary b Ca := by
      simp +decide [s6, s5, s4, State.tSet, State.tPeek, hsCB]
    have h6frame : ∀ j : Stk, j ≠ sS → j ≠ sCW → j ≠ sCB → s6.stk j = s.stk j := by
      intro j h1 h2 h3
      simp +decide [s6, s5, s4, State.tSet, State.tPeek]
    have hchain : Ev main (seqs [lbC4, lbC5, lbC6 copyProg]) s s6 (1 + (2 + 2)) :=
      Ev.seqs_cons hev4 (Ev.seqs_cons hev5 hev6)
    refine ⟨s6, 8 + (if k % b = 0 then KC * (b + 1) else 0), hchain.mono (by omega), ?_, h6S, h6CW,
      h6CB, h6frame⟩
    · have hz : 0 ≤ (if k % b = 0 then KC * (b + 1) else 0) := Nat.zero_le _
      omega

/-! ## Block 3: pushing the bit, decrementing the counter, closing the group -/

/-- Commands 7–11: push the bit at position `k` onto `sS`, decrement the working counter, and close
the group (stripping the trailing zero bits and appending an `iend`) when the counter runs out. -/
theorem loopBodySS (main : Cmd) (x b N k : ℕ) (hb : 1 ≤ b) (hxN : x < 2 ^ (b * N))
    (hk : k < b * N) (Y : Stk → List Glyph) (s : State)
    (hsS : s.stk sS = lbSSbody x b N k ++ Shift.gmk sS :: Y sS)
    (hsCW : s.stk sCW = (if k % b = 0 then Unary b (Shift.gmk sCW :: Y sCW)
        else Unary (wcnt b k) (Shift.gmk sCW :: Y sCW)))
    (hsCN : s.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN))
    (hZ : s.stk sZ = Glyph.bit (lbBit x b N k) :: Shift.gmk sZ :: Y sZ) :
    ∃ (s' : State) (n : ℕ), Ev main (seqs [lbC7, lbC8, lbC9, lbC10, lbC11]) s s' n ∧
      n ≤ 6 + (if (k + 1) % b = 0 then 3 * b + 4 else 0) ∧
      s'.stk sS = (outOrder (pbits x b N) b (k + 1)).reverse ++ Shift.gmk sS :: Y sS ∧
      s'.stk sCW = Unary (wcnt b (k + 1)) (Shift.gmk sCW :: Y sCW) ∧
      s'.stk sCN = Unary (N - (k + 1) / b) (Shift.gmk sCN :: Y sCN) ∧
      s'.stk sZ = Shift.gmk sZ :: Y sZ ∧
      (∀ j : Stk, j ≠ sS → j ≠ sCW → j ≠ sCN → j ≠ sZ → s'.stk j = s.stk j) := by
  let s7 : State := s.tPop sZ rA
  let s8 : State := s7.tPush sS rA
  let s9 : State := s8.tPop sCW rB
  let s10 : State := s9.tPeek sCW rB
  have h7rA : s7.reg rA = Glyph.bit (lbBit x b N k) := by
    rw [show s7.reg rA = (s.stk sZ).headD Glyph.eos from by simp +decide [s7, State.tPop], hZ]
    simp
  have h7Z : s7.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s7, State.tPop, hZ]
  have h7S : s7.stk sS = lbSSbody x b N k ++ Shift.gmk sS :: Y sS := by
    simp +decide [s7, State.tPop, hsS]
  have h7CW : s7.stk sCW = (if k % b = 0 then Unary b (Shift.gmk sCW :: Y sCW)
      else Unary (wcnt b k) (Shift.gmk sCW :: Y sCW)) := by
    simp +decide [s7, State.tPop, hsCW]
  have h7CN : s7.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
    simp +decide [s7, State.tPop, hsCN]
  have hev7 : Ev main lbC7 s s7 1 := ⟨1, Eval.pop sZ rA s, le_rfl⟩
  have h8S : s8.stk sS = (lbL x b N k).reverse ++ Shift.gmk sS :: Y sS := by
    have e : s8.stk sS = Glyph.bit (lbBit x b N k) ::
        (lbSSbody x b N k ++ Shift.gmk sS :: Y sS) := by
      simp +decide [s8, State.tPush, h7rA, h7S]
    rw [e, lbL_reverse]
    simp
  have h8CW : s8.stk sCW = (if k % b = 0 then Unary b (Shift.gmk sCW :: Y sCW)
      else Unary (wcnt b k) (Shift.gmk sCW :: Y sCW)) := by
    simp +decide [s8, State.tPush, h7CW]
  have h8CN : s8.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
    simp +decide [s8, State.tPush, h7CN]
  have h8Z : s8.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s8, State.tPush, h7Z]
  have hev8 : Ev main lbC8 s7 s8 1 := ⟨1, Eval.push sS rA s7, le_rfl⟩
  have h9CW : s9.stk sCW = Unary (wcnt b (k + 1)) (Shift.gmk sCW :: Y sCW) := by
    rw [show s9.stk sCW = (s8.stk sCW).tail from by simp +decide [s9, State.tPop], h8CW]
    by_cases hmod : k % b = 0
    · rw [if_pos hmod, Unary_tail_of_ne_zero (by omega : b ≠ 0), wcnt_succ_open hb hmod]
    · have hw : wcnt b k ≠ 0 := fun h0 => hmod ((wcnt_zero_iff hb).mp h0)
      rw [if_neg hmod, Unary_tail_of_ne_zero hw, wcnt_succ_dec hb hmod]
  have h9S : s9.stk sS = (lbL x b N k).reverse ++ Shift.gmk sS :: Y sS := by
    simp +decide [s9, State.tPop, h8S]
  have h9CN : s9.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
    simp +decide [s9, State.tPop, h8CN]
  have h9Z : s9.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s9, State.tPop, h8Z]
  have hev9 : Ev main lbC9 s8 s9 1 := ⟨1, Eval.pop sCW rB s8, le_rfl⟩
  have h10rB : s10.reg rB = (if wcnt b (k + 1) = 0 then gEnd else gTok) := by
    rw [show s10.reg rB = (s9.stk sCW).headD Glyph.eos from by simp +decide [s10, State.tPeek],
      h9CW, Unary_headD_eos]
  have h10S : s10.stk sS = (lbL x b N k).reverse ++ Shift.gmk sS :: Y sS := by
    simp +decide [s10, State.tPeek, h9S]
  have h10CN : s10.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
    simp +decide [s10, State.tPeek, h9CN]
  have h10Z : s10.stk sZ = Shift.gmk sZ :: Y sZ := by simp +decide [s10, State.tPeek, h9Z]
  have hev10 : Ev main lbC10 s9 s10 1 := ⟨1, Eval.peek sCW rB s9, le_rfl⟩
  have hkp : k < (pbits x b N).length := by
    rw [pbits_length (Nat.size_le.mpr hxN)]; exact hk
  have hout := outOrderStepProved (pbits x b N) b k hb hkp
  by_cases h2 : (k + 1) % b = 0
  · -- the group closes here
    have hw0 : wcnt b (k + 1) = 0 := wcnt_eq_of_eq h2
    have h10rBg : s10.reg rB = gEnd := by rw [h10rB, if_pos hw0]
    obtain ⟨sdz, ndz, hevdz, hndz, hdzS, hdzoth⟩ :=
      sSdropZerosProof main x b N k hb Y s10.reg s10.stk h10S
    let si : State := sdz.tSet rC_ch Glyph.iend
    let sj : State := si.tPush sS rC_ch
    let sl : State := sj.tPop sCN rB
    have hdzCW : sdz.stk sCW = Unary (wcnt b (k + 1)) (Shift.gmk sCW :: Y sCW) := by
      simp +decide [s10, State.tPeek, hdzoth sCW (by decide), h9CW]
    have hdzZ : sdz.stk sZ = Shift.gmk sZ :: Y sZ := by
      simp +decide [s10, State.tPeek, hdzoth sZ (by decide), h9Z]
    have hdzCN : sdz.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
      simp +decide [hdzoth sCN (by decide), h10CN]
    have hsiS : si.stk sS = (Work.IntLib.stripFalses (lbL x b N k)).reverse ++
        Shift.gmk sS :: Y sS := by simp +decide [si, State.tSet, hdzS]
    have hsi_reg : si.reg rC_ch = Glyph.iend := by simp +decide [si, State.tSet]
    have hsjS : sj.stk sS = Glyph.iend ::
        ((Work.IntLib.stripFalses (lbL x b N k)).reverse ++ Shift.gmk sS :: Y sS) := by
      rw [show sj.stk sS = si.reg rC_ch :: si.stk sS from by simp +decide [sj, State.tPush],
        hsi_reg, hsiS]
    have hsjCN : sj.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
      simp +decide [sj, si, State.tPush, State.tSet, hdzCN]
    have hNpos : 1 ≤ N - k / b := (loopCounterArith b k N hb).2.2.2.2.1 hk h2
    have hslCN : sl.stk sCN = Unary (N - (k + 1) / b) (Shift.gmk sCN :: Y sCN) := by
      rw [show sl.stk sCN = (sj.stk sCN).tail from by simp +decide [sl, State.tPop], hsjCN,
        Unary_tail_of_ne_zero (by omega : N - k / b ≠ 0),
        (loopCounterArith b k N hb).1 h2, (loopCounterArith b k N hb).2.2.2.1]
    have hslS : sl.stk sS = Glyph.iend ::
        ((Work.IntLib.stripFalses (lbL x b N k)).reverse ++ Shift.gmk sS :: Y sS) := by
      rw [show sl.stk sS = sj.stk sS from by simp +decide [sl, State.tPop], hsjS]
    have hslS' : sl.stk sS = (outOrder (pbits x b N) b (k + 1)).reverse ++
        Shift.gmk sS :: Y sS := by
      rw [hslS, hout, if_pos h2, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      simp
    have hslCW : sl.stk sCW = Unary (wcnt b (k + 1)) (Shift.gmk sCW :: Y sCW) := by
      simp +decide [sl, sj, si, State.tPop, State.tPush, State.tSet, hdzCW]
    have hslZ : sl.stk sZ = Shift.gmk sZ :: Y sZ := by
      simp +decide [sl, sj, si, State.tPop, State.tPush, State.tSet, hdzZ]
    have hsloth : ∀ j : Stk, j ≠ sS → j ≠ sCW → j ≠ sCN → j ≠ sZ → sl.stk j = s.stk j := by
      intro j h1 h2' h3 h4
      have e0 : sdz.stk j = s10.stk j := hdzoth j h1
      have e1 : sl.stk j = sdz.stk j := by
        simp +decide [sl, sj, si, State.tPop, State.tPush, State.tSet, h1, h3]
      have e2 : s10.stk j = s9.stk j := by simp +decide [s10, State.tPeek]
      have e3 : s9.stk j = s8.stk j := by simp +decide [s9, State.tPop, h2']
      have e4 : s8.stk j = s7.stk j := by simp +decide [s8, State.tPush, h1]
      have e5 : s7.stk j = s.stk j := by simp +decide [s7, State.tPop, h4]
      rw [e1, e0, e2, e3, e4, e5]
    have hevset : Ev main (.set rC_ch Glyph.iend) sdz si 1 := ⟨1, Eval.set rC_ch _ sdz, le_rfl⟩
    have hevpush : Ev main (.push sS rC_ch) si sj 1 := ⟨1, Eval.push sS rC_ch si, le_rfl⟩
    have hevpop : Ev main (.pop sCN rB) sj sl 1 := ⟨1, Eval.pop sCN rB sj, le_rfl⟩
    have hG : Ev main (seqs [dropZerosProg sS rD, .set rC_ch Glyph.iend, .push sS rC_ch, .pop sCN rB])
        s10 sl (ndz + 3) := Ev.seq hevdz (Ev.seq hevset (Ev.seq hevpush hevpop))
    have hev11 : Ev main lbC11 s10 sl (ndz + 4) := Ev.iteT h10rBg hG
    have hevall : Ev main (seqs [lbC7, lbC8, lbC9, lbC10, lbC11]) s sl
        (1 + (1 + (1 + (1 + (ndz + 4))))) :=
      Ev.seq hev7 (Ev.seq hev8 (Ev.seq hev9 (Ev.seq hev10 hev11)))
    exact ⟨sl, 6 + (if (k + 1) % b = 0 then 3 * b + 4 else 0),
      hevall.mono (by rw [if_pos h2]; omega), le_rfl, hslS', hslCW, hslCN, hslZ, hsloth⟩
  · -- the group stays open
    have hw : wcnt b (k + 1) ≠ 0 := fun h0 => h2 ((wcnt_zero_iff hb).mp h0)
    have h10rBne : s10.reg rB ≠ gEnd := by
      rw [h10rB, if_neg hw]; exact gTok_ne_gEnd
    have hev11 : Ev main lbC11 s10 s10 2 := Ev.iteF h10rBne (⟨1, Eval.skip s10, le_rfl⟩)
    have hS' : s10.stk sS = (outOrder (pbits x b N) b (k + 1)).reverse ++
        Shift.gmk sS :: Y sS := by rw [h10S, hout, if_neg h2]
    have hCN' : s10.stk sCN = Unary (N - (k + 1) / b) (Shift.gmk sCN :: Y sCN) := by
      rw [h10CN, (loopCounterArith b k N hb).2.2.2.2.2 h2]
    have hCW' : s10.stk sCW = Unary (wcnt b (k + 1)) (Shift.gmk sCW :: Y sCW) := h9CW
    have hevall : Ev main (seqs [lbC7, lbC8, lbC9, lbC10, lbC11]) s s10
        (1 + (1 + (1 + (1 + 2)))) :=
      Ev.seq hev7 (Ev.seq hev8 (Ev.seq hev9 (Ev.seq hev10 hev11)))
    refine ⟨s10, 6 + (if (k + 1) % b = 0 then 3 * b + 4 else 0),
      hevall.mono (by rw [if_neg h2]), le_rfl, hS', hCW', hCN', h10Z, ?_⟩
    intro j h1 h2' h3 h4
    have e2 : s10.stk j = s9.stk j := by simp +decide [s10, State.tPeek]
    have e3 : s9.stk j = s8.stk j := by simp +decide [s9, State.tPop, h2']
    have e4 : s8.stk j = s7.stk j := by simp +decide [s8, State.tPush, h1]
    have e5 : s7.stk j = s.stk j := by simp +decide [s7, State.tPop, h4]
    rw [e2, e3, e4, e5]

/-! ## Block 4: resetting the registers and the loop test -/

/-- Commands 12–14: reset the register file, read the chunk counter and set `rG` so that the loop
continues exactly while chunks remain. -/
theorem loopBodyTail (main : Cmd) (x b N k : ℕ) (hb : 1 ≤ b) (hk : k < b * N)
    (Y : Stk → List Glyph) (s : State)
    (hsCN : s.stk sCN = Unary (N - (k + 1) / b) (Shift.gmk sCN :: Y sCN)) :
    ∃ (s' : State) (n : ℕ), Ev main (seqs [lbC12, lbC13, lbC14]) s s' n ∧ n ≤ 21 ∧
      s'.stk = s.stk ∧ s'.reg = lRegs x b N (k + 1) := by
  obtain ⟨sr, nr, hevr, hnr, hregr, hstkr⟩ := resetRegs_ev main s
  let sp : State := sr.tPeek sCN rG
  have hspCN : sp.stk sCN = Unary (N - (k + 1) / b) (Shift.gmk sCN :: Y sCN) := by
    simp +decide [sp, State.tPeek, hstkr, hsCN]
  have hspstk : sp.stk = s.stk := by simp +decide [sp, State.tPeek, hstkr]
  have hspreg : sp.reg rG = (if N - (k + 1) / b = 0 then gEnd else gTok) := by
    rw [show sp.reg rG = (sr.stk sCN).headD Glyph.eos from by simp +decide [sp, State.tPeek],
      show sr.stk sCN = Unary (N - (k + 1) / b) (Shift.gmk sCN :: Y sCN) from by
        simp +decide [hstkr, hsCN],
      Unary_headD_eos]
  have hev12 : Ev main lbC12 s sr nr := hevr
  have hev13 : Ev main lbC13 sr sp 1 := ⟨1, Eval.peek sCN rG sr, le_rfl⟩
  have hregr' : ∀ r : Reg, sr.reg r = Glyph.eos := hregr
  by_cases hcase : N - (k + 1) / b = 0
  · -- no chunks left: the loop stops
    let sf : State := sp.tSet rG gStop
    have hspg : sp.reg rG = gEnd := by rw [hspreg, if_pos hcase]
    have hev14 : Ev main lbC14 sp sf 2 := Ev.iteT hspg (⟨1, Eval.set rG gStop sp, le_rfl⟩)
    have hsfstk : sf.stk = s.stk := by simp +decide [sf, State.tSet, hspstk]
    have hsfreg : sf.reg = lRegs x b N (k + 1) := by
      funext r
      by_cases hr : r = rG
      · subst hr
        have hle : b * N ≤ k + 1 := ((loopCounterArith b k N hb).2.2.1).mp hcase
        rw [show sf.reg rG = gStop from by simp +decide [sf, State.tSet], lRegs_rG,
          if_neg (by omega)]
      · rw [show sf.reg r = Glyph.eos from by
            simp +decide [sf, sp, State.tSet, State.tPeek, hr, hregr'],
          lRegs_other x b N (k + 1) hr]
    have hevall : Ev main (seqs [lbC12, lbC13, lbC14]) s sf (nr + (1 + 2)) :=
      Ev.seq hev12 (Ev.seq hev13 hev14)
    exact ⟨sf, 21, hevall.mono (by omega), by omega, hsfstk, hsfreg⟩
  · -- chunks remain: the loop continues
    let sf : State := sp.tSet rG gCont
    have hspg : sp.reg rG ≠ gEnd := by rw [hspreg, if_neg hcase]; exact gTok_ne_gEnd
    have hev14 : Ev main lbC14 sp sf 2 := Ev.iteF hspg (⟨1, Eval.set rG gCont sp, le_rfl⟩)
    have hsfstk : sf.stk = s.stk := by simp +decide [sf, State.tSet, hspstk]
    have hsfreg : sf.reg = lRegs x b N (k + 1) := by
      funext r
      by_cases hr : r = rG
      · subst hr
        have hlt : k + 1 < b * N := by
          by_contra hc
          exact hcase (((loopCounterArith b k N hb).2.2.1).mpr (by omega))
        rw [show sf.reg rG = gCont from by simp +decide [sf, State.tSet], lRegs_rG, if_pos hlt]
      · rw [show sf.reg r = Glyph.eos from by
            simp +decide [sf, sp, State.tSet, State.tPeek, hr, hregr'],
          lRegs_other x b N (k + 1) hr]
    have hevall : Ev main (seqs [lbC12, lbC13, lbC14]) s sf (nr + (1 + 2)) :=
      Ev.seq hev12 (Ev.seq hev13 hev14)
    exact ⟨sf, 21, hevall.mono (by omega), by omega, hsfstk, hsfreg⟩

/-! ## The loop step -/

theorem loopBodyStep (main : HvdH.Cmd) (copyProg : HvdH.Cmd) (KC : ℕ)
    (hcopy : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (m : ℕ)
      (Ca Cb : List HvdH.Glyph),
      X Work.IntLib.sCB = Work.IntLib.Unary m Ca → X Work.IntLib.sCW = Work.IntLib.gEnd :: Cb →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main copyProg ⟨g, X⟩ s' n ∧ n ≤ KC * (m + 1) ∧
        s'.stk Work.IntLib.sCB = Work.IntLib.Unary m Ca ∧
        s'.stk Work.IntLib.sCW = Work.IntLib.Unary m Cb ∧
        (∀ k : HvdH.Stk, k ≠ Work.IntLib.sCB → k ≠ Work.IntLib.sCW → s'.stk k = X k))
    (x b N : ℕ) (hb : 1 ≤ b) (hxN : x < 2 ^ (b * N)) (Ca : List HvdH.Glyph) :
    ∀ (Y : HvdH.Stk → List HvdH.Glyph), Y Work.IntLib.sCB = Work.IntLib.Unary b Ca →
    ∀ (k : ℕ), k < b * N →
      Work.Layout.Ev main (Work.IntLib.loopBody copyProg)
        (Work.IntLib.lSt x b N Y k) (Work.IntLib.lSt x b N Y (k + 1))
        (Work.IntLib.cstep b KC k) := by
  intro Y hY k hk
  obtain ⟨s3, n3, hev3, hn3, h3sX, h3sR, h3sZ, h3rA, h3reg, h3oth⟩ := loopBodyFront main x b N k Y
  have h3sS : s3.stk sS = lbSSrev x b N k ++ Shift.gmk sS :: Y sS := by
    rw [h3oth sS (by decide) (by decide) (by decide), lStk_sS]
  have h3sCW : s3.stk sCW = Unary (wcnt b k) (Shift.gmk sCW :: Y sCW) := by
    rw [h3oth sCW (by decide) (by decide) (by decide), lStk_sCW]
  have h3sCB : s3.stk sCB = Unary b Ca := by
    rw [h3oth sCB (by decide) (by decide) (by decide),
      lStk_other x b N Y k (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hY
  obtain ⟨s6, n6, hev6, hn6, h6sS, h6sCW, h6sCB, h6oth⟩ :=
    loopBodyCounter main copyProg KC hcopy x b N k hb Ca Y s3 h3sS h3sCW h3sCB
  have h6sCN : s6.stk sCN = Unary (N - k / b) (Shift.gmk sCN :: Y sCN) := by
    rw [h6oth sCN (by decide) (by decide) (by decide),
      h3oth sCN (by decide) (by decide) (by decide), lStk_sCN]
  have h6sZ : s6.stk sZ = Glyph.bit (lbBit x b N k) :: Shift.gmk sZ :: Y sZ := by
    rw [h6oth sZ (by decide) (by decide) (by decide), h3sZ]
  obtain ⟨s11, n11, hev11, hn11, h11sS, h11sCW, h11sCN, h11sZ, h11oth⟩ :=
    loopBodySS main x b N k hb hxN hk Y s6 h6sS h6sCW h6sCN h6sZ
  obtain ⟨s14, n14, hev14, hn14, h14stk, h14reg⟩ := loopBodyTail main x b N k hb hk Y s11 h11sCN
  have hfin : s14 = lSt x b N Y (k + 1) := by
    obtain ⟨g, X⟩ := s14
    have hstk : X = lStk x b N Y (k + 1) := by
      have h14' : X = s11.stk := h14stk
      rw [h14']
      funext j
      by_cases h1 : j = sX
      · subst h1
        rw [h11oth sX (by decide) (by decide) (by decide) (by decide),
          h6oth sX (by decide) (by decide) (by decide), h3sX, lStk_sX]
      · by_cases h2 : j = sR
        · subst h2
          rw [h11oth sR (by decide) (by decide) (by decide) (by decide),
            h6oth sR (by decide) (by decide) (by decide), h3sR, lStk_sR]
        · by_cases h3 : j = sS
          · subst h3; rw [h11sS, lStk_sS]
          · by_cases h4 : j = sCW
            · subst h4; rw [h11sCW, lStk_sCW]
            · by_cases h5 : j = sCN
              · subst h5; rw [h11sCN, lStk_sCN]
              · by_cases h6 : j = sZ
                · subst h6; rw [h11sZ, lStk_sZ]
                · by_cases h7 : j = sCB
                  · subst h7
                    rw [h11oth sCB (by decide) (by decide) (by decide) (by decide), h6sCB,
                      lStk_other x b N Y (k + 1) (by decide) (by decide) (by decide) (by decide)
                        (by decide) (by decide),
                      ← hY]
                  · rw [h11oth j h3 h4 h5 h6, h6oth j h3 h4 h7, h3oth j h1 h2 h6,
                      lStk_other x b N Y (k + 1) h1 h2 h3 h4 h5 h6,
                      ← lStk_other x b N Y k h1 h2 h3 h4 h5 h6]
    have hreg : g = lRegs x b N (k + 1) := h14reg
    rw [hreg, hstk]
    rfl
  have hevall : Ev main (seqs ([lbC1, lbC2, lbC3] ++ [lbC4, lbC5, lbC6 copyProg] ++
      [lbC7, lbC8, lbC9, lbC10, lbC11] ++ [lbC12, lbC13, lbC14]))
      (lSt x b N Y k) s14 (((n3 + n6) + n11) + n14) :=
    seqsAppend (seqsAppend (seqsAppend hev3 hev6) hev11) hev14
  obtain ⟨m, hmEval, hmle⟩ := hevall
  refine ⟨m, ?_, ?_⟩
  · rw [loopBody_eq copyProg, ← hfin]
    exact hmEval
  · have hmain : ((n3 + n6) + n11) + n14 ≤ cstep b KC k := by
      rw [cstep]
      set D : ℕ := KC * (b + 1) with hD
      by_cases hmod : k % b = 0
      · rw [if_pos hmod] at hn6 ⊢
        by_cases h2 : (k + 1) % b = 0
        · rw [if_pos h2] at hn11 ⊢
          omega
        · rw [if_neg h2] at hn11 ⊢
          omega
      · rw [if_neg hmod] at hn6 ⊢
        by_cases h2 : (k + 1) % b = 0
        · rw [if_pos h2] at hn11 ⊢
          omega
        · rw [if_neg h2] at hn11 ⊢
          omega
    omega
