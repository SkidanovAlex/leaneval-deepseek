import Mathlib
import Submission.Work.IntLib.SizeShared
import Submission.Work.IntLib.eval_mvRevOnto

/-!
# Binary → unary conversion (`IntLib`, piece `sizeBinUnaryPiece`)

Read the binary expansion of `n` (behind an arbitrary sign glyph and delimited by `iend`) off
stack 0 and build the unary counter `toks n` on stack 1, in cost `O(n + n.size)`.

Algorithm.  The bit string is first reversed onto stack 4 (above a fresh marker), so that the
bits are consumed most-significant first; then Horner's rule `w ↦ 2w + b` is applied one bit at a
time to a unary counter `toks w` living on stack 1 above the marker `gA`.  Doubling a unary
counter is done by draining it onto stack 5 (above a marker `gEb`) and filling it back two tokens
per token, so the whole run costs `Σ_i O(w_i) = O(n)` tokens moved, plus one pass over the bits.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace Size

open HvdH

/-! ## Markers and registers -/

/-- Marker of the reversed bit region (stack 4). -/
abbrev gDb : Glyph := .mk 4
/-- Marker of the doubling scratch region (stack 5). -/
abbrev gEb : Glyph := .mk 5

theorem gTok_ne_gDb : gTok ≠ gDb := by decide
theorem gTok_ne_gEb : gTok ≠ gEb := by decide
theorem gDb_ne_gTok : gDb ≠ gTok := fun h => gTok_ne_gDb h.symm
theorem gEb_ne_gTok : gEb ≠ gTok := fun h => gTok_ne_gEb h.symm
theorem gA_ne_gDb : gA ≠ gDb := by decide
theorem gA_ne_gEb : gA ≠ gEb := by decide
theorem gDb_ne_gEb : gDb ≠ gEb := by decide
theorem gEb_ne_gDb : gEb ≠ gDb := fun h => gDb_ne_gEb h.symm
theorem gDb_ne_eos : gDb ≠ Glyph.eos := by decide
theorem gEb_ne_eos : gEb ≠ Glyph.eos := by decide
theorem eos_ne_gDb : Glyph.eos ≠ gDb := fun h => gDb_ne_eos h.symm
theorem bit_ne_gDb (b : Bool) : Glyph.bit b ≠ gDb := by cases b <;> decide
theorem bit_ne_gEb (b : Bool) : Glyph.bit b ≠ gEb := by cases b <;> decide
theorem bit_ne_iendB (b : Bool) : Glyph.bit b ≠ Glyph.iend := by cases b <;> decide
theorem iend_ne_gDb : Glyph.iend ≠ gDb := by decide
theorem iend_ne_gEb : Glyph.iend ≠ gEb := by decide
theorem gDb_ne_iend : gDb ≠ Glyph.iend := fun h => iend_ne_gDb h.symm
theorem bit_true_ne_bit_false : Glyph.bit true ≠ Glyph.bit false := by decide

theorem bit_false_ne_bit_true : Glyph.bit false ≠ Glyph.bit true :=
  fun h => bit_true_ne_bit_false h.symm

/-- Register of the discarded sign glyph. -/
abbrev rSg : Reg := 0
/-- Loop/test register of all three loops. -/
abbrev rL : Reg := 1
/-- Register holding the current bit glyph. -/
abbrev rBt : Reg := 2
/-- Scratch register for pushing markers. -/
abbrev rMk : Reg := 3

/-! ## `Eval` helpers in `updStk`/`updReg` form -/

theorem evalPopU {main : Cmd} {k : Stk} {r : Reg} {s : State} {g : Glyph} {rest : List Glyph}
    (h : s.stk k = g :: rest) :
    Eval main (.pop k r) s ((s.updStk k rest).updReg r g) 1 :=
  Eval.pop_cons h

theorem evalPushU {main : Cmd} {k : Stk} {r : Reg} {s : State} {g : Glyph}
    (h : s.reg r = g) : Eval main (.push k r) s (s.updStk k (g :: s.stk k)) 1 := by
  have h' := Eval.push (main := main) k r s
  rw [h] at h'
  exact h'

theorem evalSetU {main : Cmd} (r : Reg) (g : Glyph) (s : State) :
    Eval main (.set r g) s (s.updReg r g) 1 :=
  Eval.set r g s

theorem evalSkipU {main : Cmd} (s : State) : Eval main .skip s s 1 := Eval.skip s

theorem evalMovU {main : Cmd} (dst src : Reg) (s : State) :
    Eval main (.mov dst src) s (s.updReg dst (s.reg src)) 1 := Eval.mov dst src s

/-! ## List / `ofBits` facts -/

theorem ofBits_reverse_cons (b : Bool) (B : List Bool) :
    ofBits (b :: B).reverse = 2 ^ B.length * b.toNat + ofBits B.reverse := by
  have h1 : ofBits [b] = b.toNat := by simp [ofBits]
  rw [List.reverse_cons, ofBits_append, List.length_reverse, h1]
  ring

theorem ofBits_nil_eq_zero : ofBits ([] : List Bool) = 0 := rfl

/-! ## The doubling: drain loop -/

/-- One iteration of the drain loop: pop a glyph from the counter region; if it is the marker
`gA` push it back and stop, otherwise push it onto stack 5. -/
def drainBody : Cmd :=
  .seq (.pop 1 rL)
    (.ite rL gA (.seq (.push 1 rL) (.set rL gA))
      (.seq (.push 5 rL) (.set rL Glyph.eos)))

/-- Drain the unary counter of stack 1 onto stack 5 (loop register `rL`). -/
def drainLoop : Cmd := .loop rL Glyph.eos drainBody

theorem drainBody_cont (main : Cmd) (u : ℕ) (below1 below5 : List Glyph) (s : State)
    (h1 : s.stk 1 = toks (u + 1) ++ gA :: below1) (hr : s.reg rL = Glyph.eos) :
    ∃ s' : State, Eval main drainBody s s' 4 ∧ s'.stk 1 = toks u ++ gA :: below1 ∧
      s'.stk 5 = gTok :: s.stk 5 ∧ s'.reg rL = Glyph.eos ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  have h1' : s.stk 1 = gTok :: (toks u ++ gA :: below1) := by
    rw [h1, toks_succ, List.cons_append]
  let s1 : State := (s.updStk 1 (toks u ++ gA :: below1)).updReg rL gTok
  have e1 : Eval main (.pop 1 rL) s s1 1 := evalPopU h1'
  have hr1 : s1.reg rL = gTok := by simp [s1]
  let s2 : State := s1.updStk 5 (gTok :: s1.stk 5)
  have e2 : Eval main (.push 5 rL) s1 s2 1 := evalPushU (by rw [hr1])
  let s3 : State := s2.updReg rL Glyph.eos
  have e3 : Eval main (.set rL Glyph.eos) s2 s3 1 := evalSetU rL Glyph.eos s2
  have hite : Eval main (.ite rL gA (.seq (.push 1 rL) (.set rL gA))
      (.seq (.push 5 rL) (.set rL Glyph.eos))) s1 s3 3 :=
    Eval.iteF (by rw [hr1]; exact gTok_ne_gA) (Eval.seq e2 e3)
  refine ⟨s3, Eval.seq e1 hite, ?_, ?_, ?_, ?_⟩
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · intro k hk1 hk5
    simp [s3, s2, s1, State.updStk, State.updReg, hk1, hk5]

theorem drainBody_end (main : Cmd) (below1 below5 : List Glyph) (s : State)
    (h1 : s.stk 1 = gA :: below1) (hr : s.reg rL = Glyph.eos) :
    ∃ s' : State, Eval main drainBody s s' 4 ∧ s'.stk 1 = gA :: below1 ∧
      s'.stk 5 = s.stk 5 ∧ s'.reg rL = gA ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  let s1 : State := (s.updStk 1 below1).updReg rL gA
  have e1 : Eval main (.pop 1 rL) s s1 1 := evalPopU h1
  have hr1 : s1.reg rL = gA := by simp [s1]
  let s2 : State := s1.updStk 1 (gA :: s1.stk 1)
  have e2 : Eval main (.push 1 rL) s1 s2 1 := evalPushU (by rw [hr1])
  let s3 : State := s2.updReg rL gA
  have e3 : Eval main (.set rL gA) s2 s3 1 := evalSetU rL gA s2
  have hite : Eval main (.ite rL gA (.seq (.push 1 rL) (.set rL gA))
      (.seq (.push 5 rL) (.set rL Glyph.eos))) s1 s3 3 :=
    Eval.iteT (by rw [hr1]) (Eval.seq e2 e3)
  refine ⟨s3, Eval.seq e1 hite, ?_, ?_, ?_, ?_⟩
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · intro k hk1 hk5
    simp [s3, s2, s1, State.updStk, State.updReg, hk1, hk5]

theorem drainLoop_eval (main : Cmd) (u v : ℕ) (below1 below5 : List Glyph) (s : State)
    (h1 : s.stk 1 = toks u ++ gA :: below1) (h5 : s.stk 5 = toks v ++ gEb :: below5)
    (hr : s.reg rL = Glyph.eos) :
    ∃ s' c, Eval main drainLoop s s' c ∧ c ≤ 6 * (u + 1) ∧
      s'.stk 1 = gA :: below1 ∧ s'.stk 5 = toks (u + v) ++ gEb :: below5 ∧
      s'.reg rL = gA ∧ ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  induction u generalizing v s with
  | zero =>
    have h1' : s.stk 1 = gA :: below1 := by rw [h1]; rfl
    obtain ⟨s1, e1, ha, hb, hc, hd⟩ := drainBody_end main below1 below5 s h1' hr
    have hexit : s1.reg rL ≠ Glyph.eos := by rw [hc]; exact gA_ne_eos
    have hloop : Eval main drainLoop s s1 _ :=
      Eval.loopT (main := main) hr e1 (Eval.loopF (main := main) hexit)
    refine ⟨s1, _, hloop, by omega, ha, ?_, hc, hd⟩
    simp [hb, h5]
  | succ u ih =>
    obtain ⟨s1, e1, ha, hb, hc, hd⟩ := drainBody_cont main u below1 below5 s h1 hr
    obtain ⟨s2, c2, e2, hc2, ha2, hb2, hc2', hd2⟩ :=
      ih (v + 1) s1 ha (by rw [hb, h5, toks_succ]; rfl) hc
    have hloop : Eval main drainLoop s s2 _ :=
      Eval.loopT (main := main) hr e1 e2
    refine ⟨s2, _, hloop, ?_, ha2, ?_, hc2', ?_⟩
    · have : c2 ≤ 6 * (u + 1) := hc2
      omega
    · have h5e : u + (v + 1) = (u + 1) + v := by omega
      rw [hb2, h5e]
    · intro k hk1 hk5
      exact (hd2 k hk1 hk5).trans (hd k hk1 hk5)


/-! ## The doubling: fill loop -/

/-- One iteration of the fill loop: pop a glyph from the scratch region of stack 5; if it is the
marker `gEb` push it back and stop, otherwise push two tokens onto stack 1. -/
def fillBody : Cmd :=
  .seq (.pop 5 rL)
    (.ite rL gEb (.seq (.push 5 rL) (.set rL gEb))
      (.seq (.push 1 rL) (.seq (.push 1 rL) (.set rL Glyph.eos))))

/-- `toks (u+2)` is two tokens followed by `toks u`. -/
theorem toks_add_two (u : ℕ) : toks (u + 2) = gTok :: gTok :: toks u := by
  have h : u + 2 = (u + 1) + 1 := by omega
  rw [h, toks_succ, toks_succ]

/-- One iteration of the fill loop with a token on top of the scratch region of stack 5. -/
theorem fillBody_cont (main : Cmd) (v a : ℕ) (below1 below5 : List Glyph) (s : State)
    (h5 : s.stk 5 = toks (v + 1) ++ gEb :: below5) (h1 : s.stk 1 = toks a ++ gA :: below1)
    (_hr : s.reg rL = Glyph.eos) :
    ∃ s' : State, Eval main fillBody s s' 5 ∧ s'.stk 5 = toks v ++ gEb :: below5 ∧
      s'.stk 1 = toks (a + 2) ++ gA :: below1 ∧ s'.reg rL = Glyph.eos ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  have h5' : s.stk 5 = gTok :: (toks v ++ gEb :: below5) := by
    rw [h5, toks_succ, List.cons_append]
  let s1 : State := (s.updStk 5 (toks v ++ gEb :: below5)).updReg rL gTok
  have e1 : Eval main (.pop 5 rL) s s1 1 := evalPopU h5'
  have hr1 : s1.reg rL = gTok := by simp [s1, State.updStk, State.updReg]
  let s2 : State := s1.updStk 1 (gTok :: s1.stk 1)
  have e2 : Eval main (.push 1 rL) s1 s2 1 := evalPushU (by rw [hr1])
  let s3 : State := s2.updStk 1 (gTok :: s2.stk 1)
  have e3 : Eval main (.push 1 rL) s2 s3 1 := evalPushU (by simp [s2, State.updStk, hr1])
  let s4 : State := s3.updReg rL Glyph.eos
  have e4 : Eval main (.set rL Glyph.eos) s3 s4 1 := evalSetU rL Glyph.eos s3
  have hite : Eval main (.ite rL gEb (.seq (.push 5 rL) (.set rL gEb))
      (.seq (.push 1 rL) (.seq (.push 1 rL) (.set rL Glyph.eos)))) s1 s4 4 :=
    Eval.iteF (by rw [hr1]; exact gTok_ne_gEb) (Eval.seq e2 (Eval.seq e3 e4))
  refine ⟨s4, Eval.seq e1 hite, ?_, ?_, ?_, ?_⟩
  · simp [s4, s3, s2, s1, State.updStk, State.updReg]
  · have h : s4.stk 1 = gTok :: gTok :: (toks a ++ gA :: below1) := by
      simp [s4, s3, s2, s1, State.updStk, State.updReg, h1]
    rw [h, toks_add_two, List.cons_append, List.cons_append]
  · simp [s4, s3, s2, s1, State.updStk, State.updReg]
  · intro k hk1 hk5
    simp [s4, s3, s2, s1, State.updStk, State.updReg, hk1, hk5]

/-- The last iteration of the fill loop, when the scratch region is exhausted. -/
theorem fillBody_end (main : Cmd) (a : ℕ) (below1 below5 : List Glyph) (s : State)
    (h5 : s.stk 5 = gEb :: below5) (h1 : s.stk 1 = toks a ++ gA :: below1)
    (_hr : s.reg rL = Glyph.eos) :
    ∃ s' : State, Eval main fillBody s s' 4 ∧ s'.stk 5 = gEb :: below5 ∧
      s'.stk 1 = toks a ++ gA :: below1 ∧ s'.reg rL = gEb ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  let s1 : State := (s.updStk 5 below5).updReg rL gEb
  have e1 : Eval main (.pop 5 rL) s s1 1 := evalPopU h5
  have hr1 : s1.reg rL = gEb := by simp [s1, State.updStk, State.updReg]
  let s2 : State := s1.updStk 5 (gEb :: s1.stk 5)
  have e2 : Eval main (.push 5 rL) s1 s2 1 := evalPushU (by rw [hr1])
  let s3 : State := s2.updReg rL gEb
  have e3 : Eval main (.set rL gEb) s2 s3 1 := evalSetU rL gEb s2
  have hite : Eval main (.ite rL gEb (.seq (.push 5 rL) (.set rL gEb))
      (.seq (.push 1 rL) (.seq (.push 1 rL) (.set rL Glyph.eos)))) s1 s3 3 :=
    Eval.iteT (by rw [hr1]) (Eval.seq e2 e3)
  refine ⟨s3, Eval.seq e1 hite, ?_, ?_, ?_, ?_⟩
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · simp [s3, s2, s1, State.updStk, State.updReg, h1]
  · simp [s3, s2, s1, State.updStk, State.updReg]
  · intro k hk1 hk5
    simp [s3, s2, s1, State.updStk, State.updReg, hk1, hk5]

/-- Fill the unary counter of stack 1 back from the scratch region of stack 5, two tokens per
token. -/
def fillLoop : Cmd := .loop rL Glyph.eos fillBody

theorem fillLoop_eval (main : Cmd) (v a : ℕ) (below1 below5 : List Glyph) (s : State)
    (h5 : s.stk 5 = toks v ++ gEb :: below5) (h1 : s.stk 1 = toks a ++ gA :: below1)
    (hr : s.reg rL = Glyph.eos) :
    ∃ s' c, Eval main fillLoop s s' c ∧ c ≤ 6 * (v + 1) ∧
      s'.stk 5 = gEb :: below5 ∧ s'.stk 1 = toks (a + 2 * v) ++ gA :: below1 ∧
      s'.reg rL = gEb ∧ ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  induction v generalizing a s with
  | zero =>
    have h5' : s.stk 5 = gEb :: below5 := by rw [h5]; rfl
    obtain ⟨s1, e1, ha, hb, hc, hd⟩ := fillBody_end main a below1 below5 s h5' h1 hr
    have hexit : s1.reg rL ≠ Glyph.eos := by rw [hc]; exact gEb_ne_eos
    have hloop : Eval main fillLoop s s1 _ :=
      Eval.loopT (main := main) hr e1 (Eval.loopF (main := main) hexit)
    refine ⟨s1, _, hloop, by omega, ha, ?_, hc, hd⟩
    simp [hb]
  | succ v ih =>
    obtain ⟨s1, e1, ha, hb, hc, hd⟩ := fillBody_cont main v a below1 below5 s h5 h1 hr
    obtain ⟨s2, c2, e2, hc2, ha2, hb2, hc2', hd2⟩ := ih (a + 2) s1 ha hb hc
    have hloop : Eval main fillLoop s s2 _ :=
      Eval.loopT (main := main) hr e1 e2
    refine ⟨s2, _, hloop, ?_, ha2, ?_, hc2', ?_⟩
    · have : c2 ≤ 6 * (v + 1) := hc2
      omega
    · have he : (a + 2) + 2 * v = a + 2 * (v + 1) := by omega
      rw [hb2, he]
    · intro k hk1 hk5
      exact (hd2 k hk1 hk5).trans (hd k hk1 hk5)

/-! ## The doubling program -/

/-- Double the unary counter of stack 1, using stack 5 as scratch. -/
def doubleProg : Cmd :=
  .seq (.set rMk gEb)
    (.seq (.push 5 rMk)
      (.seq (.set rL Glyph.eos)
        (.seq drainLoop
          (.seq (.set rL Glyph.eos) (.seq fillLoop (.pop 5 rL))))))

theorem doubleProg_eval (main : Cmd) (u : ℕ) (below1 below5 : List Glyph) (s : State)
    (h1 : s.stk 1 = toks u ++ gA :: below1) (h5 : s.stk 5 = below5) :
    ∃ s' c, Eval main doubleProg s s' c ∧ c ≤ 20 * (u + 1) ∧
      s'.stk 1 = toks (2 * u) ++ gA :: below1 ∧ s'.stk 5 = below5 ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 5 → s'.stk k = s.stk k := by
  let s0 : State := s.updReg rMk gEb
  have e1 : Eval main (.set rMk gEb) s s0 1 := evalSetU rMk gEb s
  let s1 : State := s0.updStk 5 (gEb :: s0.stk 5)
  have e2 : Eval main (.push 5 rMk) s0 s1 1 := evalPushU (by simp [s0, State.updReg])
  have e3 : Eval main (.set rL Glyph.eos) s1 (s1.updReg rL Glyph.eos) 1 :=
    evalSetU rL Glyph.eos s1
  have hs1_1 : s1.stk 1 = toks u ++ gA :: below1 := by simp [s1, s0, State.updStk, State.updReg, h1]
  have hs1_5 : s1.stk 5 = toks 0 ++ gEb :: below5 := by
    simp [s1, s0, State.updStk, State.updReg, h5]
  have hr1 : (s1.updReg rL Glyph.eos).reg rL = Glyph.eos := by simp
  obtain ⟨s2, c2, e4, hc2, h2a, h2b, h2c, h2d⟩ :=
    drainLoop_eval main u 0 below1 below5 (s1.updReg rL Glyph.eos) hs1_1 hs1_5 hr1
  have e5 : Eval main (.set rL Glyph.eos) s2 (s2.updReg rL Glyph.eos) 1 :=
    evalSetU rL Glyph.eos s2
  have h2a' : (s2.updReg rL Glyph.eos).stk 1 = toks 0 ++ gA :: below1 := by
    simp [h2a]
  have h2b' : (s2.updReg rL Glyph.eos).stk 5 = toks u ++ gEb :: below5 := by
    have : u + 0 = u := by omega
    simp [h2b, this]
  have hr2 : (s2.updReg rL Glyph.eos).reg rL = Glyph.eos := by simp
  obtain ⟨s3, c3, e6, hc3, h3a, h3b, h3c, h3d⟩ :=
    fillLoop_eval main u 0 below1 below5 (s2.updReg rL Glyph.eos) h2b' h2a' hr2
  let s4 : State := (s3.updStk 5 below5).updReg rL gEb
  have e7 : Eval main (.pop 5 rL) s3 s4 1 := evalPopU h3a
  have hall := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
    (Eval.seq e5 (Eval.seq e6 e7)))))
  refine ⟨s4, _, hall, ?_, ?_, ?_, ?_⟩
  · have hc2' : c2 ≤ 6 * (u + 1) := hc2
    have hc3' : c3 ≤ 6 * (u + 1) := hc3
    omega
  · have h : s4.stk 1 = toks (0 + 2 * u) ++ gA :: below1 := by
      simp [s4, State.updStk, State.updReg, h3b]
    rw [h]
    simp
  · simp [s4, State.updStk, State.updReg, h3a]
  · intro k hk1 hk5
    have h : s4.stk k = s3.stk k := by simp [s4, State.updStk, State.updReg, hk5]
    have h3e : s3.stk k = (s2.updReg rL Glyph.eos).stk k := h3d k hk1 hk5
    have h2e : (s2.updReg rL Glyph.eos).stk k = (s1.updReg rL Glyph.eos).stk k := by
      have hh := h2d k hk1 hk5
      simpa using hh
    have h1e : (s1.updReg rL Glyph.eos).stk k = s1.stk k := rfl
    have hsf : s1.stk k = s.stk k := by simp [s1, s0, State.updStk, State.updReg, hk5]
    exact h.trans (h3e.trans (h2e.trans (h1e.trans hsf)))

/-! ## The Horner loop over the bits -/

/-- Add the current bit to the counter: push a token when the bit is `true`. -/
def addProg : Cmd := .ite rBt (Glyph.bit true) (.seq (.set rL gTok) (.push 1 rL)) .skip

theorem addProg_eval (main : Cmd) (b : Bool) (w : ℕ) (below1 : List Glyph) (s : State)
    (h1 : s.stk 1 = toks w ++ gA :: below1) (hr : s.reg rBt = Glyph.bit b) :
    ∃ s' c, Eval main addProg s s' c ∧ c ≤ 3 ∧
      s'.stk 1 = toks (w + b.toNat) ++ gA :: below1 ∧
      ∀ k : Stk, k ≠ 1 → s'.stk k = s.stk k := by
  cases b with
  | true =>
    let s1 : State := s.updReg rL gTok
    have e1 : Eval main (.set rL gTok) s s1 1 := evalSetU rL gTok s
    have hr1 : s1.reg rL = gTok := by simp [s1, State.updReg]
    let s2 : State := s1.updStk 1 (gTok :: s1.stk 1)
    have e2 : Eval main (.push 1 rL) s1 s2 1 := evalPushU (by rw [hr1])
    have hite : Eval main addProg s s2 (1 + 1 + 1) := by
      have h := Eval.iteT (c₁ := .seq (.set rL gTok) (.push 1 rL)) (c₂ := .skip)
        (show s.reg rBt = Glyph.bit true from hr) (Eval.seq e1 e2)
      simpa [addProg] using h
    refine ⟨s2, 3, hite, by omega, ?_, ?_⟩
    · have h : s2.stk 1 = gTok :: (toks w ++ gA :: below1) := by
        simp [s2, s1, State.updStk, State.updReg, h1]
      have hwt : w + true.toNat = w + 1 := by rfl
      rw [h, hwt, toks_succ, List.cons_append]
    · intro k hk1
      have h : s2.stk k = s.stk k := by simp [s2, s1, State.updStk, State.updReg, hk1]
      exact h
  | false =>
    have hite : Eval main addProg s s (1 + 1) := by
      have h : Eval main (.ite rBt (Glyph.bit true) (.seq (.set rL gTok) (.push 1 rL)) .skip)
          s s (1 + 1) :=
        Eval.iteF (c₁ := .seq (.set rL gTok) (.push 1 rL)) (c₂ := .skip)
          (show s.reg rBt ≠ Glyph.bit true from by rw [hr]; exact bit_false_ne_bit_true)
          (Eval.skip s)
      simpa [addProg] using h
    refine ⟨s, 2, hite, by omega, ?_, ?_⟩
    · have hwt : w + false.toNat = w := by rfl
      rw [hwt]
      exact h1
    · intro k hk1
      rfl

/-- Body of the Horner loop: consume one bit, double the counter and add the bit. -/
def outBody : Cmd :=
  .seq (.pop 4 rL)
    (.ite rL gDb (.seq (.push 4 rL) (.set rL gDb))
      (.seq (.push 4 rL)
        (.seq doubleProg
          (.seq (.pop 4 rBt) (.seq addProg (.set rL Glyph.eos))))))

/-- The Horner loop: consume the (most significant first) bits of stack 4 above the marker `gDb`,
maintaining the unary counter `toks w` on stack 1 (`w` = the value of the bits read so far). -/
def outLoop : Cmd := .loop rL Glyph.eos outBody

theorem outBody_cons (main : Cmd) (b : Bool) (B' : List Bool) (w : ℕ)
    (below1 below4 : List Glyph) (s : State)
    (h4 : s.stk 4 = bitsG (b :: B') ++ gDb :: below4)
    (h1 : s.stk 1 = toks w ++ gA :: below1) :
    ∃ s' c, Eval main outBody s s' c ∧ c ≤ 20 * (w + 1) + 9 ∧
      s'.stk 4 = bitsG B' ++ gDb :: below4 ∧
      s'.stk 1 = toks (2 * w + b.toNat) ++ gA :: below1 ∧
      s'.stk 5 = s.stk 5 ∧ s'.reg rL = Glyph.eos ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 4 → k ≠ 5 → s'.stk k = s.stk k := by
  have h4' : s.stk 4 = Glyph.bit b :: (bitsG B' ++ gDb :: below4) := by simpa using h4
  let s1 : State := (s.updStk 4 (bitsG B' ++ gDb :: below4)).updReg rL (Glyph.bit b)
  have e1 : Eval main (.pop 4 rL) s s1 1 := evalPopU h4'
  have hr1 : s1.reg rL = Glyph.bit b := by simp [s1, State.updStk, State.updReg]
  let s2 : State := s1.updStk 4 (Glyph.bit b :: s1.stk 4)
  have e2 : Eval main (.push 4 rL) s1 s2 1 := evalPushU (by rw [hr1])
  have hs2_1 : s2.stk 1 = toks w ++ gA :: below1 := by
    simp [s2, s1, State.updStk, State.updReg, h1]
  have hs2_4 : s2.stk 4 = Glyph.bit b :: (bitsG B' ++ gDb :: below4) := by
    simp [s2, s1, State.updStk, State.updReg]
  have hs2_5 : s2.stk 5 = s.stk 5 := by simp [s2, s1, State.updStk, State.updReg]
  obtain ⟨s3, c3, e3, hc3, h3_1, h3_5, h3_fr⟩ :=
    doubleProg_eval main w below1 (s.stk 5) s2 hs2_1 hs2_5
  have h3_4 : s3.stk 4 = Glyph.bit b :: (bitsG B' ++ gDb :: below4) := by
    rw [h3_fr 4 (by decide) (by decide)]
    exact hs2_4
  let s4 : State := (s3.updStk 4 (bitsG B' ++ gDb :: below4)).updReg rBt (Glyph.bit b)
  have e4 : Eval main (.pop 4 rBt) s3 s4 1 := evalPopU h3_4
  have hr4 : s4.reg rBt = Glyph.bit b := by simp [s4, State.updStk, State.updReg]
  have hs4_1 : s4.stk 1 = toks (2 * w) ++ gA :: below1 := by
    simp [s4, State.updStk, State.updReg, h3_1]
  obtain ⟨s5, c5, e5, hc5, h5a, h5f⟩ := addProg_eval main b (2 * w) below1 s4 hs4_1 hr4
  have h5_4 : s5.stk 4 = bitsG B' ++ gDb :: below4 := by
    rw [h5f 4 (by decide)]
    simp [s4, State.updStk, State.updReg]
  have h5_5 : s5.stk 5 = s.stk 5 := by
    rw [h5f 5 (by decide)]
    simp [s4, State.updStk, State.updReg, h3_5]
  let s6 : State := s5.updReg rL Glyph.eos
  have e6 : Eval main (.set rL Glyph.eos) s5 s6 1 := evalSetU rL Glyph.eos s5
  have hite : Eval main (.ite rL gDb (.seq (.push 4 rL) (.set rL gDb))
      (.seq (.push 4 rL) (.seq doubleProg (.seq (.pop 4 rBt) (.seq addProg (.set rL Glyph.eos))))))
      s1 s6 _ :=
    Eval.iteF (by rw [hr1]; exact bit_ne_gDb b)
      (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))
  have hall := Eval.seq e1 hite
  refine ⟨s6, _, hall, ?_, h5_4, h5a, h5_5, ?_, ?_⟩
  · have hc3' : c3 ≤ 20 * (w + 1) := hc3
    have hc5' : c5 ≤ 3 := hc5
    omega
  · simp [s6, State.updReg]
  · intro k hk1 hk4 hk5
    have h6 : s6.stk k = s5.stk k := rfl
    have h5' : s5.stk k = s4.stk k := h5f k hk1
    have h4' : s4.stk k = s3.stk k := by simp [s4, State.updStk, State.updReg, hk4]
    have h3' : s3.stk k = s2.stk k := h3_fr k hk1 hk5
    have h2' : s2.stk k = s1.stk k := by simp [s2, State.updStk, State.updReg, hk4]
    have h1' : s1.stk k = s.stk k := by simp [s1, State.updStk, State.updReg, hk4]
    exact h6.trans (h5'.trans (h4'.trans (h3'.trans (h2'.trans h1'))))

theorem outLoop_eval (main : Cmd) (B : List Bool) (w W : ℕ)
    (hW : W = w * 2 ^ B.length + ofBits B.reverse)
    (below1 below4 : List Glyph) (s : State)
    (h4 : s.stk 4 = bitsG B ++ gDb :: below4)
    (h1 : s.stk 1 = toks w ++ gA :: below1)
    (hr : s.reg rL = Glyph.eos) :
    ∃ s' c, Eval main outLoop s s' c ∧ c + 27 * w ≤ 28 * (W + 2 * B.length + 2) ∧
      s'.stk 4 = gDb :: below4 ∧ s'.stk 1 = toks W ++ gA :: below1 ∧
      s'.stk 5 = s.stk 5 ∧ s'.reg rL = gDb ∧
      ∀ k : Stk, k ≠ 1 → k ≠ 4 → k ≠ 5 → s'.stk k = s.stk k := by
  induction B generalizing w s with
  | nil =>
    have h4' : s.stk 4 = gDb :: below4 := by simpa using h4
    let s1 : State := (s.updStk 4 below4).updReg rL gDb
    have e1 : Eval main (.pop 4 rL) s s1 1 := evalPopU h4'
    have hr1 : s1.reg rL = gDb := by simp [s1, State.updStk, State.updReg]
    let s2 : State := s1.updStk 4 (gDb :: s1.stk 4)
    have e2 : Eval main (.push 4 rL) s1 s2 1 := evalPushU (by rw [hr1])
    let s3 : State := s2.updReg rL gDb
    have e3 : Eval main (.set rL gDb) s2 s3 1 := evalSetU rL gDb s2
    have hite : Eval main (.ite rL gDb (.seq (.push 4 rL) (.set rL gDb))
        (.seq (.push 4 rL) (.seq doubleProg (.seq (.pop 4 rBt) (.seq addProg (.set rL Glyph.eos))))))
        s1 s3 _ :=
      Eval.iteT (by rw [hr1]) (Eval.seq e2 e3)
    have hall := Eval.seq e1 hite
    have hexit : s3.reg rL ≠ Glyph.eos := by
      have h : s3.reg rL = gDb := by simp [s3, State.updReg]
      rw [h]; exact gDb_ne_eos
    have hloop : Eval main outLoop s s3 _ :=
      Eval.loopT (main := main) hr hall (Eval.loopF (main := main) hexit)
    have hWw : W = w := by rw [hW]; simp [ofBits]
    refine ⟨s3, _, hloop, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h0 : W + 2 * ([] : List Bool).length + 2 = w + 2 := by rw [hWw]; simp
      rw [h0]
      omega
    · simp [s3, s2, s1, State.updStk, State.updReg]
    · have h1s : s3.stk 1 = toks w ++ gA :: below1 := by
        simp [s3, s2, s1, State.updStk, State.updReg, h1]
      rw [h1s, hWw]
    · simp [s3, s2, s1, State.updStk, State.updReg]
    · simp [s3, State.updReg]
    · intro k hk1 hk4 hk5
      simp [s3, s2, s1, State.updStk, State.updReg, hk1, hk4, hk5]
  | cons b B' ih =>
    obtain ⟨s1, c1, e1, hc1, h4a, h1a, h5a, hr1, hfr1⟩ :=
      outBody_cons main b B' w below1 below4 s h4 h1
    have hW' : W = (2 * w + b.toNat) * 2 ^ B'.length + ofBits B'.reverse := by
      have hpow : 2 ^ (B'.length + 1) = 2 ^ B'.length * 2 := pow_succ 2 B'.length
      rw [hW, List.length_cons, ofBits_reverse_cons, hpow]
      ring
    obtain ⟨s2, c2, e2, hc2, h4b, h1b, h5b, hr2, hfr2⟩ :=
      ih (2 * w + b.toNat) hW' s1 h4a h1a hr1
    have hloop : Eval main outLoop s s2 _ :=
      Eval.loopT (main := main) hr e1 e2
    refine ⟨s2, _, hloop, ?_, h4b, h1b, ?_, hr2, ?_⟩
    · have hc1' : c1 ≤ 20 * (w + 1) + 9 := hc1
      have hlen : (b :: B').length = B'.length + 1 := by simp
      rw [hlen]
      clear hW hW' hlen
      omega
    · exact h5b.trans h5a
    · intro k hk1 hk4 hk5
      exact (hfr2 k hk1 hk4 hk5).trans (hfr1 k hk1 hk4 hk5)

end Size

open HvdH
open Work.IntLib.Size

/-! ## The piece -/

/-- The whole program: drop the sign, reverse the bit region onto stack 4 above `gDb`, initialise
the counter on stack 1, run the Horner loop, drop the marker of stack 4. -/
def binUnaryProg : Cmd :=
  .seq (.pop 0 rSg)
    (.seq (.set rMk gDb)
      (.seq (.push 4 rMk)
        (.seq (mvRevOnto 0 Glyph.iend 4 rL)
          (.seq (.set rMk gA)
            (.seq (.push 1 rMk)
              (.seq (.set rL Glyph.eos)
                (.seq outLoop (.pop 4 rL))))))))

theorem sizeBinUnaryPiece : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (n : ℕ) (sg : HvdH.Glyph)
    (below0 below1 : List HvdH.Glyph) (s : HvdH.State),
  s.stk 0 = sg :: (Computability.encodeNat n).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ below0 →
  s.stk 1 = below1 →
  ∃ (s' : HvdH.State) (c : ℕ), HvdH.Eval main prog s s' c ∧ c ≤ K * (n + n.size + 1) ∧
    s'.stk 0 = below0 ∧ s'.stk 1 = Work.IntLib.Size.toks n ++ Work.IntLib.Size.gA :: below1 ∧
    ∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k := by
  refine ⟨binUnaryProg, 128, ?_⟩
  intro main n sg below0 below1 s h0 h1
  have hbits : ∀ g ∈ (Computability.encodeNat n).map Glyph.bit, g ≠ Glyph.iend := by
    intro g hg
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    exact bit_ne_iendB b
  -- 1. drop the sign
  let s1 : State := (s.updStk 0 ((Computability.encodeNat n).map Glyph.bit ++ [Glyph.iend] ++ below0)).updReg rSg sg
  have e1 : Eval main (.pop 0 rSg) s s1 1 := evalPopU h0
  have hs1_0 : s1.stk 0 = (Computability.encodeNat n).map Glyph.bit ++ [Glyph.iend] ++ below0 := by
    simp [s1, State.updStk, State.updReg]
  -- 2./3. push the marker gDb on stack 4
  have e2 : Eval main (.set rMk gDb) s1 (s1.updReg rMk gDb) 1 := evalSetU rMk gDb s1
  let s2 : State := (s1.updReg rMk gDb).updStk 4 (gDb :: s1.stk 4)
  have e3 : Eval main (.push 4 rMk) (s1.updReg rMk gDb) s2 1 :=
    evalPushU (by simp [s1, State.updReg])
  have hs2_4 : s2.stk 4 = gDb :: s.stk 4 := by
    simp [s2, s1, State.updStk, State.updReg]
  have hs2_0 : s2.stk 0 = (Computability.encodeNat n).map Glyph.bit ++ Glyph.iend :: below0 := by
    have h : s2.stk 0 = (Computability.encodeNat n).map Glyph.bit ++ [Glyph.iend] ++ below0 := by
      simp [s2, s1, State.updStk, State.updReg]
    rw [h, List.append_assoc]
    rfl
  -- 4. reverse the bit region onto stack 4
  obtain ⟨s3, c3, e4, hc3, hs3_0, hs3_4, hfr3⟩ :=
    eval_mvRevOnto main 0 Glyph.iend 4 rL ((Computability.encodeNat n).map Glyph.bit)
      below0 (gDb :: s.stk 4) s2 hbits hs2_0 hs2_4 (by decide)
  have hs3_1 : s3.stk 1 = below1 := by
    rw [hfr3 1 (by decide) (by decide)]
    simp [s2, s1, State.updStk, State.updReg, h1]
  have hs3_5 : s3.stk 5 = s.stk 5 := by
    rw [hfr3 5 (by decide) (by decide)]
    simp [s2, s1, State.updStk, State.updReg]
  -- 5./6. marker gA at the bottom of the counter region of stack 1
  have e5 : Eval main (.set rMk gA) s3 (s3.updReg rMk gA) 1 := evalSetU rMk gA s3
  let s4 : State := (s3.updReg rMk gA).updStk 1 (gA :: s3.stk 1)
  have e6 : Eval main (.push 1 rMk) (s3.updReg rMk gA) s4 1 :=
    evalPushU (by simp [State.updReg])
  have hs4_1 : s4.stk 1 = toks 0 ++ gA :: below1 := by
    simp [s4, State.updStk, State.updReg, hs3_1]
  have hs4_4 : s4.stk 4 = ((Computability.encodeNat n).map Glyph.bit).reverse ++ gDb :: s.stk 4 := by
    have h : s4.stk 4 = s3.stk 4 := by simp [s4, State.updStk, State.updReg]
    rw [h, hs3_4]
  -- 7. initialise the loop register
  have e7 : Eval main (.set rL Glyph.eos) s4 (s4.updReg rL Glyph.eos) 1 :=
    evalSetU rL Glyph.eos s4
  have hB4 : (s4.updReg rL Glyph.eos).stk 4 =
      bitsG ((Computability.encodeNat n).reverse) ++ gDb :: s.stk 4 := by
    have h : s4.stk 4 = ((Computability.encodeNat n).reverse).map Glyph.bit ++ gDb :: s.stk 4 := by
      rw [hs4_4, ← List.map_reverse]
    exact h
  have hB1 : (s4.updReg rL Glyph.eos).stk 1 = toks 0 ++ gA :: below1 := by
    simp [s4, State.updStk, State.updReg, hs3_1]
  have hBr : (s4.updReg rL Glyph.eos).reg rL = Glyph.eos := by simp
  have hW : n = 0 * 2 ^ ((Computability.encodeNat n).reverse).length +
      ofBits ((Computability.encodeNat n).reverse).reverse := by
    rw [encodeNat_eq_bits, List.reverse_reverse, ofBits_bits_eq]
    simp
  -- 8. the Horner loop
  obtain ⟨s5, c5, e8, hc5, hs5_4, hs5_1, hs5_5, hr5, hfr5⟩ :=
    outLoop_eval main ((Computability.encodeNat n).reverse) 0 n hW below1 (s.stk 4)
      (s4.updReg rL Glyph.eos) hB4 hB1 hBr
  -- 9. drop the marker of stack 4
  let s6 : State := (s5.updStk 4 (s.stk 4)).updReg rL gDb
  have e9 : Eval main (.pop 4 rL) s5 s6 1 := evalPopU hs5_4
  have hall : Eval main binUnaryProg s s6
      (1 + (1 + (1 + (c3 + (1 + (1 + (1 + (c5 + 1)))))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
      (Eval.seq e7 (Eval.seq e8 e9)))))))
  have hc3' : c3 ≤ 6 * (n.size + 1) + 9 := by
    have h := hc3
    rwa [encodeNat_map_bit_length] at h
  have hc5' : c5 ≤ 28 * (n + 2 * n.size + 2) := by
    have h := hc5
    have hlen : ((Computability.encodeNat n).reverse).length = n.size := by
      simp [encodeNat_length]
    rw [hlen] at h
    omega
  refine ⟨s6, _, hall, ?_, ?_, ?_, ?_⟩
  · have h3 := hc3'
    have h5' := hc5'
    omega
  · have h : s6.stk 0 = s5.stk 0 := by simp [s6, State.updStk, State.updReg]
    have h2 : s5.stk 0 = (s4.updReg rL Glyph.eos).stk 0 :=
      hfr5 0 (by decide) (by decide) (by decide)
    have h3 : (s4.updReg rL Glyph.eos).stk 0 = s4.stk 0 := rfl
    have h4 : s4.stk 0 = s3.stk 0 := by simp [s4, State.updStk, State.updReg]
    exact h.trans (h2.trans (h3.trans (h4.trans hs3_0)))
  · have h : s6.stk 1 = s5.stk 1 := by simp [s6, State.updStk, State.updReg]
    rw [h, hs5_1]
  · intro k hk0 hk1
    by_cases hk4 : k = 4
    · subst hk4
      simp [s6, State.updStk, State.updReg]
    by_cases hk5 : k = 5
    · subst hk5
      have hA : s6.stk 5 = s5.stk 5 := by simp [s6, State.updStk, State.updReg, hk4]
      have hC : (s4.updReg rL Glyph.eos).stk 5 = s4.stk 5 := rfl
      have hD : s4.stk 5 = s3.stk 5 := by simp [s4, State.updStk, State.updReg]
      exact hA.trans (hs5_5.trans (hC.trans (hD.trans hs3_5)))
    · have hA : s6.stk k = s5.stk k := by simp [s6, State.updStk, State.updReg, hk4]
      have hB : s5.stk k = (s4.updReg rL Glyph.eos).stk k := hfr5 k hk1 hk4 hk5
      have hC : (s4.updReg rL Glyph.eos).stk k = s4.stk k := rfl
      have hD : s4.stk k = s3.stk k := by simp [s4, State.updStk, State.updReg, hk1]
      have hE : s3.stk k = s2.stk k := hfr3 k hk0 hk4
      have hF : s2.stk k = s1.stk k := by simp [s2, State.updStk, State.updReg, hk4]
      have hG : s1.stk k = s.stk k := by simp [s1, State.updStk, State.updReg, hk0]
      exact hA.trans (hB.trans (hC.trans (hD.trans (hE.trans (hF.trans hG)))))

end Work.IntLib
