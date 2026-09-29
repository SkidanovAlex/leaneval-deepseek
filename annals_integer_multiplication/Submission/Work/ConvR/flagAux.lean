import Mathlib
import Submission.Work.ConvR.flagDefs

/-!
# ConvR: auxiliary lemmas for the "trivial array" flag word

Straight-line `Eval` lemmas for the three cases of `flagDecide`, the component facts about the
resulting states, and the small semantic facts about `InDiscArr` used by the post-condition.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## The individual steps of `flagDecide` -/

theorem eval_fdP (main : Cmd) {s : State} {T : List Glyph} (h : s.stk 0 = Glyph.cons :: T) :
    Eval main (Cmd.peek 0 1) s (fdP s) 1 := by
  have hst : State.tPeek s 0 1 = fdP s := by simp [fdP, State.tPeek, h]
  rw [← hst]
  exact Eval.peek 0 1 s

theorem eval_fdQ (main : Cmd) (s : State) :
    Eval main (Cmd.push 1 1) (fdP s) (fdQ s) 1 := by
  have hst : State.tPush (fdP s) 1 1 = fdQ s := by simp [fdQ, fdP, State.tPush]
  rw [← hst]
  exact Eval.push 1 1 (fdP s)

theorem eval_fdR (main : Cmd) {s : State} {g : Glyph} {T : List Glyph}
    (h : s.stk 0 = Glyph.cons :: g :: T) :
    Eval main (Cmd.pop 0 1) (fdQ s) (fdR s g T) 1 := by
  have hst : State.tPop (fdQ s) 0 1 = fdR s g T := by simp [fdR, fdQ, fdP, State.tPop, h]
  rw [← hst]
  exact Eval.pop 0 1 (fdQ s)

theorem eval_fdS (main : Cmd) {s : State} {g : Glyph} {T : List Glyph}
    (h : s.stk 0 = Glyph.cons :: g :: T) :
    Eval main (Cmd.peek 0 1) (fdR s g T) (fdS s g T) 1 := by
  have hst : State.tPeek (fdR s g T) 0 1 = fdS s g T := by
    simp [fdS, fdR, fdQ, fdP, State.tPeek, h]
  rw [← hst]
  exact Eval.peek 0 1 (fdR s g T)

/-! ## The three cases -/

theorem eval_flagDecide_nil (main : Cmd) {T : List Glyph} {s : State}
    (h : s.stk 0 = Glyph.nil :: T) : Eval main flagDecide s (flagNilOut s) 3 := by
  have hp : Eval main (Cmd.peek 0 1) s (s.updReg 1 Glyph.nil) 1 := by
    have hst : State.tPeek s 0 1 = s.updReg 1 Glyph.nil := by simp [State.tPeek, h]
    rw [← hst]; exact Eval.peek 0 1 s
  have hs : Eval main (Cmd.set 2 Glyph.pos) (s.updReg 1 Glyph.nil) (flagNilOut s) 1 := by
    have hst : State.tSet (s.updReg 1 Glyph.nil) 2 Glyph.pos = flagNilOut s := by
      simp [flagNilOut, State.tSet]
    rw [← hst]; exact Eval.set 2 Glyph.pos (s.updReg 1 Glyph.nil)
  have hi : Eval main (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos)
      (Cmd.ite 1 Glyph.cons
        (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
          (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
        (Cmd.set 2 Glyph.pos)))
      (s.updReg 1 Glyph.nil) (flagNilOut s) 2 := Eval.iteT (by simp) hs
  exact Eval.seq hp hi

theorem eval_flagDecide_rowNil (main : Cmd) (T : List Glyph) (s : State)
    (h : s.stk 0 = Glyph.cons :: Glyph.nil :: T) :
    Eval main flagDecide s (flagRowNilOut s T) 8 := by
  have hp : Eval main (Cmd.peek 0 1) s (fdP s) 1 := eval_fdP main h
  have hq : Eval main (Cmd.push 1 1) (fdP s) (fdQ s) 1 := eval_fdQ main s
  have hr : Eval main (Cmd.pop 0 1) (fdQ s) (fdR s Glyph.nil T) 1 := eval_fdR main h
  have hs2 : Eval main (Cmd.peek 0 1) (fdR s Glyph.nil T) (fdS s Glyph.nil T) 1 :=
    eval_fdS main h
  have hset : Eval main (Cmd.set 2 Glyph.pos) (fdS s Glyph.nil T) (flagRowNilOut s T) 1 := by
    have hst : State.tSet (fdS s Glyph.nil T) 2 Glyph.pos = flagRowNilOut s T := by
      simp [flagRowNilOut, State.tSet]
    rw [← hst]; exact Eval.set 2 Glyph.pos (fdS s Glyph.nil T)
  have hite : Eval main (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg))
      (fdS s Glyph.nil T) (flagRowNilOut s T) 2 :=
    Eval.iteT (by simp [fdS, fdR, fdQ, fdP]) hset
  have h3 : Eval main (Cmd.seq (Cmd.peek 0 1)
      (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))
      (fdR s Glyph.nil T) (flagRowNilOut s T) 3 := Eval.seq hs2 hite
  have h2 : Eval main (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
      (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg))))
      (fdQ s) (flagRowNilOut s T) 4 := Eval.seq hr h3
  have h1 : Eval main (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
      (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
      (fdP s) (flagRowNilOut s T) 5 := Eval.seq hq h2
  have hmid : Eval main (Cmd.ite 1 Glyph.cons
      (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
        (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
      (Cmd.set 2 Glyph.pos)) (fdP s) (flagRowNilOut s T) 6 := Eval.iteT (by simp [fdP]) h1
  have hout : Eval main (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos)
      (Cmd.ite 1 Glyph.cons
        (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
          (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
        (Cmd.set 2 Glyph.pos)))
      (fdP s) (flagRowNilOut s T) 7 := Eval.iteF (by simp [fdP]) hmid
  exact Eval.seq hp hout

theorem eval_flagDecide_rowCons (main : Cmd) (T : List Glyph) (s : State) (g : Glyph)
    (hg : g ≠ Glyph.nil) (h : s.stk 0 = Glyph.cons :: g :: T) :
    Eval main flagDecide s (flagRowConsOut s g T) 8 := by
  have hp : Eval main (Cmd.peek 0 1) s (fdP s) 1 := eval_fdP main h
  have hq : Eval main (Cmd.push 1 1) (fdP s) (fdQ s) 1 := eval_fdQ main s
  have hr : Eval main (Cmd.pop 0 1) (fdQ s) (fdR s g T) 1 := eval_fdR main h
  have hs2 : Eval main (Cmd.peek 0 1) (fdR s g T) (fdS s g T) 1 := eval_fdS main h
  have hset : Eval main (Cmd.set 2 Glyph.neg) (fdS s g T) (flagRowConsOut s g T) 1 := by
    have hst : State.tSet (fdS s g T) 2 Glyph.neg = flagRowConsOut s g T := by
      simp [flagRowConsOut, State.tSet]
    rw [← hst]; exact Eval.set 2 Glyph.neg (fdS s g T)
  have hite : Eval main (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg))
      (fdS s g T) (flagRowConsOut s g T) 2 :=
    Eval.iteF (by simpa [fdS, fdR, fdQ, fdP] using hg) hset
  have h3 : Eval main (Cmd.seq (Cmd.peek 0 1)
      (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))
      (fdR s g T) (flagRowConsOut s g T) 3 := Eval.seq hs2 hite
  have h2 : Eval main (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
      (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg))))
      (fdQ s) (flagRowConsOut s g T) 4 := Eval.seq hr h3
  have h1 : Eval main (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
      (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
      (fdP s) (flagRowConsOut s g T) 5 := Eval.seq hq h2
  have hmid : Eval main (Cmd.ite 1 Glyph.cons
      (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
        (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
      (Cmd.set 2 Glyph.pos)) (fdP s) (flagRowConsOut s g T) 6 := Eval.iteT (by simp [fdP]) h1
  have hout : Eval main (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos)
      (Cmd.ite 1 Glyph.cons
        (Cmd.seq (Cmd.push 1 1) (Cmd.seq (Cmd.pop 0 1) (Cmd.seq (Cmd.peek 0 1)
          (Cmd.ite 1 Glyph.nil (Cmd.set 2 Glyph.pos) (Cmd.set 2 Glyph.neg)))))
        (Cmd.set 2 Glyph.pos)))
      (fdP s) (flagRowConsOut s g T) 7 := Eval.iteF (by simp [fdP]) hmid
  exact Eval.seq hp hout

/-! ## Components of the three outcomes -/

@[simp] theorem flagNilOut_stk (s : State) (k : Stk) : (flagNilOut s).stk k = s.stk k := by
  simp [flagNilOut]

@[simp] theorem flagNilOut_reg2 (s : State) : (flagNilOut s).reg 2 = Glyph.pos := by
  simp [flagNilOut]

@[simp] theorem flagRowNilOut_stk0 (s : State) (T : List Glyph) :
    (flagRowNilOut s T).stk 0 = Glyph.nil :: T := by
  simp [flagRowNilOut, fdS, fdR, fdQ, fdP]

@[simp] theorem flagRowNilOut_stk1 (s : State) (T : List Glyph) :
    (flagRowNilOut s T).stk 1 = Glyph.cons :: s.stk 1 := by
  simp [flagRowNilOut, fdS, fdR, fdQ, fdP]

@[simp] theorem flagRowNilOut_stk_ne (s : State) (T : List Glyph) {k : Stk}
    (h0 : k ≠ 0) (h1 : k ≠ 1) : (flagRowNilOut s T).stk k = s.stk k := by
  simp [flagRowNilOut, fdS, fdR, fdQ, fdP, h0, h1]

@[simp] theorem flagRowNilOut_reg2 (s : State) (T : List Glyph) :
    (flagRowNilOut s T).reg 2 = Glyph.pos := by
  simp [flagRowNilOut, fdS, fdR, fdQ, fdP]

@[simp] theorem flagRowConsOut_stk0 (s : State) (g : Glyph) (T : List Glyph) :
    (flagRowConsOut s g T).stk 0 = g :: T := by
  simp [flagRowConsOut, fdS, fdR, fdQ, fdP]

@[simp] theorem flagRowConsOut_stk1 (s : State) (g : Glyph) (T : List Glyph) :
    (flagRowConsOut s g T).stk 1 = Glyph.cons :: s.stk 1 := by
  simp [flagRowConsOut, fdS, fdR, fdQ, fdP]

@[simp] theorem flagRowConsOut_stk_ne (s : State) (g : Glyph) (T : List Glyph) {k : Stk}
    (h0 : k ≠ 0) (h1 : k ≠ 1) : (flagRowConsOut s g T).stk k = s.stk k := by
  simp [flagRowConsOut, fdS, fdR, fdQ, fdP, h0, h1]

@[simp] theorem flagRowConsOut_reg2 (s : State) (g : Glyph) (T : List Glyph) :
    (flagRowConsOut s g T).reg 2 = Glyph.neg := by
  simp [flagRowConsOut, fdS, fdR, fdQ, fdP]

/-! ## The marker is not part of any encoding -/

theorem mk3_notMem_intBody (z : ℤ) : (Glyph.mk 3 : Glyph) ∉ intBody z := by
  rw [intBody, List.mem_cons, List.mem_map]
  rintro (h | ⟨b, _, hb⟩)
  · split at h <;> exact absurd h (by decide)
  · cases hb

theorem mk3_notMem_intEnc_reverse (z : ℤ) : (Glyph.mk 3 : Glyph) ∉ (Val.int z).enc.reverse := by
  rw [List.mem_reverse, intEnc_eq, List.mem_append]
  rintro (h | h)
  · exact mk3_notMem_intBody z h
  · simp at h

/-! ## `InDiscArr` facts -/

/-- If the first row of a disc array is empty then every row is empty (all rows have length `r`). -/
theorem all_nil_of_head_nil {p M r : ℕ} {w : List (ℤ × ℤ)} {ws : List (List (ℤ × ℤ))}
    (h : InDiscArr p M r (w :: ws)) (hw : w = []) : ∀ u ∈ w :: ws, u = [] := by
  have hr0 : r = 0 := by
    have h1 : w.length = r := (h.2 w (List.mem_cons_self ..)).1
    rw [hw] at h1
    simpa using h1.symm
  intro u hu
  have hu' : u.length = r := (h.2 u hu).1
  exact List.eq_nil_of_length_eq_zero (by rw [hu', hr0])

/-! ## The phase states of `flagProg` -/

/-- State after pushing the frame marker `mk 3` on stack 1. -/
def stA (s : State) : State := (s.updReg 3 (Glyph.mk 3)).updStk 1 (Glyph.mk 3 :: s.stk 1)

/-- State after one read loop (reading `l₁ ++ [iend]` from stack 0 onto stack 1). -/
def stB (s : State) (l₁ l₂ : List Glyph) : State := (readFin 0 1 1 l₁ l₂ s).updReg 0 (Glyph.mk 2)

/-- State after the restore loop. -/
def stE (s : State) (B l₀ : List Glyph) : State :=
  (restFin 1 0 1 (Glyph.mk 3) B l₀ s).updReg 0 (Glyph.mk 2)

/-- State after pushing the flag value `k`. -/
def stF (k : ℕ) (s : State) : State :=
  Work.Kernel.pushGlyphsState ((Val.int (k : ℤ)).enc.reverse) 0 4 s

theorem eval_marker (main : Cmd) (s : State) :
    Eval main (Cmd.seq (Cmd.set 3 (Glyph.mk 3)) (Cmd.push 1 3)) s (stA s) 2 := by
  have h1 : Eval main (Cmd.set 3 (Glyph.mk 3)) s (s.updReg 3 (Glyph.mk 3)) 1 :=
    Eval.set 3 (Glyph.mk 3) s
  have h2 : Eval main (Cmd.push 1 3) (s.updReg 3 (Glyph.mk 3)) (stA s) 1 := by
    have hst : State.tPush (s.updReg 3 (Glyph.mk 3)) 1 3 = stA s := by simp [stA, State.tPush]
    rw [← hst]
    exact Eval.push 1 3 (s.updReg 3 (Glyph.mk 3))
  exact Eval.seq h1 h2

theorem stA_stk0 (s : State) : (stA s).stk 0 = s.stk 0 := by simp [stA]
theorem stA_stk1 (s : State) : (stA s).stk 1 = Glyph.mk 3 :: s.stk 1 := by simp [stA]
theorem stA_stk_ne (s : State) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (stA s).stk k = s.stk k := by simp [stA, hk0, hk1]

theorem stB_stk0 (s : State) (l₁ l₂ : List Glyph) : (stB s l₁ l₂).stk 0 = l₂ := by
  simp only [stB, State.updReg_stk]
  exact readFin_stk_rs (rs := 0) (rd := 1) (hrd := by decide) (rv := 1) l₁ l₂ s

theorem stB_stk1 (s : State) (l₁ l₂ : List Glyph) :
    (stB s l₁ l₂).stk 1 = (l₁ ++ [Glyph.iend]).reverse ++ s.stk 1 := by
  simp only [stB, State.updReg_stk]
  exact readFin_stk_rd (rs := 0) (rd := 1) (hrd := by decide) (rv := 1) l₁ l₂ s

theorem stB_stk_ne (s : State) (l₁ l₂ : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (stB s l₁ l₂).stk k = s.stk k := by
  simp only [stB, State.updReg_stk]
  exact readFin_stk_ne (rs := 0) (rd := 1) (rv := 1) l₁ l₂ s hk0 hk1

theorem stB_reg2 (s : State) (l₁ l₂ : List Glyph) : (stB s l₁ l₂).reg 2 = s.reg 2 := by
  simp [stB, readFin]

theorem stE_stk0 (s : State) (B l₀ : List Glyph) : (stE s B l₀).stk 0 = B.reverse ++ s.stk 0 := by
  simp only [stE, State.updReg_stk]
  exact restFin_stk_rd (rs := 1) (rd := 0) (hrd := by decide) (rv := 1) (m := Glyph.mk 3) B l₀ s

theorem stE_stk1 (s : State) (B l₀ : List Glyph) : (stE s B l₀).stk 1 = l₀ := by
  simp only [stE, State.updReg_stk]
  exact restFin_stk_rs (rs := 1) (rd := 0) (hrd := by decide) (rv := 1) (m := Glyph.mk 3) B l₀ s

theorem stE_stk_ne (s : State) (B l₀ : List Glyph) {k : Stk} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (stE s B l₀).stk k = s.stk k := by
  simp only [stE, State.updReg_stk]
  exact restFin_stk_ne (rs := 1) (rd := 0) (rv := 1) (m := Glyph.mk 3) B l₀ s hk1 hk0

theorem stE_reg2 (s : State) (B l₀ : List Glyph) : (stE s B l₀).reg 2 = s.reg 2 := by
  simp [stE, restFin]

theorem stF_stk0 (k : ℕ) (s : State) :
    (stF k s).stk 0 = (Val.int (k : ℤ)).enc ++ s.stk 0 := by
  rw [stF, Work.Kernel.pushGlyphsState_stk]
  simp

theorem stF_stk_ne (k : ℕ) (s : State) {j : Stk} (hj : j ≠ 0) :
    (stF k s).stk j = s.stk j := by
  exact Work.Kernel.pushGlyphsState_stk_ne _ _ _ _ hj

/-! ## The restore and push phases -/

theorem eval_rest
    (hrest : ∀ (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m : Glyph), rd ≠ rs → rv ≠ rf →
      ∀ (B l₀ : List Glyph), m ∉ B → ∀ s : State, s.stk rs = B ++ m :: l₀ →
        Eval main (restLoop rs rd rf rv m) s
          ((restFin rs rd rv m B l₀ s).updReg rf (Glyph.mk 2)) (4 * (B.length + 1) + 2))
    (main : Cmd) (s : State) (B l₀ : List Glyph) (hm : Glyph.mk 3 ∉ B)
    (hstk : s.stk 1 = B ++ Glyph.mk 3 :: l₀) :
    Eval main (restLoop 1 0 0 1 (Glyph.mk 3)) s (stE s B l₀) (4 * (B.length + 1) + 2) := by
  rw [stE]
  exact hrest main 1 0 0 1 (Glyph.mk 3) (by decide) (by decide) B l₀ hm s hstk

theorem eval_pushFlag0 (main : Cmd) (s : State) (h : s.reg 2 = Glyph.pos) :
    Eval main (Cmd.ite 2 Glyph.pos (pushIntVal 0 4) (pushIntVal 1 4)) s (stF 0 s)
      (1 + Work.Kernel.pushGlyphsCost ((Val.int (0 : ℤ)).enc.reverse)) := by
  have hset : Eval main (pushIntVal 0 4) s (stF 0 s)
      (Work.Kernel.pushGlyphsCost ((Val.int (0 : ℤ)).enc.reverse)) := by
    rw [stF]
    exact Work.Kernel.eval_pushGlyphs main _ 0 4 s
  exact Eval.iteT (by simpa using h) hset

theorem eval_pushFlag1 (main : Cmd) (s : State) (h : s.reg 2 = Glyph.neg) :
    Eval main (Cmd.ite 2 Glyph.pos (pushIntVal 0 4) (pushIntVal 1 4)) s (stF 1 s)
      (1 + Work.Kernel.pushGlyphsCost ((Val.int (1 : ℤ)).enc.reverse)) := by
  have hset : Eval main (pushIntVal 1 4) s (stF 1 s)
      (Work.Kernel.pushGlyphsCost ((Val.int (1 : ℤ)).enc.reverse)) := by
    rw [stF]
    exact Work.Kernel.eval_pushGlyphs main _ 0 4 s
  exact Eval.iteF (by rw [h]; decide) hset

/-! ## Cost facts -/

theorem pushGlyphsCost_intEnc (k : ℕ) :
    Work.Kernel.pushGlyphsCost ((Val.int (k : ℤ)).enc.reverse) = 2 * isz (k : ℤ) + 1 := by
  rw [Work.Kernel.pushGlyphsCost_eq, List.length_reverse, intEnc_length]

theorem isz_lower (z : ℤ) : 2 ≤ isz z := by simp [isz]

theorem isz_natCast_zero_le : isz (((0 : ℕ) : ℤ)) ≤ 4 := by
  have h : (((0 : ℕ) : ℤ)).natAbs ≤ 2 ^ 1 := by norm_num
  have := Work.ConvR.isz_le_of_natAbs_le h
  omega

theorem isz_natCast_one_le : isz (((1 : ℕ) : ℤ)) ≤ 4 := by
  have h : (((1 : ℕ) : ℤ)).natAbs ≤ 2 ^ 1 := by norm_num
  have := Work.ConvR.isz_le_of_natAbs_le h
  omega

/-- Reversing a reversed concatenation. -/
theorem reverse_append_reverse {α : Type*} (A B : List α) :
    (B.reverse ++ A.reverse).reverse = A ++ B := by
  simp [List.reverse_append]

end Work.ConvR
