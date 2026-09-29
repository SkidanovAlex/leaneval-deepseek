import Mathlib
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Loop
import Submission.Work.IntLib.encodeNatBridge

/-!
# `IntLib` / shift words: the `parse` prologue

`parse` splits the top two values of the value stack.  This file proves the `Eval` specification
of `parse`, decomposed as

* a *prefix* (seven frame-marker pushes, one pop, one push) which we describe by explicit state
  functions (`mkA1 … mkA7`, `preD`), and
* a *suffix* (`parse_suffix`, the three drains and the three pops) which is stated for an
  arbitrary predecessor state `u`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib.Shift

open HvdH

/-! ## Glyph distinctness -/

theorem bit_ne_iend (b : Bool) : (Glyph.bit b : Glyph) ≠ Glyph.iend := fun h => by cases h

theorem bit_ne_mk' (b : Bool) (k : Stk) : (Glyph.bit b : Glyph) ≠ gmk k := fun h => by cases h

/-! ## State-step helpers -/

/-- State reached by `pop k r`. -/
def stPop (u : State) (k : Stk) (r : Reg) : State :=
  ⟨Function.update u.reg r ((u.stk k).headD .eos), Function.update u.stk k (u.stk k).tail⟩

/-- State reached by `push k r`. -/
def stPush (u : State) (k : Stk) (r : Reg) : State :=
  ⟨u.reg, Function.update u.stk k (u.reg r :: u.stk k)⟩

/-- State reached by `pushC k g r`. -/
def stPushC (u : State) (k : Stk) (g : Glyph) (r : Reg) : State :=
  ⟨Function.update u.reg r g, Function.update u.stk k (g :: u.stk k)⟩

@[simp] theorem stPop_stk_self (u : State) (k : Stk) (r : Reg) :
    (stPop u k r).stk k = (u.stk k).tail :=
  Function.update_self k _ u.stk

theorem stPop_stk_of_ne (u : State) (k : Stk) (r : Reg) {j : Stk} (h : j ≠ k) :
    (stPop u k r).stk j = u.stk j :=
  Function.update_of_ne h _ u.stk

@[simp] theorem stPop_reg_self (u : State) (k : Stk) (r : Reg) :
    (stPop u k r).reg r = (u.stk k).headD .eos :=
  Function.update_self r _ u.reg

theorem stPop_reg_of_ne (u : State) (k : Stk) (r : Reg) {r' : Reg} (h : r' ≠ r) :
    (stPop u k r).reg r' = u.reg r' :=
  Function.update_of_ne h _ u.reg

@[simp] theorem stPush_stk_self (u : State) (k : Stk) (r : Reg) :
    (stPush u k r).stk k = u.reg r :: u.stk k :=
  Function.update_self k _ u.stk

theorem stPush_stk_of_ne (u : State) (k : Stk) (r : Reg) {j : Stk} (h : j ≠ k) :
    (stPush u k r).stk j = u.stk j :=
  Function.update_of_ne h _ u.stk

theorem stPush_reg (u : State) (k : Stk) (r : Reg) (r' : Reg) :
    (stPush u k r).reg r' = u.reg r' := rfl

@[simp] theorem stPushC_stk_self (u : State) (k : Stk) (g : Glyph) (r : Reg) :
    (stPushC u k g r).stk k = g :: u.stk k :=
  Function.update_self k _ u.stk

theorem stPushC_stk_of_ne (u : State) (k : Stk) (g : Glyph) (r : Reg) {j : Stk} (h : j ≠ k) :
    (stPushC u k g r).stk j = u.stk j :=
  Function.update_of_ne h _ u.stk

@[simp] theorem stPushC_reg_self (u : State) (k : Stk) (g : Glyph) (r : Reg) :
    (stPushC u k g r).reg r = g :=
  Function.update_self r _ u.reg

theorem stPushC_reg_of_ne (u : State) (k : Stk) (g : Glyph) (r : Reg) {r' : Reg}
    (h : r' ≠ r) : (stPushC u k g r).reg r' = u.reg r' :=
  Function.update_of_ne h _ u.reg

/-! ## `Eval` steps -/

theorem ev_stPushC (main : Cmd) (u : State) (k : Stk) (g : Glyph) (r : Reg) :
    Ev main (pushC k g r) u (stPushC u k g r) 2 :=
  ev_pushC_st main k g r u

theorem ev_stPop (main : Cmd) (u : State) (k : Stk) (r : Reg) :
    Ev main (.pop k r) u (stPop u k r) 1 :=
  ev_pop_st main k r u

theorem ev_stPush (main : Cmd) (u : State) (k : Stk) (r : Reg) :
    Ev main (.push k r) u (stPush u k r) 1 :=
  ev_push_st main k r u

/-- `Eval` for a `push` from a state whose register `r` holds `gd`. -/
theorem Eval_pushD (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    (gd : Glyph) (hg : g r = gd) :
    Eval main (.push k r) ⟨g, X⟩ ⟨g, Function.update X k (gd :: X k)⟩ 1 := by
  have h : Eval main (.push k r) ⟨g, X⟩ ⟨g, Function.update X k (g r :: X k)⟩ 1 :=
    Eval.push (main := main) k r (⟨g, X⟩ : State)
  rw [hg] at h
  exact h

/-- `Eval` for `pushMark k r`. -/
theorem eval_pushMark (main : Cmd) (u : State) (k : Stk) (r : Reg) :
    Eval main (pushMark k r) u (stPushC u k (gmk k) r) 2 := by
  have h1 : Eval main (.set r (gmk k)) u ⟨Function.update u.reg r (gmk k), u.stk⟩ 1 :=
    Eval.set (main := main) r (gmk k) u
  have h2 : Eval main (.push k r) ⟨Function.update u.reg r (gmk k), u.stk⟩
      (stPushC u k (gmk k) r) 1 :=
    Eval_pushD main k r (Function.update u.reg r (gmk k)) u.stk (gmk k)
      (Function.update_self r (gmk k) u.reg)
  exact Eval.seq h1 h2

theorem eval_popMark (main : Cmd) (u : State) (r : Reg) :
    Eval main (.pop 0 r) u (stPop u 0 r) 1 :=
  Eval.pop 0 r u

theorem eval_pushReg (main : Cmd) (u : State) (k : Stk) (r : Reg) :
    Eval main (.push k r) u (stPush u k r) 1 :=
  Eval.push k r u

/-! ## The seven frame-marker pushes -/

def mkA1 (s : State) : State := stPushC s sSg (gmk sSg) rY
def mkA2 (s : State) : State := stPushC (mkA1 s) sM (gmk sM) rY
def mkA3 (s : State) : State := stPushC (mkA2 s) sK (gmk sK) rY
def mkA4 (s : State) : State := stPushC (mkA3 s) sP (gmk sP) rY
def mkA5 (s : State) : State := stPushC (mkA4 s) sA (gmk sA) rY
def mkA6 (s : State) : State := stPushC (mkA5 s) sT (gmk sT) rY
def mkA7 (s : State) : State := stPushC (mkA6 s) sT2 (gmk sT2) rY

theorem mkA1_stk_of_ne (s : State) {j : Stk} (h : j ≠ sSg) : (mkA1 s).stk j = s.stk j :=
  stPushC_stk_of_ne s sSg (gmk sSg) rY h

theorem mkA1_stk_self (s : State) : (mkA1 s).stk sSg = gmk sSg :: s.stk sSg :=
  stPushC_stk_self s sSg (gmk sSg) rY

theorem mkA2_stk_of_ne (s : State) {j : Stk} (h : j ≠ sM) :
    (mkA2 s).stk j = (mkA1 s).stk j :=
  stPushC_stk_of_ne (mkA1 s) sM (gmk sM) rY h

theorem mkA2_stk_self (s : State) : (mkA2 s).stk sM = gmk sM :: (mkA1 s).stk sM :=
  stPushC_stk_self (mkA1 s) sM (gmk sM) rY

theorem mkA3_stk_of_ne (s : State) {j : Stk} (h : j ≠ sK) :
    (mkA3 s).stk j = (mkA2 s).stk j :=
  stPushC_stk_of_ne (mkA2 s) sK (gmk sK) rY h

theorem mkA3_stk_self (s : State) : (mkA3 s).stk sK = gmk sK :: (mkA2 s).stk sK :=
  stPushC_stk_self (mkA2 s) sK (gmk sK) rY

theorem mkA4_stk_of_ne (s : State) {j : Stk} (h : j ≠ sP) :
    (mkA4 s).stk j = (mkA3 s).stk j :=
  stPushC_stk_of_ne (mkA3 s) sP (gmk sP) rY h

theorem mkA4_stk_self (s : State) : (mkA4 s).stk sP = gmk sP :: (mkA3 s).stk sP :=
  stPushC_stk_self (mkA3 s) sP (gmk sP) rY

theorem mkA5_stk_of_ne (s : State) {j : Stk} (h : j ≠ sA) :
    (mkA5 s).stk j = (mkA4 s).stk j :=
  stPushC_stk_of_ne (mkA4 s) sA (gmk sA) rY h

theorem mkA5_stk_self (s : State) : (mkA5 s).stk sA = gmk sA :: (mkA4 s).stk sA :=
  stPushC_stk_self (mkA4 s) sA (gmk sA) rY

theorem mkA6_stk_of_ne (s : State) {j : Stk} (h : j ≠ sT) :
    (mkA6 s).stk j = (mkA5 s).stk j :=
  stPushC_stk_of_ne (mkA5 s) sT (gmk sT) rY h

theorem mkA6_stk_self (s : State) : (mkA6 s).stk sT = gmk sT :: (mkA5 s).stk sT :=
  stPushC_stk_self (mkA5 s) sT (gmk sT) rY

theorem mkA7_stk_of_ne (s : State) {j : Stk} (h : j ≠ sT2) :
    (mkA7 s).stk j = (mkA6 s).stk j :=
  stPushC_stk_of_ne (mkA6 s) sT2 (gmk sT2) rY h

theorem mkA7_stk_self (s : State) : (mkA7 s).stk sT2 = gmk sT2 :: (mkA6 s).stk sT2 :=
  stPushC_stk_self (mkA6 s) sT2 (gmk sT2) rY

/-- All stacks outside the seven frame stacks are untouched by the marker phase. -/
theorem mkA7_stk_of_not (s : State) {j : Stk} (h1 : j ≠ sSg) (h2 : j ≠ sM) (h3 : j ≠ sK)
    (h4 : j ≠ sP) (h5 : j ≠ sA) (h6 : j ≠ sT) (h7 : j ≠ sT2) :
    (mkA7 s).stk j = s.stk j := by
  rw [mkA7_stk_of_ne s h7, mkA6_stk_of_ne s h6, mkA5_stk_of_ne s h5, mkA4_stk_of_ne s h4,
    mkA3_stk_of_ne s h3, mkA2_stk_of_ne s h2, mkA1_stk_of_ne s h1]

theorem mkA7_stk_sSg (s : State) : (mkA7 s).stk sSg = gmk sSg :: s.stk sSg := by
  rw [mkA7_stk_of_ne s (by decide), mkA6_stk_of_ne s (by decide), mkA5_stk_of_ne s (by decide),
    mkA4_stk_of_ne s (by decide), mkA3_stk_of_ne s (by decide), mkA2_stk_of_ne s (by decide),
    mkA1_stk_self]

theorem mkA7_stk_sM (s : State) : (mkA7 s).stk sM = gmk sM :: s.stk sM := by
  rw [mkA7_stk_of_ne s (by decide), mkA6_stk_of_ne s (by decide), mkA5_stk_of_ne s (by decide),
    mkA4_stk_of_ne s (by decide), mkA3_stk_of_ne s (by decide), mkA2_stk_self,
    mkA1_stk_of_ne s (by decide)]

theorem mkA7_stk_sK (s : State) : (mkA7 s).stk sK = gmk sK :: s.stk sK := by
  rw [mkA7_stk_of_ne s (by decide), mkA6_stk_of_ne s (by decide), mkA5_stk_of_ne s (by decide),
    mkA4_stk_of_ne s (by decide), mkA3_stk_self, mkA2_stk_of_ne s (by decide),
    mkA1_stk_of_ne s (by decide)]

theorem mkA7_stk_sP (s : State) : (mkA7 s).stk sP = gmk sP :: s.stk sP := by
  rw [mkA7_stk_of_ne s (by decide), mkA6_stk_of_ne s (by decide), mkA5_stk_of_ne s (by decide),
    mkA4_stk_self, mkA3_stk_of_ne s (by decide), mkA2_stk_of_ne s (by decide),
    mkA1_stk_of_ne s (by decide)]

theorem mkA7_stk_sA (s : State) : (mkA7 s).stk sA = gmk sA :: s.stk sA := by
  rw [mkA7_stk_of_ne s (by decide), mkA6_stk_of_ne s (by decide), mkA5_stk_self,
    mkA4_stk_of_ne s (by decide), mkA3_stk_of_ne s (by decide), mkA2_stk_of_ne s (by decide),
    mkA1_stk_of_ne s (by decide)]

theorem mkA7_stk_sT (s : State) : (mkA7 s).stk sT = gmk sT :: s.stk sT := by
  rw [mkA7_stk_of_ne s (by decide), mkA6_stk_self, mkA5_stk_of_ne s (by decide),
    mkA4_stk_of_ne s (by decide), mkA3_stk_of_ne s (by decide), mkA2_stk_of_ne s (by decide),
    mkA1_stk_of_ne s (by decide)]

theorem mkA7_stk_sT2 (s : State) : (mkA7 s).stk sT2 = gmk sT2 :: s.stk sT2 := by
  rw [mkA7_stk_self, mkA6_stk_of_ne s (by decide), mkA5_stk_of_ne s (by decide),
    mkA4_stk_of_ne s (by decide), mkA3_stk_of_ne s (by decide), mkA2_stk_of_ne s (by decide),
    mkA1_stk_of_ne s (by decide)]

/-- State after the prefix of `parse` (seven markers, one pop, one push). -/
def preD (s : State) : State := stPush (stPop (mkA7 s) 0 rX) sSg rX

theorem preD_def (s : State) : preD s = stPush (stPop (mkA7 s) 0 rX) sSg rX := rfl


/-! ## Reversal of a mapped bit list, and `NoMark` facts -/

theorem bits_map_reverse (l : List Bool) :
    ((l.map Glyph.bit).reverse) = (l.reverse).map Glyph.bit := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.reverse_cons, ih, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil]

/-- The bits of a natural number encode to glyphs none of which is `iend`. -/
theorem bits_no_iend (l : List Bool) : ∀ h ∈ l.map Glyph.bit, h ≠ Glyph.iend := by
  intro h hh
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hh
  rw [← hb]
  exact bit_ne_iend b

/-- `a` is `j`-free as soon as `a.val ≤ 7 < j.val`. -/
theorem stk_ne_of_val_le {j a : Stk} (ha : a.val ≤ 7) (hj : 7 < j.val) : j ≠ a := fun hh => by
  rw [hh] at hj; omega

/-! ## The suffix of `parse`: three drains and three pops -/

theorem parse_suffix (main : Cmd) (s u : State) (σk : Glyph) (Ba Bk A' : List Glyph)
    (h0 : u.stk 0 = Ba ++ Glyph.iend :: σk :: (Bk ++ Glyph.iend :: A'))
    (hBai : ∀ h ∈ Ba, h ≠ Glyph.iend)
    (hBki : ∀ h ∈ Bk, h ≠ Glyph.iend)
    (hBam : NoMark Ba)
    (hT : u.stk sT = gmk sT :: s.stk sT)
    (hM : u.stk sM = gmk sM :: s.stk sM)
    (hK : u.stk sK = gmk sK :: s.stk sK) :
    ∃ (s' : State) (n : ℕ),
      Eval main
        (seqs [drain 0 sT Glyph.iend rZ rJ, .pop 0 rX,
               drain sT sM (gmk sT) rZ rJ, .pop 0 rX,
               drain 0 sK Glyph.iend rZ rJ, .pop 0 rX]) u s' n ∧
      n ≤ 5 * (Ba.length + 1) + 2 + 1 + (5 * (Ba.length + 1) + 2) + 1
            + (5 * (Bk.length + 1) + 2) + 1 ∧
      s'.stk 0 = A' ∧
      s'.stk sM = Ba ++ gmk sM :: s.stk sM ∧
      s'.stk sK = Bk.reverse ++ gmk sK :: s.stk sK ∧
      s'.stk sT = gmk sT :: s.stk sT ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sM → j ≠ sK → s'.stk j = u.stk j) := by
  have hBam' : ∀ h ∈ Ba.reverse, h ≠ gmk sT := fun h hh => hBam h (List.mem_reverse.mp hh) sT
  obtain ⟨s1, n1, he1, hb1, _, h01, hT1, hfr1⟩ :=
    drain_ev main 0 sT Glyph.iend rZ rJ (by decide) (by decide)
      Ba (σk :: Bk ++ Glyph.iend :: A') (gmk sT :: s.stk sT) u.reg u.stk hBai h0 hT
  have he1' : Eval main (drain 0 sT Glyph.iend rZ rJ) u s1 n1 := he1
  have he2 : Eval main (.pop 0 rX) s1 (stPop s1 0 rX) 1 := Eval.pop (main := main) 0 rX s1
  have hs1T : (stPop s1 0 rX).stk sT = Ba.reverse ++ gmk sT :: s.stk sT := by
    rw [stPop_stk_of_ne s1 0 rX (show sT ≠ (0 : Stk) by decide)]; exact hT1
  have hs1M : (stPop s1 0 rX).stk sM = gmk sM :: s.stk sM := by
    rw [stPop_stk_of_ne s1 0 rX (show sM ≠ (0 : Stk) by decide),
      hfr1 sM (show sM ≠ (0 : Stk) by decide) (show sM ≠ sT by decide)]
    exact hM
  obtain ⟨s2, n2, he3, hb3, _, hT3, hM3, hfr3⟩ :=
    drain_ev main sT sM (gmk sT) rZ rJ (by decide) (by decide)
      Ba.reverse (s.stk sT) (gmk sM :: s.stk sM) (stPop s1 0 rX).reg (stPop s1 0 rX).stk
      hBam' hs1T hs1M
  have he4 : Eval main (.pop 0 rX) s2 (stPop s2 0 rX) 1 := Eval.pop (main := main) 0 rX s2
  have hs2_0 : s2.stk 0 = σk :: Bk ++ Glyph.iend :: A' := by
    rw [hfr3 0 (show (0 : Stk) ≠ sT by decide) (show (0 : Stk) ≠ sM by decide),
      stPop_stk_self, h01]
    rfl
  have hs2K : s2.stk sK = gmk sK :: s.stk sK := by
    rw [hfr3 sK (show sK ≠ sT by decide) (show sK ≠ sM by decide),
      stPop_stk_of_ne s1 0 rX (show sK ≠ (0 : Stk) by decide),
      hfr1 sK (show sK ≠ (0 : Stk) by decide) (show sK ≠ sT by decide)]
    exact hK
  have hs3_0 : (stPop s2 0 rX).stk 0 = Bk ++ Glyph.iend :: A' := by
    rw [stPop_stk_self, hs2_0]; rfl
  have hs3K : (stPop s2 0 rX).stk sK = gmk sK :: s.stk sK := by
    rw [stPop_stk_of_ne s2 0 rX (show sK ≠ (0 : Stk) by decide)]; exact hs2K
  obtain ⟨s3, n3, he5, hb5, _, h03, hK3, hfr5⟩ :=
    drain_ev main 0 sK Glyph.iend rZ rJ (by decide) (by decide)
      Bk A' (gmk sK :: s.stk sK) (stPop s2 0 rX).reg (stPop s2 0 rX).stk
      hBki hs3_0 hs3K
  refine ⟨stPop s3 0 rX, n1 + (1 + (n2 + (1 + (n3 + 1)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq he1' (Eval.seq he2 (Eval.seq he3 (Eval.seq he4
      (Eval.seq he5 (Eval.pop (main := main) 0 rX s3)))))
  · rw [List.length_reverse] at hb3
    omega
  · rw [stPop_stk_self, h03]; rfl
  · rw [stPop_stk_of_ne s3 0 rX (show sM ≠ (0 : Stk) by decide),
      hfr5 sM (show sM ≠ (0 : Stk) by decide) (show sM ≠ sK by decide),
      stPop_stk_of_ne s2 0 rX (show sM ≠ (0 : Stk) by decide), hM3, List.reverse_reverse]
  · rw [stPop_stk_of_ne s3 0 rX (show sK ≠ (0 : Stk) by decide)]; exact hK3
  · rw [stPop_stk_of_ne s3 0 rX (show sT ≠ (0 : Stk) by decide),
      hfr5 sT (show sT ≠ (0 : Stk) by decide) (show sT ≠ sK by decide),
      stPop_stk_of_ne s2 0 rX (show sT ≠ (0 : Stk) by decide)]; exact hT3
  · intro j hj0 hjT hjM hjK
    rw [stPop_stk_of_ne s3 0 rX hj0, hfr5 j hj0 hjK, stPop_stk_of_ne s2 0 rX hj0,
      hfr3 j hjT hjM, stPop_stk_of_ne s1 0 rX hj0, hfr1 j hj0 hjT]

/-! ## The full `parse` -/

theorem parse_core (main : Cmd) (s : State) (σa σk : Glyph) (Ba Bk A' : List Glyph)
    (h0 : s.stk 0 = σa :: (Ba ++ Glyph.iend :: σk :: (Bk ++ Glyph.iend :: A')))
    (hBai : ∀ h ∈ Ba, h ≠ Glyph.iend)
    (hBki : ∀ h ∈ Bk, h ≠ Glyph.iend)
    (hBam : NoMark Ba) :
    ∃ (s' : State) (n : ℕ), Eval main parse s s' n ∧
      n ≤ 10 * Ba.length + 5 * Bk.length + 40 ∧
      s'.stk 0 = A' ∧
      s'.stk sSg = σa :: gmk sSg :: s.stk sSg ∧
      s'.stk sM = Ba ++ gmk sM :: s.stk sM ∧
      s'.stk sK = Bk.reverse ++ gmk sK :: s.stk sK ∧
      s'.stk sP = gmk sP :: s.stk sP ∧
      s'.stk sA = gmk sA :: s.stk sA ∧
      s'.stk sT = gmk sT :: s.stk sT ∧
      s'.stk sT2 = gmk sT2 :: s.stk sT2 ∧
      (∀ j : Stk, 7 < j.val → s'.stk j = s.stk j) := by
  have e1 : Eval main (pushMark sSg rY) s (mkA1 s) 2 := eval_pushMark main s sSg rY
  have e2 : Eval main (pushMark sM rY) (mkA1 s) (mkA2 s) 2 := eval_pushMark main (mkA1 s) sM rY
  have e3 : Eval main (pushMark sK rY) (mkA2 s) (mkA3 s) 2 := eval_pushMark main (mkA2 s) sK rY
  have e4 : Eval main (pushMark sP rY) (mkA3 s) (mkA4 s) 2 := eval_pushMark main (mkA3 s) sP rY
  have e5 : Eval main (pushMark sA rY) (mkA4 s) (mkA5 s) 2 := eval_pushMark main (mkA4 s) sA rY
  have e6 : Eval main (pushMark sT rY) (mkA5 s) (mkA6 s) 2 := eval_pushMark main (mkA5 s) sT rY
  have e7 : Eval main (pushMark sT2 rY) (mkA6 s) (mkA7 s) 2 := eval_pushMark main (mkA6 s) sT2 rY
  have e8 : Eval main (.pop 0 rX) (mkA7 s) (stPop (mkA7 s) 0 rX) 1 :=
    Eval.pop (main := main) 0 rX (mkA7 s)
  have e9 : Eval main (.push sSg rX) (stPop (mkA7 s) 0 rX) (preD s) 1 :=
    Eval.push (main := main) sSg rX (stPop (mkA7 s) 0 rX)
  have hA70 : (mkA7 s).stk 0 = s.stk 0 :=
    mkA7_stk_of_not s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have hpre0 : (preD s).stk 0 = Ba ++ Glyph.iend :: σk :: (Bk ++ Glyph.iend :: A') := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show (0 : Stk) ≠ sSg by decide), stPop_stk_self, hA70, h0]
    rfl
  have hpreT : (preD s).stk sT = gmk sT :: s.stk sT := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show sT ≠ sSg by decide),
      stPop_stk_of_ne _ _ _ (show sT ≠ (0 : Stk) by decide), mkA7_stk_sT]
  have hpreM : (preD s).stk sM = gmk sM :: s.stk sM := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show sM ≠ sSg by decide),
      stPop_stk_of_ne _ _ _ (show sM ≠ (0 : Stk) by decide), mkA7_stk_sM]
  have hpreK : (preD s).stk sK = gmk sK :: s.stk sK := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show sK ≠ sSg by decide),
      stPop_stk_of_ne _ _ _ (show sK ≠ (0 : Stk) by decide), mkA7_stk_sK]
  have hpreP : (preD s).stk sP = gmk sP :: s.stk sP := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show sP ≠ sSg by decide),
      stPop_stk_of_ne _ _ _ (show sP ≠ (0 : Stk) by decide), mkA7_stk_sP]
  have hpreA : (preD s).stk sA = gmk sA :: s.stk sA := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show sA ≠ sSg by decide),
      stPop_stk_of_ne _ _ _ (show sA ≠ (0 : Stk) by decide), mkA7_stk_sA]
  have hpreT2 : (preD s).stk sT2 = gmk sT2 :: s.stk sT2 := by
    rw [preD_def, stPush_stk_of_ne _ _ _ (show sT2 ≠ sSg by decide),
      stPop_stk_of_ne _ _ _ (show sT2 ≠ (0 : Stk) by decide), mkA7_stk_sT2]
  have hpreSg : (preD s).stk sSg = σa :: gmk sSg :: s.stk sSg := by
    have hX : (stPop (mkA7 s) 0 rX).stk sSg = gmk sSg :: s.stk sSg := by
      rw [stPop_stk_of_ne _ _ _ (show sSg ≠ (0 : Stk) by decide), mkA7_stk_sSg]
    have hY : (stPop (mkA7 s) 0 rX).reg rX = σa := by
      rw [stPop_reg_self, hA70, h0]; rfl
    rw [preD_def, stPush_stk_self, hY, hX]
  obtain ⟨s', n2, he2, hb2, h00, hM, hK, hT, hfr⟩ :=
    parse_suffix main s (preD s) σk Ba Bk A' hpre0 hBai hBki hBam hpreT hpreM hpreK
  refine ⟨s', 2 + (2 + (2 + (2 + (2 + (2 + (2 + (1 + (1 + n2)))))))), ?_, ?_, ?_, ?_, ?_, ?_
    , ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
      (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 he2))))))))
  · omega
  · exact h00
  · rw [hfr sSg (show sSg ≠ (0 : Stk) by decide) (show sSg ≠ sT by decide)
      (show sSg ≠ sM by decide) (show sSg ≠ sK by decide)]
    exact hpreSg
  · exact hM
  · exact hK
  · rw [hfr sP (show sP ≠ (0 : Stk) by decide) (show sP ≠ sT by decide)
      (show sP ≠ sM by decide) (show sP ≠ sK by decide)]
    exact hpreP
  · rw [hfr sA (show sA ≠ (0 : Stk) by decide) (show sA ≠ sT by decide)
      (show sA ≠ sM by decide) (show sA ≠ sK by decide)]
    exact hpreA
  · exact hT
  · rw [hfr sT2 (show sT2 ≠ (0 : Stk) by decide) (show sT2 ≠ sT by decide)
      (show sT2 ≠ sM by decide) (show sT2 ≠ sK by decide)]
    exact hpreT2
  · intro j hj
    have hne : ∀ a : Stk, a.val ≤ 7 → j ≠ a := fun a ha => stk_ne_of_val_le ha hj
    rw [hfr j (hne 0 (by decide)) (hne sT (by decide)) (hne sM (by decide)) (hne sK (by decide)),
      preD_def, stPush_stk_of_ne _ _ _ (hne sSg (by decide)),
      stPop_stk_of_ne _ _ _ (hne 0 (by decide)),
      mkA7_stk_of_not s (hne sSg (by decide)) (hne sM (by decide)) (hne sK (by decide))
        (hne sP (by decide)) (hne sA (by decide)) (hne sT (by decide)) (hne sT2 (by decide))]

/-! ## The specification of `parse` -/

theorem parse_ev (main : HvdH.Cmd) (a k : ℤ) (rest : List HvdH.Val) (Rj : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = (HvdH.Val.int a).enc ++ (HvdH.Val.int k).enc ++ HvdH.encs rest ++ Rj) :
    ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main Work.IntLib.Shift.parse s s' n ∧
      n ≤ 60 * (((a.natAbs.bits).length + (k.natAbs.bits).length) + 2) ∧
      s'.stk 0 = HvdH.encs rest ++ Rj ∧
      s'.stk Work.IntLib.Shift.sSg = (if a < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos) :: Work.IntLib.Shift.gmk Work.IntLib.Shift.sSg :: s.stk Work.IntLib.Shift.sSg ∧
      s'.stk Work.IntLib.Shift.sM = (a.natAbs.bits).map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: s.stk Work.IntLib.Shift.sM ∧
      s'.stk Work.IntLib.Shift.sK = (k.natAbs.bits.reverse).map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sK :: s.stk Work.IntLib.Shift.sK ∧
      s'.stk Work.IntLib.Shift.sP = Work.IntLib.Shift.gmk Work.IntLib.Shift.sP :: s.stk Work.IntLib.Shift.sP ∧
      s'.stk Work.IntLib.Shift.sA = Work.IntLib.Shift.gmk Work.IntLib.Shift.sA :: s.stk Work.IntLib.Shift.sA ∧
      s'.stk Work.IntLib.Shift.sT = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT :: s.stk Work.IntLib.Shift.sT ∧
      s'.stk Work.IntLib.Shift.sT2 = Work.IntLib.Shift.gmk Work.IntLib.Shift.sT2 :: s.stk Work.IntLib.Shift.sT2 ∧
      (∀ j : HvdH.Stk, 7 < j.val → s'.stk j = s.stk j) := by
  have hdec : s.stk 0 = (if a < 0 then Glyph.neg else Glyph.pos) ::
      ((a.natAbs.bits).map Glyph.bit ++ Glyph.iend ::
       (if k < 0 then Glyph.neg else Glyph.pos) ::
       ((k.natAbs.bits).map Glyph.bit ++ Glyph.iend :: (encs rest ++ Rj))) := by
    rw [h0, Work.IntLib.enc_int, Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  obtain ⟨s', n, hev, hbnd, h00, hSg, hM, hK, hP, hA, hT, hT2, hfr⟩ :=
    parse_core main s (if a < 0 then Glyph.neg else Glyph.pos)
      (if k < 0 then Glyph.neg else Glyph.pos) ((a.natAbs.bits).map Glyph.bit)
      ((k.natAbs.bits).map Glyph.bit) (encs rest ++ Rj) hdec
      (bits_no_iend (a.natAbs.bits)) (bits_no_iend (k.natAbs.bits)) (noMark_bitsG (a.natAbs.bits))
  refine ⟨s', n, hev, ?_, h00, hSg, hM, ?_, hP, hA, hT, hT2, hfr⟩
  · have hb := hbnd
    simp only [List.length_map] at hb
    omega
  · rw [hK, bits_map_reverse]

end Work.IntLib.Shift
