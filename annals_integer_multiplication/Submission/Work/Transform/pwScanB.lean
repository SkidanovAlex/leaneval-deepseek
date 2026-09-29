import Mathlib
import Submission.Work.Transform.pwBase
import Submission.Work.Transform.pwScanDefs
import Submission.Work.Transform.Pw.pwScanFlagCmd

/-!
# `Work.Transform.pwScanB`: the buffered lockstep scan of two canonical bit strings

From two stacks carrying two canonical bit strings (least significant bit first, above the frame
marker `Pw.gM`) a fixed program (no `self`) walks the two strings in parallel, moving the common
prefix (in reverse order, above a fresh marker) to two buffer stacks and keeping in
`reg Pw.rFlag` the comparison of the bits read so far (the *last* difference, i.e. the most
significant one, wins).  It stops as soon as one side reaches its marker, which it does *not*
consume, so the two stacks keep exactly the unconsumed suffixes, and `reg Pw.rCont` leaves `eos`.

The main work is `scanAux`, the induction on the length of the common prefix; the per-step facts
about the loop body are the `*_ev` lemmas below.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel
open Work.IntLib

/-! ## Register and flag facts -/

theorem rCont_ne_rFlag : rCont ≠ rFlag := by decide
theorem rFlag_ne_rGA : rFlag ≠ rGA := rGA_ne_rFlag.symm
theorem rFlag_ne_rGB : rFlag ≠ rGB := rGB_ne_rFlag.symm
theorem rCont_ne_rGA : rCont ≠ rGA := rGA_ne_rCont.symm
theorem rCont_ne_rGB : rCont ≠ rGB := rGB_ne_rCont.symm
theorem rFlag_ne_rCont : rFlag ≠ rCont := rCont_ne_rFlag.symm

/-- The canonical flag glyph records the comparison it is built from. -/
theorem natFlag_flagOf (x y : ℕ) : NatFlag (flagOf x y) x y := by
  unfold flagOf
  by_cases h : x < y
  · rw [if_pos h]; exact Or.inl ⟨rfl, h⟩
  · rw [if_neg h]
    by_cases h2 : x = y
    · rw [if_pos h2]; exact Or.inr (Or.inl ⟨rfl, h2⟩)
    · rw [if_neg h2]; exact Or.inr (Or.inr ⟨rfl, by omega⟩)

/-- A glyph recording a comparison is the canonical one. -/
theorem eq_flagOf_of_natFlag {f : Glyph} {x y : ℕ} (h : NatFlag f x y) : f = flagOf x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; unfold flagOf; rw [if_pos h2]
  · subst h1; unfold flagOf; rw [if_neg (by omega), if_pos h2]
  · subst h1; unfold flagOf; rw [if_neg (by omega), if_neg (by omega)]

theorem flagOf_zero_zero : flagOf 0 0 = gEq := by simp [flagOf]

/-- One step of the flag arithmetic: appending the bits `a` resp. `b` (both strings having equal
length so far) updates the flag by `flagStep`. -/
theorem flagStep_natFlag_ev {f : Glyph} {x y : ℕ} {pA pB : List Bool} {a b : Bool}
    (h : NatFlag f x y) (hx : x = ofBits pA) (hy : y = ofBits pB)
    (hlen : pA.length = pB.length) :
    NatFlag (flagStep f a b) (ofBits (pA ++ [a])) (ofBits (pB ++ [b])) := by
  subst hx; subst hy
  have hp : 2 ^ pA.length = 2 ^ pB.length := by rw [hlen]
  have hA1 : ofBits (pA ++ [true]) = ofBits pA + 2 ^ pA.length := by
    rw [ofBits_append]; simp [ofBits]
  have hB1 : ofBits (pB ++ [true]) = ofBits pB + 2 ^ pB.length := by
    rw [ofBits_append]; simp [ofBits]
  have hA0 : ofBits (pA ++ [false]) = ofBits pA := by
    rw [ofBits_append]; simp [ofBits]
  have hB0 : ofBits (pB ++ [false]) = ofBits pB := by
    rw [ofBits_append]; simp [ofBits]
  have hAx : ofBits pA < 2 ^ pA.length := ofBits_lt_two_pow pA
  have hBy : ofBits pB < 2 ^ pB.length := ofBits_lt_two_pow pB
  cases a <;> cases b
  · have hf : flagStep f false false = f := by simp [flagStep]
    rw [hf, hA0, hB0]; exact h
  · have hf : flagStep f false true = gLt := by simp [flagStep]
    rw [hf, hA0, hB1]
    exact Or.inl ⟨rfl, by omega⟩
  · have hf : flagStep f true false = gGt := by simp [flagStep]
    rw [hf, hA1, hB0]
    exact Or.inr (Or.inr ⟨rfl, by omega⟩)
  · have hf : flagStep f true true = f := by simp [flagStep]
    rw [hf, hA1, hB1, ← hlen]
    exact natFlag_add f (ofBits pA) (ofBits pB) (2 ^ pA.length) h

/-! ## List plumbing for the induction step -/

theorem take_succ_eq (A : List Bool) (i : ℕ) (h : i < A.length) :
    A.take (i + 1) = A.take i ++ [A[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some]

theorem map_bit_take_succ_rev (A : List Bool) (i : ℕ) (h : i < A.length) :
    ((A.take (i + 1)).map Glyph.bit).reverse =
      Glyph.bit A[i] :: ((A.take i).map Glyph.bit).reverse := by
  rw [take_succ_eq A i h, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]

/-! ## The loop body, case by case -/

/-- The `moveCmd` part of the loop body: one bit from each stack goes to the corresponding buffer;
the stacks keep their frame markers and everything else is untouched. -/
theorem moveCmd_ev (main : Cmd) (s : State) (sA sB bA bB : Stk)
    (a b : Bool) (A' B' : List Bool) (RA RB : List Glyph)
    (hA : s.stk sA = Glyph.bit a :: A'.map Glyph.bit ++ gM :: RA)
    (hB : s.stk sB = Glyph.bit b :: B'.map Glyph.bit ++ gM :: RB)
    (hsAB : sA ≠ sB) (hbA1 : bA ≠ sA) (hbA2 : bA ≠ sB) (hbB1 : bB ≠ sA) (hbB2 : bB ≠ sB)
    (hbAB : bA ≠ bB) :
    ∃ s' n, Eval main (moveCmd sA sB bA bB) s s' n ∧ n ≤ 4 ∧
      s'.stk sA = A'.map Glyph.bit ++ gM :: RA ∧
      s'.stk sB = B'.map Glyph.bit ++ gM :: RB ∧
      s'.stk bA = Glyph.bit a :: s.stk bA ∧
      s'.stk bB = Glyph.bit b :: s.stk bB ∧
      s'.reg rGA = Glyph.bit a ∧ s'.reg rGB = Glyph.bit b ∧
      s'.reg rCont = s.reg rCont ∧ s'.reg rFlag = s.reg rFlag ∧
      (∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  let s1 : State := State.tPop s sA rGA
  let s2 : State := State.tPush s1 bA rGA
  let s3 : State := State.tPop s2 sB rGB
  let s4 : State := State.tPush s3 bB rGB
  have e1 : Eval main (.pop sA rGA) s s1 1 := eval_pop main sA rGA s
  have e2 : Eval main (.push bA rGA) s1 s2 1 := eval_push main bA rGA s1
  have e3 : Eval main (.pop sB rGB) s2 s3 1 := eval_pop main sB rGB s2
  have e4 : Eval main (.push bB rGB) s3 s4 1 := eval_push main bB rGB s3
  have hev : Eval main (moveCmd sA sB bA bB) s s4 4 := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  have hAB : sA ≠ sB := hsAB
  have hBA : sB ≠ sA := hsAB.symm
  have hA1 : sA ≠ bA := fun h => hbA1 h.symm
  have h1A : bA ≠ sA := hbA1
  have hA2 : sA ≠ bB := fun h => hbB1 h.symm
  have h2A : bB ≠ sA := hbB1
  have hB1 : sB ≠ bA := fun h => hbA2 h.symm
  have h1B : bA ≠ sB := hbA2
  have hB2 : sB ≠ bB := fun h => hbB2 h.symm
  have h2B : bB ≠ sB := hbB2
  have h12 : bA ≠ bB := hbAB
  have h21 : bB ≠ bA := hbAB.symm
  refine ⟨s4, 4, hev, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [s4, s3, s2, s1, State.tPop, State.tPush, State.updStk, State.updReg,
      Function.update_apply] <;>
    simp_all [rGA_ne_rGB, rGA_ne_rCont, rGA_ne_rFlag, rGB_ne_rCont, rGB_ne_rFlag,
      rCont_ne_rFlag, rCont_ne_rGA, rCont_ne_rGB, rFlag_ne_rGA, rFlag_ne_rGB, rFlag_ne_rCont]

/-- The loop body when both stacks have reached their markers: keep the flag, stop. -/
theorem scanBody_mm_ev (main : Cmd) (s : State) (sA sB bA bB : Stk) (TA TB : List Glyph)
    (hA : s.stk sA = gM :: TA) (hB : s.stk sB = gM :: TB) (hC : s.reg rCont = Glyph.eos) :
    ∃ s' n, Eval main (scanBody sA sB bA bB) s s' n ∧ n ≤ 6 ∧
      s'.stk sA = s.stk sA ∧ s'.stk sB = s.stk sB ∧
      s'.stk bA = s.stk bA ∧ s'.stk bB = s.stk bB ∧
      s'.reg rCont = gStop ∧ s'.reg rFlag = s.reg rFlag ∧
      (∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  let t1 : State := State.tPeek s sA rGA
  let t2 : State := State.tPeek t1 sB rGB
  let t3 : State := State.tSet t2 rCont gStop
  have e1 : Eval main (.peek sA rGA) s t1 1 := eval_peek main sA rGA s
  have e2 : Eval main (.peek sB rGB) t1 t2 1 := eval_peek main sB rGB t1
  have h1 : t1.reg rGA = gM := by
    simp only [t1, State.tPeek, State.updReg, Function.update_self]
    rw [hA]; simp
  have h2 : t2.reg rGB = gM := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_self, State.updReg_stk]
    rw [hB]; simp
  have e3 : Eval main (.set rCont gStop) t2 t3 1 := eval_set main rCont gStop t2
  have e23 : Eval main (.ite rGB gM (.set rCont gStop)
      (.seq (.set rFlag gLt) (.set rCont gStop))) t2 t3 2 := Eval.iteT h2 e3
  have ebig : Eval main (.ite rGA gM
      (.ite rGB gM (.set rCont gStop) (.seq (.set rFlag gLt) (.set rCont gStop)))
      (.ite rGB gM (.seq (.set rFlag gGt) (.set rCont gStop))
        (.seq (moveCmd sA sB bA bB) flagCmd))) t2 t3 3 := Eval.iteT h1 e23
  have hev : Eval main (scanBody sA sB bA bB) s t3 5 := Eval.seq e1 (Eval.seq e2 ebig)
  refine ⟨t3, 5, hev, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [t3, t2, t1, State.tSet, State.tPeek, State.updStk, State.updReg,
      Function.update_apply, Function.update_self, State.updReg_stk] <;>
    simp_all [rFlag_ne_rGA, rFlag_ne_rGB, rCont_ne_rFlag, rGA_ne_rGB, rGA_ne_rCont,
      rGA_ne_rFlag, rGB_ne_rCont, rGB_ne_rFlag, rCont_ne_rGA, rCont_ne_rGB, rFlag_ne_rCont]

/-- The loop body when the first stack has reached its marker but the second still holds a bit. -/
theorem scanBody_mb_ev (main : Cmd) (s : State) (sA sB bA bB : Stk)
    (TA : List Glyph) (b : Bool) (TB : List Glyph)
    (hA : s.stk sA = gM :: TA) (hB : s.stk sB = Glyph.bit b :: TB)
    (hC : s.reg rCont = Glyph.eos) :
    ∃ s' n, Eval main (scanBody sA sB bA bB) s s' n ∧ n ≤ 7 ∧
      s'.stk sA = s.stk sA ∧ s'.stk sB = s.stk sB ∧
      s'.stk bA = s.stk bA ∧ s'.stk bB = s.stk bB ∧
      s'.reg rCont = gStop ∧ s'.reg rFlag = gLt ∧
      (∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  let t1 : State := State.tPeek s sA rGA
  let t2 : State := State.tPeek t1 sB rGB
  let t3 : State := State.tSet t2 rFlag gLt
  let t4 : State := State.tSet t3 rCont gStop
  have e1 : Eval main (.peek sA rGA) s t1 1 := eval_peek main sA rGA s
  have e2 : Eval main (.peek sB rGB) t1 t2 1 := eval_peek main sB rGB t1
  have h1 : t1.reg rGA = gM := by
    simp only [t1, State.tPeek, State.updReg, Function.update_self]
    rw [hA]; simp
  have h2 : t2.reg rGB = Glyph.bit b := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_self, State.updReg_stk]
    rw [hB]; simp
  have h2' : ¬ (t2.reg rGB = gM) := by rw [h2]; exact bit_ne_gM b
  have e3 : Eval main (.set rFlag gLt) t2 t3 1 := eval_set main rFlag gLt t2
  have e4 : Eval main (.set rCont gStop) t3 t4 1 := eval_set main rCont gStop t3
  have e34 : Eval main (.seq (.set rFlag gLt) (.set rCont gStop)) t2 t4 2 := Eval.seq e3 e4
  have e23 : Eval main (.ite rGB gM (.set rCont gStop)
      (.seq (.set rFlag gLt) (.set rCont gStop))) t2 t4 3 := Eval.iteF h2' e34
  have ebig : Eval main (.ite rGA gM
      (.ite rGB gM (.set rCont gStop) (.seq (.set rFlag gLt) (.set rCont gStop)))
      (.ite rGB gM (.seq (.set rFlag gGt) (.set rCont gStop))
        (.seq (moveCmd sA sB bA bB) flagCmd))) t2 t4 4 := Eval.iteT h1 e23
  have hev : Eval main (scanBody sA sB bA bB) s t4 6 := Eval.seq e1 (Eval.seq e2 ebig)
  refine ⟨t4, 6, hev, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [t4, t3, t2, t1, State.tSet, State.tPeek, State.updStk, State.updReg,
      Function.update_apply, Function.update_self, State.updReg_stk] <;>
    simp_all [rFlag_ne_rGA, rFlag_ne_rGB, rCont_ne_rFlag, rCont_ne_rGA, rCont_ne_rGB,
      rGA_ne_rGB, rGA_ne_rCont, rGA_ne_rFlag, rGB_ne_rCont, rGB_ne_rFlag, rFlag_ne_rCont]

/-- The loop body when the second stack has reached its marker but the first still holds a bit. -/
theorem scanBody_bm_ev (main : Cmd) (s : State) (sA sB bA bB : Stk)
    (TB : List Glyph) (a : Bool) (TA : List Glyph)
    (hA : s.stk sA = Glyph.bit a :: TA) (hB : s.stk sB = gM :: TB)
    (hC : s.reg rCont = Glyph.eos) :
    ∃ s' n, Eval main (scanBody sA sB bA bB) s s' n ∧ n ≤ 7 ∧
      s'.stk sA = s.stk sA ∧ s'.stk sB = s.stk sB ∧
      s'.stk bA = s.stk bA ∧ s'.stk bB = s.stk bB ∧
      s'.reg rCont = gStop ∧ s'.reg rFlag = gGt ∧
      (∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  let t1 : State := State.tPeek s sA rGA
  let t2 : State := State.tPeek t1 sB rGB
  let t3 : State := State.tSet t2 rFlag gGt
  let t4 : State := State.tSet t3 rCont gStop
  have e1 : Eval main (.peek sA rGA) s t1 1 := eval_peek main sA rGA s
  have e2 : Eval main (.peek sB rGB) t1 t2 1 := eval_peek main sB rGB t1
  have h1 : ¬ (t1.reg rGA = gM) := by
    simp only [t1, State.tPeek, State.updReg, Function.update_self]
    rw [hA]; simp [bit_ne_gM a]
  have h2 : t2.reg rGB = gM := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_self, State.updReg_stk]
    rw [hB]; simp
  have e3 : Eval main (.set rFlag gGt) t2 t3 1 := eval_set main rFlag gGt t2
  have e4 : Eval main (.set rCont gStop) t3 t4 1 := eval_set main rCont gStop t3
  have e34 : Eval main (.seq (.set rFlag gGt) (.set rCont gStop)) t2 t4 2 := Eval.seq e3 e4
  have e23 : Eval main (.ite rGB gM (.seq (.set rFlag gGt) (.set rCont gStop))
      (.seq (moveCmd sA sB bA bB) flagCmd)) t2 t4 3 := Eval.iteT h2 e34
  have ebig : Eval main (.ite rGA gM
      (.ite rGB gM (.set rCont gStop) (.seq (.set rFlag gLt) (.set rCont gStop)))
      (.ite rGB gM (.seq (.set rFlag gGt) (.set rCont gStop))
        (.seq (moveCmd sA sB bA bB) flagCmd))) t2 t4 4 := Eval.iteF h1 e23
  have hev : Eval main (scanBody sA sB bA bB) s t4 6 := Eval.seq e1 (Eval.seq e2 ebig)
  refine ⟨t4, 6, hev, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [t4, t3, t2, t1, State.tSet, State.tPeek, State.updStk, State.updReg,
      Function.update_apply, Function.update_self, State.updReg_stk] <;>
    simp_all [rFlag_ne_rGA, rFlag_ne_rGB, rCont_ne_rFlag, rCont_ne_rGA, rCont_ne_rGB,
      rGA_ne_rGB, rGA_ne_rCont, rGA_ne_rFlag, rGB_ne_rCont, rGB_ne_rFlag, rFlag_ne_rCont]

/-- The loop body when both stacks still hold a bit: the two bits go to the buffers and the flag
is updated. -/
theorem scanBody_bits_ev (main : Cmd) (s : State) (sA sB bA bB : Stk) (a b : Bool)
    (A' B' : List Bool) (RA RB : List Glyph)
    (hA : s.stk sA = Glyph.bit a :: A'.map Glyph.bit ++ gM :: RA)
    (hB : s.stk sB = Glyph.bit b :: B'.map Glyph.bit ++ gM :: RB)
    (hsAB : sA ≠ sB) (hbA1 : bA ≠ sA) (hbA2 : bA ≠ sB) (hbB1 : bB ≠ sA) (hbB2 : bB ≠ sB)
    (hbAB : bA ≠ bB) :
    ∃ s' n, Eval main (scanBody sA sB bA bB) s s' n ∧ n ≤ 12 ∧
      s'.stk sA = A'.map Glyph.bit ++ gM :: RA ∧
      s'.stk sB = B'.map Glyph.bit ++ gM :: RB ∧
      s'.stk bA = Glyph.bit a :: s.stk bA ∧
      s'.stk bB = Glyph.bit b :: s.stk bB ∧
      s'.reg rCont = s.reg rCont ∧
      s'.reg rFlag = flagStep (s.reg rFlag) a b ∧
      (∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  let t1 : State := State.tPeek s sA rGA
  let t2 : State := State.tPeek t1 sB rGB
  have e1 : Eval main (.peek sA rGA) s t1 1 := eval_peek main sA rGA s
  have e2 : Eval main (.peek sB rGB) t1 t2 1 := eval_peek main sB rGB t1
  have h1' : t2.reg rGA = Glyph.bit a := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_apply, Function.update_self,
      State.updReg_stk]
    rw [hA]; simp [rGA_ne_rGB]
  have h2 : t2.reg rGB = Glyph.bit b := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_self, State.updReg_stk]
    rw [hB]; simp
  have h2a : ¬ (t2.reg rGA = gM) := by rw [h1']; exact bit_ne_gM a
  have h2b : ¬ (t2.reg rGB = gM) := by rw [h2]; exact bit_ne_gM b
  have hAt : t2.stk sA = Glyph.bit a :: A'.map Glyph.bit ++ gM :: RA := by
    simp only [t2, t1, State.tPeek, State.updReg_stk]; exact hA
  have hBt : t2.stk sB = Glyph.bit b :: B'.map Glyph.bit ++ gM :: RB := by
    simp only [t2, t1, State.tPeek, State.updReg_stk]; exact hB
  have ht2f : t2.reg rFlag = s.reg rFlag := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_apply, Function.update_self]
    rw [if_neg rFlag_ne_rGB, if_neg rFlag_ne_rGA]
  have ht2c : t2.reg rCont = s.reg rCont := by
    simp only [t2, t1, State.tPeek, State.updReg, Function.update_apply, Function.update_self]
    rw [if_neg rCont_ne_rGB, if_neg rCont_ne_rGA]
  obtain ⟨s3, n3, hev3, hn3, h3sA, h3sB, h3bA, h3bB, h3GA, h3GB, h3cont, h3flag, h3oth⟩ :=
    moveCmd_ev main t2 sA sB bA bB a b A' B' RA RB hAt hBt hsAB hbA1 hbA2 hbB1 hbB2 hbAB
  obtain ⟨n4, hn4, hev4⟩ := pwScanFlagCmd main s3 a b h3GA h3GB
  let s4 : State := s3.updReg rFlag (flagStep (s3.reg rFlag) a b)
  have hev4' : Eval main flagCmd s3 s4 n4 := hev4
  have h4stk : ∀ j : Stk, s4.stk j = s3.stk j := fun j => rfl
  have hs3t : s3.reg rFlag = s.reg rFlag := by rw [h3flag]; exact ht2f
  have h4cont : s4.reg rCont = s.reg rCont := by
    simp only [s4, State.updReg, Function.update_apply]
    rw [if_neg rCont_ne_rFlag, h3cont, ht2c]
  have h4flag : s4.reg rFlag = flagStep (s.reg rFlag) a b := by
    simp only [s4, State.updReg, Function.update_self]
    rw [hs3t]
  have h4oth : ∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s4.stk j = s.stk j := by
    intro j hj1 hj2 hj3 hj4
    rw [h4stk j, h3oth j hj1 hj2 hj3 hj4]
    simp only [t2, t1, State.tPeek, State.updReg_stk]
  have ebig : Eval main (.ite rGA gM
      (.ite rGB gM (.set rCont gStop) (.seq (.set rFlag gLt) (.set rCont gStop)))
      (.ite rGB gM (.seq (.set rFlag gGt) (.set rCont gStop))
        (.seq (moveCmd sA sB bA bB) flagCmd))) t2 s4 (n3 + n4 + 2) :=
    Eval.iteF h2a (Eval.iteF h2b (Eval.seq hev3 hev4'))
  have hev : Eval main (scanBody sA sB bA bB) s s4 (1 + (1 + (n3 + n4 + 2))) :=
    Eval.seq e1 (Eval.seq e2 ebig)
  refine ⟨s4, 1 + (1 + (n3 + n4 + 2)), hev, by omega, h3sA, h3sB, h3bA, h3bB, h4cont, h4flag,
    h4oth⟩

/-! ## The loop -/

/-- The scan loop from the `i`-th step on: the invariant is that after `i` steps the consumed
prefixes (in reverse, above the marker the program pushed) are on the two buffers and the flag
records the comparison of those prefixes. -/
theorem scanAux (main : Cmd) (sA sB bA bB : Stk)
    (hsAB : sA ≠ sB) (hbA1 : bA ≠ sA) (hbA2 : bA ≠ sB) (hbB1 : bB ≠ sA) (hbB2 : bB ≠ sB)
    (hbAB : bA ≠ bB) :
    ∀ (m : ℕ) (A B : List Bool) (i : ℕ) (RA RB bA0 bB0 : List Glyph) (s : State),
      IsBits A → IsBits B → i ≤ min A.length B.length → min A.length B.length - i = m →
      s.stk sA = (A.drop i).map Glyph.bit ++ gM :: RA →
      s.stk sB = (B.drop i).map Glyph.bit ++ gM :: RB →
      s.stk bA = ((A.take i).map Glyph.bit).reverse ++ gM :: bA0 →
      s.stk bB = ((B.take i).map Glyph.bit).reverse ++ gM :: bB0 →
      s.reg rCont = Glyph.eos →
      s.reg rFlag = flagOf (ofBits (A.take i)) (ofBits (B.take i)) →
      ∃ s' n, Eval main (scanLoop sA sB bA bB) s s' n ∧ n ≤ 13 * (m + 1) ∧
        s'.reg rCont ≠ Glyph.eos ∧
        NatFlag (s'.reg rFlag) (ofBits A) (ofBits B) ∧
        s'.stk sA = (A.drop (min A.length B.length)).map Glyph.bit ++ gM :: RA ∧
        s'.stk sB = (B.drop (min A.length B.length)).map Glyph.bit ++ gM :: RB ∧
        s'.stk bA = ((A.take (min A.length B.length)).map Glyph.bit).reverse ++ gM :: bA0 ∧
        s'.stk bB = ((B.take (min A.length B.length)).map Glyph.bit).reverse ++ gM :: bB0 ∧
        (∀ j : Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  intro m
  induction m with
  | zero =>
    intro A B i RA RB bA0 bB0 s hIsA hIsB hile hmi hA hB hbA hbB hC hF
    have hle : min A.length B.length ≤ i := Nat.le_of_sub_eq_zero hmi
    have hie : i = min A.length B.length := le_antisymm hile hle
    by_cases hAd : A.drop i = []
    · by_cases hBd : B.drop i = []
      · -- both sides exhausted
        have hAlen : A.length ≤ i := List.drop_eq_nil_iff.mp hAd
        have hBlen : B.length ≤ i := List.drop_eq_nil_iff.mp hBd
        have hTA : A.take i = A := List.take_of_length_le hAlen
        have hTB : B.take i = B := List.take_of_length_le hBlen
        have hAmm : s.stk sA = gM :: RA := by rw [hA, hAd, List.map_nil, List.nil_append]
        have hBmm : s.stk sB = gM :: RB := by rw [hB, hBd, List.map_nil, List.nil_append]
        obtain ⟨s1, n1, hev1, hn1, h1sA, h1sB, h1bA, h1bB, h1c, h1f, h1o⟩ :=
          scanBody_mm_ev main s sA sB bA bB RA RB hAmm hBmm hC
        have hstop : s1.reg rCont ≠ Glyph.eos := by rw [h1c]; exact gStop_ne_eos
        have hloop : Eval main (scanLoop sA sB bA bB) s s1 (n1 + 1 + 1) :=
          Eval.loopT (main := main) (r := rCont) (c := Glyph.eos) hC hev1 (Eval.loopF hstop)
        refine ⟨s1, n1 + 1 + 1, hloop, by omega, hstop, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hfl : s1.reg rFlag = flagOf (ofBits A) (ofBits B) := by rw [h1f, hF, hTA, hTB]
          rw [hfl]; exact natFlag_flagOf _ _
        · rw [h1sA, hA, ← hie]
        · rw [h1sB, hB, ← hie]
        · rw [h1bA, hbA, ← hie]
        · rw [h1bB, hbB, ← hie]
        · intro j hj1 hj2 hj3 hj4; exact h1o j hj1 hj2 hj3 hj4
      · -- A exhausted, B still has bits
        have hAlen : A.length ≤ i := List.drop_eq_nil_iff.mp hAd
        have hBlen : i < B.length := by
          have hc : ¬ (B.length ≤ i) := fun h => hBd (List.drop_eq_nil_iff.mpr h)
          omega
        have hTA : A.take i = A := List.take_of_length_le hAlen
        obtain ⟨b, B', hBc⟩ : ∃ (b : Bool) (B' : List Bool), B.drop i = b :: B' := by
          cases h : B.drop i with
          | nil => exact absurd h hBd
          | cons b B' => exact ⟨b, B', rfl⟩
        have hAmm : s.stk sA = gM :: RA := by rw [hA, hAd, List.map_nil, List.nil_append]
        have hBhd : s.stk sB = Glyph.bit b :: B'.map Glyph.bit ++ gM :: RB := by
          rw [hB, hBc, List.map_cons]
        obtain ⟨s1, n1, hev1, hn1, h1sA, h1sB, h1bA, h1bB, h1c, h1f, h1o⟩ :=
          scanBody_mb_ev main s sA sB bA bB RA b (B'.map Glyph.bit ++ gM :: RB) hAmm hBhd hC
        have hstop : s1.reg rCont ≠ Glyph.eos := by rw [h1c]; exact gStop_ne_eos
        have hloop : Eval main (scanLoop sA sB bA bB) s s1 (n1 + 1 + 1) :=
          Eval.loopT (main := main) (r := rCont) (c := Glyph.eos) hC hev1 (Eval.loopF hstop)
        refine ⟨s1, n1 + 1 + 1, hloop, by omega, hstop, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h1f]
          exact Or.inl ⟨rfl, ofBits_lt_of_length_lt hIsA hIsB (by omega)⟩
        · rw [h1sA, hA, ← hie]
        · rw [h1sB, hB, ← hie]
        · rw [h1bA, hbA, ← hie]
        · rw [h1bB, hbB, ← hie]
        · intro j hj1 hj2 hj3 hj4; exact h1o j hj1 hj2 hj3 hj4
    · by_cases hBd : B.drop i = []
      · -- B exhausted, A still has bits
        have hBlen : B.length ≤ i := List.drop_eq_nil_iff.mp hBd
        have hAlen : i < A.length := by
          have hc : ¬ (A.length ≤ i) := fun h => hAd (List.drop_eq_nil_iff.mpr h)
          omega
        have hTB : B.take i = B := List.take_of_length_le hBlen
        obtain ⟨a, A', hAc⟩ : ∃ (a : Bool) (A' : List Bool), A.drop i = a :: A' := by
          cases h : A.drop i with
          | nil => exact absurd h hAd
          | cons a A' => exact ⟨a, A', rfl⟩
        have hBmm : s.stk sB = gM :: RB := by rw [hB, hBd, List.map_nil, List.nil_append]
        have hAhd : s.stk sA = Glyph.bit a :: A'.map Glyph.bit ++ gM :: RA := by
          rw [hA, hAc, List.map_cons]
        obtain ⟨s1, n1, hev1, hn1, h1sA, h1sB, h1bA, h1bB, h1c, h1f, h1o⟩ :=
          scanBody_bm_ev main s sA sB bA bB RB a (A'.map Glyph.bit ++ gM :: RA) hAhd hBmm hC
        have hstop : s1.reg rCont ≠ Glyph.eos := by rw [h1c]; exact gStop_ne_eos
        have hloop : Eval main (scanLoop sA sB bA bB) s s1 (n1 + 1 + 1) :=
          Eval.loopT (main := main) (r := rCont) (c := Glyph.eos) hC hev1 (Eval.loopF hstop)
        refine ⟨s1, n1 + 1 + 1, hloop, by omega, hstop, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h1f]
          exact Or.inr (Or.inr ⟨rfl, ofBits_lt_of_length_lt hIsB hIsA (by omega)⟩)
        · rw [h1sA, hA, ← hie]
        · rw [h1sB, hB, ← hie]
        · rw [h1bA, hbA, ← hie]
        · rw [h1bB, hbB, ← hie]
        · intro j hj1 hj2 hj3 hj4; exact h1o j hj1 hj2 hj3 hj4
      · -- impossible: neither side exhausted at the end of the common prefix
        have hAdl : i < A.length := by
          have hc : ¬ (A.length ≤ i) := fun h => hAd (List.drop_eq_nil_iff.mpr h)
          omega
        have hBdl : i < B.length := by
          have hc : ¬ (B.length ≤ i) := fun h => hBd (List.drop_eq_nil_iff.mpr h)
          omega
        exact absurd (Nat.lt_min.mpr ⟨hAdl, hBdl⟩) (by omega)
  | succ m ih =>
    intro A B i RA RB bA0 bB0 s hIsA hIsB hile hmi hA hB hbA hbB hC hF
    have hilt : i < min A.length B.length := by omega
    have hiA : i < A.length := lt_of_lt_of_le hilt (Nat.min_le_left _ _)
    have hiB : i < B.length := lt_of_lt_of_le hilt (Nat.min_le_right _ _)
    have hA' : s.stk sA = Glyph.bit A[i] :: (A.drop (i + 1)).map Glyph.bit ++ gM :: RA := by
      rw [hA, List.drop_eq_getElem_cons hiA, List.map_cons]
    have hB' : s.stk sB = Glyph.bit B[i] :: (B.drop (i + 1)).map Glyph.bit ++ gM :: RB := by
      rw [hB, List.drop_eq_getElem_cons hiB, List.map_cons]
    obtain ⟨s1, n1, hev1, hn1, h1sA, h1sB, h1bA, h1bB, h1c, h1f, h1o⟩ :=
      scanBody_bits_ev main s sA sB bA bB A[i] B[i] (A.drop (i + 1)) (B.drop (i + 1)) RA RB
        hA' hB' hsAB hbA1 hbA2 hbB1 hbB2 hbAB
    have hbA' : s1.stk bA = ((A.take (i + 1)).map Glyph.bit).reverse ++ gM :: bA0 := by
      rw [h1bA, hbA, map_bit_take_succ_rev A i hiA, List.cons_append]
    have hbB' : s1.stk bB = ((B.take (i + 1)).map Glyph.bit).reverse ++ gM :: bB0 := by
      rw [h1bB, hbB, map_bit_take_succ_rev B i hiB, List.cons_append]
    have hlen : (A.take i).length = (B.take i).length := by
      rw [List.length_take, List.length_take,
        Nat.min_eq_left (le_trans hile (Nat.min_le_left _ _)),
        Nat.min_eq_left (le_trans hile (Nat.min_le_right _ _))]
    have hstep : NatFlag (flagStep (flagOf (ofBits (A.take i)) (ofBits (B.take i))) A[i] B[i])
        (ofBits (A.take (i + 1))) (ofBits (B.take (i + 1))) := by
      rw [take_succ_eq A i hiA, take_succ_eq B i hiB]
      exact flagStep_natFlag_ev (natFlag_flagOf _ _) rfl rfl hlen
    have hflag' : s1.reg rFlag = flagOf (ofBits (A.take (i + 1))) (ofBits (B.take (i + 1))) := by
      rw [h1f, hF]
      exact eq_flagOf_of_natFlag hstep
    have hmi' : min A.length B.length - (i + 1) = m := by omega
    have hile' : i + 1 ≤ min A.length B.length := by omega
    have h1c' : s1.reg rCont = Glyph.eos := by rw [h1c]; exact hC
    obtain ⟨s2, n2, hev2, hn2, h2c, h2f, h2sA, h2sB, h2bA, h2bB, h2o⟩ :=
      ih A B (i + 1) RA RB bA0 bB0 s1 hIsA hIsB hile' hmi' h1sA h1sB hbA' hbB' h1c' hflag'
    refine ⟨s2, n1 + n2 + 1, ?_, by omega, h2c, h2f, h2sA, h2sB, h2bA, h2bB, ?_⟩
    · exact Eval.loopT (main := main) (r := rCont) (c := Glyph.eos) hC hev1 hev2
    · intro j hj1 hj2 hj3 hj4
      rw [h2o j hj1 hj2 hj3 hj4, h1o j hj1 hj2 hj3 hj4]

end Work.Transform.Pw

namespace Work.Transform

open HvdH
open Work.Kernel
open Work.IntLib
open Work.Transform.Pw

/-! ## The statement -/

theorem pwScanB (sA sB bA bB : HvdH.Stk) :
    sA ≠ sB → bA ≠ sA → bA ≠ sB → bB ≠ sA → bB ≠ sB → bA ≠ bB →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (A B : List Bool) (RA RB : List HvdH.Glyph) (s : HvdH.State),
      Work.IntLib.IsBits A → Work.IntLib.IsBits B →
      s.stk sA = A.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: RA →
      s.stk sB = B.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: RB →
      s.reg Work.Transform.Pw.rCont = HvdH.Glyph.eos →
      s.reg Work.Transform.Pw.rFlag = Work.Transform.Pw.gEq →
      ∃ s' n, HvdH.Eval main prog s s' n ∧
        n ≤ K * (min A.length B.length + 1) ∧
        s'.reg Work.Transform.Pw.rCont ≠ HvdH.Glyph.eos ∧
        Work.Transform.Pw.NatFlag (s'.reg Work.Transform.Pw.rFlag)
          (Work.IntLib.ofBits A) (Work.IntLib.ofBits B) ∧
        s'.stk sA = (A.drop (min A.length B.length)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: RA ∧
        s'.stk sB = (B.drop (min A.length B.length)).map HvdH.Glyph.bit
            ++ Work.Transform.Pw.gM :: RB ∧
        s'.stk bA = ((A.take (min A.length B.length)).map HvdH.Glyph.bit).reverse
            ++ Work.Transform.Pw.gM :: s.stk bA ∧
        s'.stk bB = ((B.take (min A.length B.length)).map HvdH.Glyph.bit).reverse
            ++ Work.Transform.Pw.gM :: s.stk bB ∧
        (∀ j : HvdH.Stk, j ≠ sA → j ≠ sB → j ≠ bA → j ≠ bB → s'.stk j = s.stk j) := by
  intro hsAB hbA1 hbA2 hbB1 hbB2 hbAB
  refine ⟨scanProg sA sB bA bB, 20, ?_⟩
  intro main A B RA RB s hIsA hIsB hA hB hCont hFlag
  have hAsB : sA ≠ sB := hsAB
  have hBsA : sB ≠ sA := hsAB.symm
  have hAs1 : sA ≠ bA := fun h => hbA1 h.symm
  have hs1A : bA ≠ sA := hbA1
  have hAs2 : sA ≠ bB := fun h => hbB1 h.symm
  have hs2A : bB ≠ sA := hbB1
  have hBs1 : sB ≠ bA := fun h => hbA2 h.symm
  have hs1B : bA ≠ sB := hbA2
  have hBs2 : sB ≠ bB := fun h => hbB2 h.symm
  have hs2B : bB ≠ sB := hbB2
  have hs12 : bA ≠ bB := hbAB
  have hs21 : bB ≠ bA := hbAB.symm
  let s0 : State := State.tSet s rFlag gEq
  let s1 : State := State.tSet s0 rCont Glyph.eos
  let s2 : State := State.tSet s1 rGB gM
  let s3 : State := State.tPush s2 bA rGB
  let s4 : State := State.tSet s3 rGB gM
  let s5 : State := State.tPush s4 bB rGB
  have e1 : Eval main (.set rFlag gEq) s s0 1 := eval_set main rFlag gEq s
  have e2 : Eval main (.set rCont Glyph.eos) s0 s1 1 := eval_set main rCont Glyph.eos s0
  have e3 : Eval main (.set rGB gM) s1 s2 1 := eval_set main rGB gM s1
  have e4 : Eval main (.push bA rGB) s2 s3 1 := eval_push main bA rGB s2
  have e5 : Eval main (.set rGB gM) s3 s4 1 := eval_set main rGB gM s3
  have e6 : Eval main (.push bB rGB) s4 s5 1 := eval_push main bB rGB s4
  have hs5sA : s5.stk sA = A.map Glyph.bit ++ gM :: RA := by
    have h : s5.stk sA = s.stk sA := by
      simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
        Function.update_apply, Function.update_self]
      simp_all
    rw [h, hA]
  have hs5sB : s5.stk sB = B.map Glyph.bit ++ gM :: RB := by
    have h : s5.stk sB = s.stk sB := by
      simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
        Function.update_apply, Function.update_self]
      simp_all
    rw [h, hB]
  have hs5bA : s5.stk bA = gM :: s.stk bA := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all
  have hs5bB : s5.stk bB = gM :: s.stk bB := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all
  have hs5c : s5.reg rCont = Glyph.eos := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all [rGB_ne_rCont, rCont_ne_rGB]
  have hs5f : s5.reg rFlag = flagOf (ofBits (A.take 0)) (ofBits (B.take 0)) := by
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self, List.take_zero, ofBits]
    simp_all [rGB_ne_rFlag, rFlag_ne_rGB, rFlag_ne_rCont, flagOf_zero_zero]
  obtain ⟨s', n, hev, hn, hcont, hflag, htA, htB, htbA, htbB, hoth⟩ :=
    scanAux main sA sB bA bB hsAB hbA1 hbA2 hbB1 hbB2 hbAB (min A.length B.length) A B 0
      RA RB (s.stk bA) (s.stk bB) s5 hIsA hIsB (Nat.zero_le _) (by simp) hs5sA hs5sB
      (by simpa using hs5bA) (by simpa using hs5bB) hs5c hs5f
  have hev0 : Eval main (scanProg sA sB bA bB) s s'
      (1 + (1 + (1 + (1 + (1 + (1 + n)))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 hev)))))
  refine ⟨s', 1 + (1 + (1 + (1 + (1 + (1 + n))))), hev0, by omega, hcont, hflag, htA, htB,
    ?_, ?_, ?_⟩
  · exact htbA
  · exact htbB
  · intro j hj1 hj2 hj3 hj4
    rw [hoth j hj1 hj2 hj3 hj4]
    simp only [s5, s4, s3, s2, s1, s0, State.tPush, State.tSet, State.updStk, State.updReg,
      Function.update_apply, Function.update_self]
    simp_all

end Work.Transform
