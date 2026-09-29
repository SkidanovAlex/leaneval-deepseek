import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.parseEmitDefs
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.splitGlyphEval
import Submission.Work.IntLib.drainAllEval
import Submission.Work.IntLib.drainUntilEval
import Submission.Work.IntLib.splitLoopEval
import Submission.Work.IntLib.pushAccBitsZipWithAll

/-!
# IntLib: the top-level `parse` / `emit` words

This file proves both halves of the requested lemma `Work.IntLib.parseEmitWord`:

* `emitEval`: `emitProg` turns the encoding `(Val.int z).enc` of a natural number `z`, sitting alone
  on stack 0 (with stack 1 empty), into the bits of `z` (least significant bit first, hence first
  bit on top) on stack 1, at cost `≤ 21 * (z.size + 1)`;
* `parseEval`: `parseProg` turns the raw input word
  `(IntegerMultiplication.encodeProd encodeNat encodeNat (x, y)).map inpGlyph` on stack 0 into
  `encs [Val.int x, Val.int y]`, at cost `≤ 100 * (length + 1)`.

Both proofs are raw `Eval` chains assembled from the words of `parseEmitDefs.lean`; the loops are
handled by the delegated lemmas `splitGlyphEval`, `drainAllEval`, `drainUntilEval`, `splitLoopEval`
(which turn a loop into a single `Eval` step with an explicit cost) and the list algebra of the
accumulators is `pushAccBitsZipWithAll`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Self-contained helper lemmas -/


theorem enc_int_natCast (z : ℕ) :
    (Val.int (z : ℤ)).enc = Glyph.pos :: ((Computability.encodeNat z).map Glyph.bit ++ [Glyph.iend]) := by
  rw [enc_int]
  simp [Int.natAbs_natCast]

theorem zipWithAll_length {α β γ : Type*} (f : Option α → Option β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), (List.zipWithAll f l₁ l₂).length = max l₁.length l₂.length
  | [], [] => rfl
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | _ :: as, _ :: bs => by
      rw [List.zipWithAll_cons_cons, List.length_cons, zipWithAll_length f as bs, List.length_cons,
        List.length_cons]
      omega

theorem bit_ne_eos (b : Bool) : Glyph.bit b ≠ Glyph.eos := by intro h; cases h
theorem bit_ne_iend_pe (b : Bool) : Glyph.bit b ≠ Glyph.iend := by intro h; cases h
theorem bit_ne_mk (b : Bool) (i : Fin 16) : Glyph.bit b ≠ Glyph.mk i := by intro h; cases h
theorem iend_ne_eos : Glyph.iend ≠ Glyph.eos := by intro h; cases h
theorem iend_ne_mk (i : Fin 16) : Glyph.iend ≠ Glyph.mk i := by intro h; cases h
theorem pos_ne_mk (i : Fin 16) : Glyph.pos ≠ Glyph.mk i := by intro h; cases h
theorem inp_ne_eos (a b : Option Bool) : Glyph.inp a b ≠ Glyph.eos := by intro h; cases h
theorem inp_ne_iend (a b : Option Bool) : Glyph.inp a b ≠ Glyph.iend := by intro h; cases h
theorem inp_ne_pos (a b : Option Bool) : Glyph.inp a b ≠ Glyph.pos := by intro h; cases h

theorem inpGlyph_ne_eos (p : InSym) : inpGlyph p ≠ Glyph.eos := by
  obtain ⟨a, b⟩ := p; exact inp_ne_eos a b

theorem map_bit_ne (l : List Bool) (i : Fin 16) : ∀ g ∈ l.map Glyph.bit, g ≠ Glyph.mk i := by
  intro g hg
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
  exact bit_ne_mk b i

theorem map_bit_append_iend_ne_eos (l : List Bool) :
    ∀ g ∈ l.map Glyph.bit ++ [Glyph.iend], g ≠ Glyph.eos := by
  intro g hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    exact bit_ne_eos b
  · exact iend_ne_eos

/-! ## The `emit` word -/

theorem bits_append_iend_ne_eos (z : ℕ) (bits : List Glyph)
    (hbits : bits = (Computability.encodeNat z).map Glyph.bit) :
    ∀ g ∈ bits ++ [Glyph.iend], g ≠ Glyph.eos := by
  intro g hg
  rw [hbits] at hg
  exact map_bit_append_iend_ne_eos (Computability.encodeNat z) g hg

theorem emitEval (main : Cmd) (z : ℕ) (s : State)
    (h0 : s.stk 0 = (Val.int (z : ℤ)).enc) (h1 : s.stk 1 = []) :
    ∃ (s' : State) (n : ℕ), Eval main emitProg s s' n ∧ n ≤ 21 * (z.size + 1) ∧
      s'.stk 0 = [] ∧ s'.stk 1 = (Computability.encodeNat z).map Glyph.bit ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  set bits : List Glyph := (Computability.encodeNat z).map Glyph.bit with hbits
  have hlen : bits.length = z.size := by rw [hbits, List.length_map, encodeNat_length]
  have hs0 : s.stk 0 = Glyph.pos :: (bits ++ [Glyph.iend]) := by
    rw [h0, enc_int_natCast, hbits]
  -- step A: drop the sign glyph
  set s1 : State := State.tPop s 0 5 with hs1
  have hA : Eval main (Cmd.pop 0 5) s s1 1 := by rw [hs1]; exact Work.Kernel.eval_pop main 0 5 s
  have hs1_0 : s1.stk 0 = bits ++ [Glyph.iend] := by
    rw [hs1]; simp [State.tPop, hs0]
  have hs1_1 : s1.stk 1 = [] := by rw [hs1]; simp [State.tPop, h1]
  have hs1_k : ∀ k : Stk, k ≠ 0 → s1.stk k = s.stk k := by
    intro k hk; rw [hs1]; simp [State.tPop, hk]
  -- step B: marker on stack 2
  set s2 : State := State.tPush (State.tSet s1 5 (Glyph.mk 1)) 2 5 with hs2
  have hB : Eval main (pushConst 2 (Glyph.mk 1) 5) s1 s2 2 := by
    rw [hs2, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 (Glyph.mk 1) s1)
      (Work.Kernel.eval_push main 2 5 (State.tSet s1 5 (Glyph.mk 1)))
  have hs2_0 : s2.stk 0 = bits ++ [Glyph.iend] := by
    rw [hs2]; simp [State.tPush, State.tSet, hs1_0]
  have hs2_2 : s2.stk 2 = Glyph.mk 1 :: s.stk 2 := by
    rw [hs2]; simp [State.tPush, State.tSet, hs1_k 2 (by decide)]
  have hs2_k : ∀ k : Stk, k ≠ 0 → k ≠ 2 → s2.stk k = s.stk k := by
    intro k hk0 hk2
    rw [hs2]; simp [State.tPush, State.tSet, hk2, hs1_k k hk0]
  -- step C: move the bits onto stack 2 (reversing them)
  obtain ⟨s3, n3, hn3, hC, hs3_0, hs3_2, hs3_reg, hs3_k⟩ :=
    drainAllEval main 0 2 (by decide) 5 (bits ++ [Glyph.iend]) s2
      (bits_append_iend_ne_eos z bits hbits) (by rw [hs2_0])
  have hs3_1 : s3.stk 1 = [] := by
    have h1' : s3.stk 1 = s2.stk 1 := hs3_k 1 (by decide) (by decide)
    have h2' : s2.stk 1 = s1.stk 1 := hs2_k 1 (by decide) (by decide)
    rw [h1', h2', hs1_1]
  have hs3_2' : s3.stk 2 = Glyph.iend :: (bits.reverse ++ Glyph.mk 1 :: s.stk 2) := by
    rw [hs3_2, hs2_2, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    rfl
  -- step D: drop the `iend`
  set s4 : State := State.tPop s3 2 5 with hs4
  have hD : Eval main (Cmd.pop 2 5) s3 s4 1 := by rw [hs4]; exact Work.Kernel.eval_pop main 2 5 s3
  have hs4_2 : s4.stk 2 = bits.reverse ++ Glyph.mk 1 :: s.stk 2 := by
    rw [hs4]; simp [State.tPop, hs3_2']
  have hs4_1 : s4.stk 1 = [] := by rw [hs4]; simp [State.tPop, hs3_1]
  have hs4_0 : s4.stk 0 = [] := by rw [hs4]; simp [State.tPop, hs3_0]
  have hs4_k : ∀ k : Stk, k ≠ 2 → s4.stk k = s3.stk k := by
    intro k hk; rw [hs4]; simp [State.tPop, hk]
  -- step E: move the bits onto stack 1
  have hne5 : ∀ g ∈ bits.reverse, g ≠ Glyph.mk 1 := by
    intro g hg
    rw [hbits, ← List.map_reverse] at hg
    exact map_bit_ne (Computability.encodeNat z).reverse 1 g hg
  obtain ⟨s5, n5, hn5, hE, hs5_2, hs5_1, hs5_reg, hs5_k⟩ :=
    drainUntilEval main 2 1 (by decide) (Glyph.mk 1) 5 bits.reverse (s.stk 2) s4 hne5
      (by rw [hs4_2])
  have hs5_1' : s5.stk 1 = bits := by
    rw [hs5_1, List.reverse_reverse, hs4_1, List.append_nil]
  have hs5_0 : s5.stk 0 = [] := by rw [hs5_k 0 (by decide) (by decide), hs4_0]
  have hframes : ∀ k : Stk, k ≠ 0 → k ≠ 1 → s5.stk k = s.stk k := by
    intro k hk0 hk1
    by_cases hk2 : k = 2
    · subst hk2; exact hs5_2
    · rw [hs5_k k hk2 hk1, hs4_k k hk2, hs3_k k hk0 hk2, hs2_k k hk0 hk2]
  -- assembly
  have hmain : Eval main emitProg s s5 (1 + (2 + (n3 + (1 + n5)))) := by
    rw [emitProg]
    exact Eval.seq hA (Eval.seq hB (Eval.seq hC (Eval.seq hD hE)))
  refine ⟨s5, 1 + (2 + (n3 + (1 + n5))), hmain, ?_, hs5_0, hs5_1', hframes⟩
  have hlen2 : (bits ++ [Glyph.iend]).length = z.size + 1 := by
    rw [List.length_append, hlen]; simp
  have hn5' : n5 ≤ 5 * z.size + 6 := by
    rw [List.length_reverse, hlen] at hn5; omega
  have hn3' : n3 ≤ 5 * z.size + 11 := by
    rw [hlen2] at hn3; omega
  omega


/-! ## Component lemmas for the canonical states -/

theorem tPush_stk_same (X : State) (k : Stk) (r : Reg) :
    (State.tPush X k r).stk k = X.reg r :: X.stk k := by simp [State.tPush]

theorem tPush_stk_ne_pe (X : State) {k j : Stk} (r : Reg) (h : j ≠ k) :
    (State.tPush X k r).stk j = X.stk j := by simp [State.tPush, h]

theorem tPush_reg_pe (X : State) (k : Stk) (r : Reg) : (State.tPush X k r).reg = X.reg := rfl

theorem tSet_stk_pe (X : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet X r g).stk j = X.stk j := by simp [State.tSet]

theorem tSet_reg_same (X : State) (r : Reg) (g : Glyph) : (State.tSet X r g).reg r = g := by
  simp [State.tSet, State.updReg_apply]

theorem tSet_reg_ne_pe (X : State) (r : Reg) (g : Glyph) {r' : Reg} (h : r' ≠ r) :
    (State.tSet X r g).reg r' = X.reg r' := by
  simp [State.tSet, State.updReg_apply, h]

theorem tPop_stk_same (X : State) (k : Stk) (r : Reg) : (State.tPop X k r).stk k = (X.stk k).tail := by
  simp [State.tPop]

theorem tPop_stk_ne_pe (X : State) {k j : Stk} (r : Reg) (h : j ≠ k) :
    (State.tPop X k r).stk j = X.stk j := by simp [State.tPop, h]

/-! ## The `parse` word -/

theorem parseEval (main : Cmd) (x y : ℕ) (s : State)
    (h0 : s.stk 0 =
      (IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat (x, y)).map inpGlyph) :
    ∃ (s' : State) (n : ℕ), Eval main parseProg s s' n ∧
      n ≤ 100 * ((IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat
        (x, y)).length + 1) ∧
      s'.stk 0 = encs [Val.int (x : ℤ), Val.int (y : ℤ)] ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) := by
  set bx : List Bool := Computability.encodeNat x with hbx
  set bY : List Bool := Computability.encodeNat y with hbY
  set W : List Glyph :=
    (List.zipWithAll Prod.mk (Computability.encodeNat x) (Computability.encodeNat y)).map inpGlyph
    with hW
  have hsW : s.stk 0 = W := by rw [h0, hW]; rfl
  have hWne : ∀ g ∈ W, g ≠ Glyph.eos := by
    intro g hg
    rw [hW] at hg
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
    exact inpGlyph_ne_eos p
  have hxne : ∀ g ∈ (bx.map Glyph.bit).reverse, g ≠ Glyph.mk 0 := by
    rw [← List.map_reverse]; exact map_bit_ne bx.reverse 0
  have hyne : ∀ g ∈ (bY.map Glyph.bit).reverse, g ≠ Glyph.mk 1 := by
    rw [← List.map_reverse]; exact map_bit_ne bY.reverse 1
  have hzaccX : pushAcc inX W.reverse = (bx.map Glyph.bit).reverse := by
    rw [hW, ← hbx, ← hbY]
    exact pushAccBitsZipWithAll.1 bx bY
  have hzaccY : pushAcc inY W.reverse = (bY.map Glyph.bit).reverse := by
    rw [hW, ← hbx, ← hbY]
    exact pushAccBitsZipWithAll.2 bx bY
  -- step 1: marker mk 0 on stack 1
  set s1 : State := State.tPush (State.tSet s 5 (Glyph.mk 0)) 1 5 with hs1
  have hE1 : Eval main (pushConst 1 (Glyph.mk 0) 5) s s1 2 := by
    rw [hs1, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 (Glyph.mk 0) s)
      (Work.Kernel.eval_push main 1 5 (State.tSet s 5 (Glyph.mk 0)))
  have hs1_0 : s1.stk 0 = W := by rw [hs1, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe]; exact hsW
  have hs1_1 : s1.stk 1 = Glyph.mk 0 :: s.stk 1 := by
    rw [hs1, tPush_stk_same, tSet_reg_same, tSet_stk_pe]
  have hs1_k : ∀ k : Stk, k ≠ 1 → s1.stk k = s.stk k := by
    intro k hk; rw [hs1, tPush_stk_ne_pe _ _ hk, tSet_stk_pe]
  -- step 2: marker mk 1 on stack 2
  set s2 : State := State.tPush (State.tSet s1 5 (Glyph.mk 1)) 2 5 with hs2
  have hE2 : Eval main (pushConst 2 (Glyph.mk 1) 5) s1 s2 2 := by
    rw [hs2, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 (Glyph.mk 1) s1)
      (Work.Kernel.eval_push main 2 5 (State.tSet s1 5 (Glyph.mk 1)))
  have hs2_0 : s2.stk 0 = W := by
    rw [hs2, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs1_0]
  have hs2_1 : s2.stk 1 = Glyph.mk 0 :: s.stk 1 := by
    rw [hs2, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs1_1]
  have hs2_2 : s2.stk 2 = Glyph.mk 1 :: s.stk 2 := by
    rw [hs2, tPush_stk_same, tSet_reg_same, tSet_stk_pe, hs1_k 2 (by decide)]
  have hs2_k : ∀ k : Stk, k ≠ 1 → k ≠ 2 → s2.stk k = s.stk k := by
    intro k hk1 hk2
    rw [hs2, tPush_stk_ne_pe _ _ hk2, tSet_stk_pe, hs1_k k hk1]
  -- step 3: the splitting scan
  set s2e : State := State.tSet s2 5 Glyph.eos with hs2e
  have hE2e : Eval main (Cmd.set 5 Glyph.eos) s2 s2e 1 := by
    rw [hs2e]; exact Work.Kernel.eval_set main 5 Glyph.eos s2
  have hs2e_0 : s2e.stk 0 = W := by rw [hs2e, tSet_stk_pe, hs2_0]
  have hs2e_1 : s2e.stk 1 = Glyph.mk 0 :: s.stk 1 := by rw [hs2e, tSet_stk_pe, hs2_1]
  have hs2e_2 : s2e.stk 2 = Glyph.mk 1 :: s.stk 2 := by rw [hs2e, tSet_stk_pe, hs2_2]
  have hs2e_k : ∀ k : Stk, s2e.stk k = s2.stk k := fun k => tSet_stk_pe _ _ _ _
  have hs2e_reg : s2e.reg 5 = Glyph.eos := by rw [hs2e, tSet_reg_same]
  have hbranch : ∀ (g : Glyph) (Y : State), g ≠ Glyph.eos → Y.reg 5 = g →
      ∃ (Y' : State) (n : ℕ), n ≤ 13 ∧
        Eval main (Cmd.seq (splitCmd 5) (Cmd.set 5 Glyph.eos)) Y Y' n ∧
        Y'.stk 0 = Y.stk 0 ∧ Y'.stk 1 = inX g ++ Y.stk 1 ∧ Y'.stk 2 = inY g ++ Y.stk 2 ∧
        Y'.reg 5 = Glyph.eos ∧ (∀ j : Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → Y'.stk j = Y.stk j) := by
    intro g Y hg hreg
    obtain ⟨Y1, n1, hn1, hEv, hY1_0, hY1_1, hY1_2, hY1_k⟩ := splitGlyphEval main 5 Y g hreg
    refine ⟨State.tSet Y1 5 Glyph.eos, n1 + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Eval.seq hEv (Work.Kernel.eval_set main 5 Glyph.eos Y1)
    · rw [tSet_stk_pe]; exact hY1_0
    · rw [tSet_stk_pe]; exact hY1_1
    · rw [tSet_stk_pe]; exact hY1_2
    · rw [tSet_reg_same]
    · intro j hj0 hj1 hj2; rw [tSet_stk_pe]; exact hY1_k j hj0 hj1 hj2
  obtain ⟨s3, n3, hn3, hE3, hs3_0, hs3_1, hs3_2, hs3_reg, hs3_k⟩ :=
    splitLoopEval main 5 13 hbranch W [] s2e s2e hWne hs2e_0 hs2e_reg
      (by rw [pushAcc_nil]; rfl) (by rw [pushAcc_nil]; rfl) (fun j _ _ _ => rfl)
  have hs3_1' : s3.stk 1 = (bx.map Glyph.bit).reverse ++ (Glyph.mk 0 :: s.stk 1) := by
    rw [hs3_1, List.append_nil, hzaccX, hs2e_1]
  have hs3_2' : s3.stk 2 = (bY.map Glyph.bit).reverse ++ (Glyph.mk 1 :: s.stk 2) := by
    rw [hs3_2, List.append_nil, hzaccY, hs2e_2]
  have hs3_fr : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s3.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    rw [hs3_k k hk0 hk1 hk2, hs2e_k k, hs2_k k hk1 hk2]
  -- step 4: the terminator of `y` on stack 0
  set s4 : State := State.tPush (State.tSet s3 5 Glyph.iend) 0 5 with hs4
  have hE4 : Eval main (pushConst 0 Glyph.iend 5) s3 s4 2 := by
    rw [hs4, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 Glyph.iend s3)
      (Work.Kernel.eval_push main 0 5 (State.tSet s3 5 Glyph.iend))
  have hs4_0 : s4.stk 0 = [Glyph.iend] := by
    rw [hs4, tPush_stk_same, tSet_reg_same, tSet_stk_pe, hs3_0]
  have hs4_1 : s4.stk 1 = (bx.map Glyph.bit).reverse ++ (Glyph.mk 0 :: s.stk 1) := by
    rw [hs4, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs3_1']
  have hs4_2 : s4.stk 2 = (bY.map Glyph.bit).reverse ++ (Glyph.mk 1 :: s.stk 2) := by
    rw [hs4, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs3_2']
  have hs4_k : ∀ k : Stk, k ≠ 0 → s4.stk k = s3.stk k := by
    intro k hk; rw [hs4, tPush_stk_ne_pe _ _ hk, tSet_stk_pe]
  -- step 5: move the `y` bits onto stack 0
  obtain ⟨s5, n5, hn5, hE5, hs5_2, hs5_0, hs5_reg, hs5_k⟩ :=
    drainUntilEval main 2 0 (by decide) (Glyph.mk 1) 5 (bY.map Glyph.bit).reverse (s.stk 2) s4
      hyne hs4_2
  have hs5_0' : s5.stk 0 = bY.map Glyph.bit ++ [Glyph.iend] := by
    rw [hs5_0, List.reverse_reverse, hs4_0]
  have hs5_1 : s5.stk 1 = (bx.map Glyph.bit).reverse ++ (Glyph.mk 0 :: s.stk 1) := by
    rw [hs5_k 1 (by decide) (by decide), hs4_1]
  have hs5_k' : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s5.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    exact ((hs5_k k hk2 hk0).trans (hs4_k k hk0)).trans (hs3_fr k hk0 hk1 hk2)
  -- step 6/7: the sign of `y` and the terminator of `x`
  set s6 : State := State.tPush (State.tSet s5 5 Glyph.pos) 0 5 with hs6
  have hE6 : Eval main (pushConst 0 Glyph.pos 5) s5 s6 2 := by
    rw [hs6, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 Glyph.pos s5)
      (Work.Kernel.eval_push main 0 5 (State.tSet s5 5 Glyph.pos))
  have hs6_0 : s6.stk 0 = Glyph.pos :: (bY.map Glyph.bit ++ [Glyph.iend]) := by
    rw [hs6, tPush_stk_same, tSet_reg_same, tSet_stk_pe, hs5_0']
  have hs6_1 : s6.stk 1 = (bx.map Glyph.bit).reverse ++ (Glyph.mk 0 :: s.stk 1) := by
    rw [hs6, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs5_1]
  have hs6_2 : s6.stk 2 = s.stk 2 := by
    rw [hs6, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs5_2]
  have hs6_k : ∀ k : Stk, k ≠ 0 → s6.stk k = s5.stk k := by
    intro k hk; rw [hs6, tPush_stk_ne_pe _ _ hk, tSet_stk_pe]
  set s7 : State := State.tPush (State.tSet s6 5 Glyph.iend) 0 5 with hs7
  have hE7 : Eval main (pushConst 0 Glyph.iend 5) s6 s7 2 := by
    rw [hs7, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 Glyph.iend s6)
      (Work.Kernel.eval_push main 0 5 (State.tSet s6 5 Glyph.iend))
  have hs7_0 : s7.stk 0 = Glyph.iend :: Glyph.pos :: (bY.map Glyph.bit ++ [Glyph.iend]) := by
    rw [hs7, tPush_stk_same, tSet_reg_same, tSet_stk_pe, hs6_0]
  have hs7_1 : s7.stk 1 = (bx.map Glyph.bit).reverse ++ (Glyph.mk 0 :: s.stk 1) := by
    rw [hs7, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs6_1]
  have hs7_2 : s7.stk 2 = s.stk 2 := by
    rw [hs7, tPush_stk_ne_pe _ _ (by decide), tSet_stk_pe, hs6_2]
  have hs7_k : ∀ k : Stk, k ≠ 0 → s7.stk k = s6.stk k := by
    intro k hk; rw [hs7, tPush_stk_ne_pe _ _ hk, tSet_stk_pe]
  -- step 8: move the `x` bits onto stack 0
  obtain ⟨s8, n8, hn8, hE8, hs8_1, hs8_0, hs8_reg, hs8_k⟩ :=
    drainUntilEval main 1 0 (by decide) (Glyph.mk 0) 5 (bx.map Glyph.bit).reverse (s.stk 1) s7
      hxne hs7_1
  have hs8_0' : s8.stk 0 =
      bx.map Glyph.bit ++ (Glyph.iend :: Glyph.pos :: (bY.map Glyph.bit ++ [Glyph.iend])) := by
    rw [hs8_0, List.reverse_reverse, hs7_0]
  have hs8_2 : s8.stk 2 = s.stk 2 := by
    rw [hs8_k 2 (by decide) (by decide), hs7_2]
  have hs8_k' : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → s8.stk k = s.stk k := by
    intro k hk0 hk1 hk2
    exact ((((hs8_k k hk1 hk0).trans (hs7_k k hk0)).trans (hs6_k k hk0)).trans
      (hs5_k' k hk0 hk1 hk2))
  -- step 9: the sign of `x`
  set s9 : State := State.tPush (State.tSet s8 5 Glyph.pos) 0 5 with hs9
  have hE9 : Eval main (pushConst 0 Glyph.pos 5) s8 s9 2 := by
    rw [hs9, pushConst]
    exact Eval.seq (Work.Kernel.eval_set main 5 Glyph.pos s8)
      (Work.Kernel.eval_push main 0 5 (State.tSet s8 5 Glyph.pos))
  have hs9_0 : s9.stk 0 = encs [Val.int (x : ℤ), Val.int (y : ℤ)] := by
    rw [hs9, tPush_stk_same, tSet_reg_same, tSet_stk_pe, hs8_0']
    simp [encs, enc_int_natCast, ← hbx, ← hbY, List.append_assoc]
  have hs9_k : ∀ k : Stk, k ≠ 0 → s9.stk k = s.stk k := by
    intro k hk0
    rw [hs9, tPush_stk_ne_pe _ _ hk0, tSet_stk_pe]
    by_cases hk1 : k = 1
    · subst hk1; exact hs8_1
    · by_cases hk2 : k = 2
      · subst hk2; exact hs8_2
      · exact hs8_k' k hk0 hk1 hk2
  -- assembly
  refine ⟨s9, 2 + (2 + ((1 + n3) + (2 + (n5 + (2 + (2 + (n8 + 2))))))), ?_, ?_, hs9_0, hs9_k⟩
  · rw [parseProg, splitAll]
    exact Eval.seq hE1 (Eval.seq hE2 (Eval.seq (Eval.seq hE2e hE3) (Eval.seq hE4 (Eval.seq hE5
      (Eval.seq hE6 (Eval.seq hE7 (Eval.seq hE8 hE9)))))))
  -- cost
  have hL : W.length = max x.size y.size := by
    rw [hW, List.length_map, zipWithAll_length, encodeNat_length, encodeNat_length]
  have hn3' : n3 ≤ 17 * W.length + 18 := by omega
  have hxlen : (bx.map Glyph.bit).reverse.length = x.size := by
    rw [List.length_reverse, List.length_map, hbx, encodeNat_length]
  have hylen : (bY.map Glyph.bit).reverse.length = y.size := by
    rw [List.length_reverse, List.length_map, hbY, encodeNat_length]
  have hn5' : n5 ≤ 5 * y.size + 6 := by rw [hylen] at hn5; omega
  have hn8' : n8 ≤ 5 * x.size + 6 := by rw [hxlen] at hn8; omega
  have hxs : x.size ≤ W.length := by rw [hL]; exact le_max_left _ _
  have hys : y.size ≤ W.length := by rw [hL]; exact le_max_right _ _
  have hgoal : (IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat
      (x, y)).length = W.length := by
    rw [hW, IntegerMultiplication.encodeProd, List.length_map]
  rw [hgoal]
  omega


/-! ## The target lemma -/

theorem parseEmitWord : (∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (x y : ℕ) (s : HvdH.State), s.stk 0 = (IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat (x, y)).map HvdH.inpGlyph → ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main prog s s' n ∧ n ≤ K * ((IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat (x, y)).length + 1) ∧ s'.stk 0 = HvdH.encs [HvdH.Val.int x, HvdH.Val.int y] ∧ ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = s.stk k) ∧ (∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (z : ℕ) (s : HvdH.State), s.stk 0 = (HvdH.Val.int z).enc → s.stk 1 = [] → ∃ (s' : HvdH.State) (n : ℕ), HvdH.Eval main prog s s' n ∧ n ≤ K * (z.size + 1) ∧ s'.stk 0 = [] ∧ s'.stk 1 = (Computability.encodeNat z).map HvdH.Glyph.bit ∧ ∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  refine ⟨⟨parseProg, 100, fun main x y s h => parseEval main x y s h⟩,
    ⟨emitProg, 21, fun main z s h0 h1 => emitEval main z s h0 h1⟩⟩

end Work.IntLib
