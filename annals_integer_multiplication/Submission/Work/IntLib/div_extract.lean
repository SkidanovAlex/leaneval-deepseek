import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.padBitsAPI
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.mvRevOntoTight

/-!
# `Work.IntLib.div_extract`

Evaluation of `Work.IntLib.Div.extract`, the extraction phase of the long-division core: it peels
the two integer values off stack 0 (sign glyphs to stack 9, dividend bits reversed to stack 1,
divisor bits to stack 8 and then reversed onto stack 2, `|b|+1` zero bits to stack 3) and leaves
stack 0 holding the raw remainder `R`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib

open HvdH

/-! ## Small list facts -/

theorem de_bitsG_append (l₁ l₂ : List Bool) : bitsG (l₁ ++ l₂) = bitsG l₁ ++ bitsG l₂ := by
  simp [bitsG, List.map_append]

theorem de_bitsG_reverse (l : List Bool) : (bitsG l).reverse = bitsG l.reverse :=
  (List.map_reverse).symm

theorem de_bitsG_singleton (b : Bool) : bitsG [b] = [Glyph.bit b] := rfl

theorem de_bitsG_length (l : List Bool) : (bitsG l).length = l.length := by
  simp [bitsG]

theorem de_padBits_size (n : ℕ) : padBits n n.size = n.bits := by
  have h := padBits_ofBits n.bits
  rw [ofBits_bits, Nat.size_eq_bits_len] at h
  exact h

theorem de_padBits_succ_size (n : ℕ) : padBits n (n.size + 1) = n.bits ++ [false] := by
  have hr : padBits n (n.size + 1) = padBits n n.size ++ [n.testBit n.size] := by
    simp only [padBits, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [hr, de_padBits_size, Nat.testBit_lt_two_pow (Nat.size_le.mp (le_refl n.size))]

theorem de_padBits_zero (L : ℕ) : padBits 0 L = List.replicate L false := by
  simp [padBits, List.map_const']

theorem de_bitsG_padBits_zero (L : ℕ) :
    bitsG (padBits 0 L) = List.replicate L (Glyph.bit false) := by
  rw [de_padBits_zero]
  simp [bitsG, List.map_replicate]

/-! ## State bookkeeping for the canonical intermediate states -/

theorem de_tPop_stk_self (s : HvdH.State) (k : HvdH.Stk) (r : HvdH.Reg) :
    (State.tPop s k r).stk k = (s.stk k).tail := by
  simp [State.tPop, State.updStk, State.updReg, Function.update_self]

theorem de_tPop_stk_of_ne (s : HvdH.State) (k : HvdH.Stk) (r : HvdH.Reg) (j : HvdH.Stk)
    (h : j ≠ k) : (State.tPop s k r).stk j = s.stk j := by
  simp [State.tPop, State.updStk, State.updReg, Function.update_of_ne h]

theorem de_tPop_reg_self (s : HvdH.State) (k : HvdH.Stk) (r : HvdH.Reg) :
    (State.tPop s k r).reg r = (s.stk k).headD Glyph.eos := by
  simp [State.tPop, State.updStk, State.updReg, Function.update_self]

theorem de_tPush_stk_self (s : HvdH.State) (k : HvdH.Stk) (r : HvdH.Reg) :
    (State.tPush s k r).stk k = s.reg r :: s.stk k := by
  simp [State.tPush, State.updStk, Function.update_self]

theorem de_tPush_stk_of_ne (s : HvdH.State) (k : HvdH.Stk) (r : HvdH.Reg) (j : HvdH.Stk)
    (h : j ≠ k) : (State.tPush s k r).stk j = s.stk j := by
  simp [State.tPush, State.updStk, Function.update_of_ne h]

theorem de_tPush_reg (s : HvdH.State) (k : HvdH.Stk) (r r' : HvdH.Reg) :
    (State.tPush s k r).reg r' = s.reg r' := rfl

theorem de_tSet_stk (s : HvdH.State) (r : HvdH.Reg) (c : HvdH.Glyph) (j : HvdH.Stk) :
    (State.tSet s r c).stk j = s.stk j := rfl

theorem de_tSet_reg_self (s : HvdH.State) (r : HvdH.Reg) (c : HvdH.Glyph) :
    (State.tSet s r c).reg r = c := by
  simp [State.tSet, State.updReg, Function.update_self]

theorem de_tSet_reg_of_ne (s : HvdH.State) (r r' : HvdH.Reg) (c : HvdH.Glyph) (h : r' ≠ r) :
    (State.tSet s r c).reg r' = s.reg r' := by
  simp [State.tSet, State.updReg, Function.update_of_ne h]

/-! ## The bit-consuming loop of `Div.extract`

`Div.extractBHandler` pushes the glyph just popped onto stack `stX` and a `false` bit onto stack
`stR`; the loop below is the generic version of that behaviour (push the popped glyph on `k'`,
push the constant `c` on `k''`).
-/

theorem consumeLoop_push_push (main : HvdH.Cmd) (k k' k'' : HvdH.Stk) (T c : HvdH.Glyph)
    (r rs : HvdH.Reg) (hne1 : k ≠ k') (hne2 : k ≠ k'') (hne12 : k' ≠ k'')
    (bk bk' bk'' l : List HvdH.Glyph) (hT : ∀ g ∈ l, g ≠ T) :
    ∀ (pre gs : List HvdH.Glyph) (s : HvdH.State), l = pre ++ gs →
      s.stk k = gs ++ T :: bk → s.stk k' = pre.reverse ++ bk' →
      s.stk k'' = List.replicate pre.length c ++ bk'' → s.reg r = HvdH.Glyph.eos →
      ∃ s' n, HvdH.Eval main (consumeLoop k T r
          (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])) s s' n ∧
        s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
        s'.stk k'' = List.replicate l.length c ++ bk'' ∧ s'.reg r ≠ HvdH.Glyph.eos ∧
        n ≤ 8 * gs.length + 6 ∧
        ∀ j : HvdH.Stk, j ≠ k → j ≠ k' → j ≠ k'' → s'.stk j = s.stk j := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    intro s hl hk hk' hk'' hr
    have hl' : l = pre := by rw [hl, List.append_nil]
    set s1 : State := State.tPop s k r with hs1
    set s2 : State := State.tPush s1 k r with hs2
    set s3 : State := State.tSet s2 r (Glyph.mk 0) with hs3
    have hs1reg : s1.reg r = T := by simp [hs1, State.tPop, hk]
    have e1 : Eval main (.pop k r) s s1 1 := by rw [hs1]; exact Work.Kernel.eval_pop main k r s
    have e2 : Eval main (.push k r) s1 s2 1 := by rw [hs2]; exact Work.Kernel.eval_push main k r s1
    have e3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      rw [hs3]; exact Work.Kernel.eval_set main r (Glyph.mk 0) s2
    have h23 : Eval main (.seq (.push k r) (.set r (Glyph.mk 0))) s1 s3 2 := Eval.seq e2 e3
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])
          (.set r .eos))) s1 s3 3 := Eval.iteT hs1reg h23
    have h3reg : s3.reg r = Glyph.mk 0 := by simp [hs3, State.tSet]
    have hexit : s3.reg r ≠ Glyph.eos := by rw [h3reg]; decide
    have hbody : Eval main (consumeStep k T r
        (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])) s s3 4 :=
      Eval.seq e1 hite
    have hloopF : Eval main (consumeLoop k T r
        (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])) s3 s3 1 :=
      Eval.loopF hexit
    have hmain : Eval main (consumeLoop k T r
        (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])) s s3 6 :=
      Eval.loopT hr hbody hloopF
    refine ⟨s3, 6, hmain, ?_, ?_, ?_, hexit, by simp, ?_⟩
    · simp [hs3, hs2, hs1, State.tPop, State.tPush, State.tSet, hk]
    · rw [hl']; simp [hs3, hs2, hs1, State.tPop, State.tPush, State.tSet, hk',
        Ne.symm hne1]
    · rw [hl']; simp [hs3, hs2, hs1, State.tPop, State.tPush, State.tSet, hk'',
        Ne.symm hne2]
    · intro j hj1 hj2 hj3
      simp [hs3, hs2, hs1, State.tPop, State.tPush, State.tSet, hj1, hj2, hj3]
  | cons g gs' ih =>
    intro s hl hk hk' hk'' hr
    have hg : g ≠ T := hT g (by rw [hl]; simp)
    have hl' : l = (pre ++ [g]) ++ gs' := by rw [hl, List.append_assoc]; simp
    set s1 : State := State.tPop s k r with hs1
    set s2 : State := State.tPush s1 k' r with hs2
    set s3 : State := State.tSet s2 rs c with hs3
    set s4 : State := State.tPush s3 k'' rs with hs4
    set s5 : State := State.tSet s4 r Glyph.eos with hs5
    have hs1reg : s1.reg r = g := by simp [hs1, State.tPop, hk]
    have hs1stk : s1.stk k = gs' ++ T :: bk := by simp [hs1, State.tPop, hk]
    have hs1stk' : s1.stk k' = pre.reverse ++ bk' := by
      simp [hs1, State.tPop, hk', Ne.symm hne1]
    have hs1stk'' : s1.stk k'' = List.replicate pre.length c ++ bk'' := by
      simp [hs1, State.tPop, hk'', Ne.symm hne2]
    have e1 : Eval main (.pop k r) s s1 1 := by rw [hs1]; exact Work.Kernel.eval_pop main k r s
    have e2 : Eval main (.push k' r) s1 s2 1 := by rw [hs2]; exact Work.Kernel.eval_push main k' r s1
    have e3 : Eval main (.set rs c) s2 s3 1 := by rw [hs3]; exact Work.Kernel.eval_set main rs c s2
    have e4 : Eval main (.push k'' rs) s3 s4 1 := by
      rw [hs4]; exact Work.Kernel.eval_push main k'' rs s3
    have e5 : Eval main (.skip : HvdH.Cmd) s4 s4 1 := Eval.skip s4
    have hH : Eval main (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])
        s1 s4 4 := Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))
    have hne : s1.reg r ≠ T := by rw [hs1reg]; exact hg
    have e6 : Eval main (.set r Glyph.eos) s4 s5 1 := by
      rw [hs5]; exact Work.Kernel.eval_set main r Glyph.eos s4
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])
          (.set r .eos))) s1 s5 6 := Eval.iteF hne (Eval.seq hH e6)
    have hbody : Eval main (consumeStep k T r
        (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs])) s s5 7 :=
      Eval.seq e1 hite
    have hs5k : s5.stk k = gs' ++ T :: bk := by
      simp [hs5, hs4, hs3, hs2, State.tPush, State.tSet, hs1stk, hne1, hne2]
    have hs5k' : s5.stk k' = (pre ++ [g]).reverse ++ bk' := by
      rw [hs5, de_tSet_stk, hs4, de_tPush_stk_of_ne s3 k'' rs k' hne12, hs3, de_tSet_stk,
        hs2, de_tPush_stk_self, hs1reg, hs1stk', List.reverse_append]
      simp
    have hs5k'' : s5.stk k'' = List.replicate (pre ++ [g]).length c ++ bk'' := by
      rw [hs5, de_tSet_stk, hs4, de_tPush_stk_self, hs3, de_tSet_reg_self, de_tSet_stk,
        hs2, de_tPush_stk_of_ne s1 k' r k'' (Ne.symm hne12), hs1stk'']
      simp [List.replicate_succ]
    have hs5reg : s5.reg r = Glyph.eos := by simp [hs5, State.tSet]
    obtain ⟨s', n', hev', hk_, hk'_, hk''_, hr_, hn_, hfr_⟩ :=
      ih (pre ++ [g]) s5 hl' hs5k hs5k' hs5k'' hs5reg
    have hmain : Eval main (consumeLoop k T r
        (Div.seqs [HvdH.Cmd.push k' r, HvdH.Cmd.set rs c, HvdH.Cmd.push k'' rs]))
        s s' (7 + n' + 1) := Eval.loopT hr hbody hev'
    refine ⟨s', 7 + n' + 1, hmain, hk_, hk'_, hk''_, hr_, ?_, ?_⟩
    · rw [List.length_cons]
      omega
    · intro j hj1 hj2 hj3
      rw [hfr_ j hj1 hj2 hj3]
      simp [hs5, hs4, hs3, hs2, hs1, State.tPop, State.tPush, State.tSet, hj1, hj2, hj3]

/-- `Work.IntLib.consume 0 iend rLoop Div.extractBHandler` (the divisor-bit extraction loop of
`Div.extract`). -/
theorem consumeBitsExtract_ev (main : HvdH.Cmd) (s : HvdH.State)
    (l bk bk' bk'' : List HvdH.Glyph)
    (h0 : s.stk 0 = l ++ HvdH.Glyph.iend :: bk)
    (hX : s.stk Div.stX = bk') (hR : s.stk Div.stR = bk'')
    (hT : ∀ g ∈ l, g ≠ HvdH.Glyph.iend) :
    ∃ s' n, HvdH.Eval main (consume 0 HvdH.Glyph.iend rLoop Div.extractBHandler) s s' n ∧
      n ≤ 8 * l.length + 7 ∧
      s'.stk 0 = HvdH.Glyph.iend :: bk ∧ s'.stk Div.stX = l.reverse ++ bk' ∧
      s'.stk Div.stR = List.replicate l.length (HvdH.Glyph.bit false) ++ bk'' ∧
      ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stX → j ≠ Div.stR → s'.stk j = s.stk j := by
  have hne1 : (0 : HvdH.Stk) ≠ Div.stX := by decide
  have hne2 : (0 : HvdH.Stk) ≠ Div.stR := by decide
  have hne12 : Div.stX ≠ Div.stR := by decide
  set s1 : State := State.tSet s rLoop Glyph.eos with hs1
  have hs1r : s1.reg rLoop = Glyph.eos := by rw [hs1, de_tSet_reg_self]
  have hs10 : s1.stk 0 = l ++ Glyph.iend :: bk := by rw [hs1, de_tSet_stk, h0]
  have hs1X : s1.stk Div.stX = bk' := by rw [hs1, de_tSet_stk, hX]
  have hs1R : s1.stk Div.stR = bk'' := by rw [hs1, de_tSet_stk, hR]
  obtain ⟨s2, n2, hev2, hk2, hk2', hk2'', hr2, hn2, hfr2⟩ :=
    consumeLoop_push_push main 0 Div.stX Div.stR Glyph.iend (Glyph.bit false) rLoop Div.rgS
      hne1 hne2 hne12 bk bk' bk'' l hT [] l s1 rfl hs10 hs1X hs1R hs1r
  refine ⟨s2, 1 + n2, ?_, by omega, hk2, hk2', hk2'', ?_⟩
  · rw [show Work.IntLib.consume 0 Glyph.iend rLoop Div.extractBHandler =
        Cmd.seq (Cmd.set rLoop Glyph.eos)
          (Work.IntLib.consumeLoop 0 Glyph.iend rLoop
            (Div.seqs [HvdH.Cmd.push Div.stX rLoop, HvdH.Cmd.set Div.rgS (Glyph.bit false),
              HvdH.Cmd.push Div.stR Div.rgS])) from rfl]
    exact Eval.seq (by rw [hs1]; exact Work.Kernel.eval_set main rLoop Glyph.eos s) hev2
  · intro j hj0 hjX hjR
    rw [hfr2 j hj0 hjX hjR, hs1, de_tSet_stk]

/-- The last two commands of `Div.extract`: the (reversed) contents of stack `stX` are reversed
onto stack `stB` and the empty marker of `stX` is restored. -/
theorem extractFinishEval (main : HvdH.Cmd) (Bb bkX bkB : List HvdH.Glyph) (s : HvdH.State)
    (hX : s.stk Div.stX = Bb ++ [gX] ++ bkX)
    (hB : s.stk Div.stB = [gB] ++ bkB)
    (hT : ∀ g ∈ Bb, g ≠ gX) :
    ∃ s' n, HvdH.Eval main
        (Div.seqs [mvRevOnto Div.stX gX Div.stB Div.rgT, Div.mkG Div.stX gX]) s s' n ∧
      n ≤ 5 * Bb.length + 12 ∧
      s'.stk Div.stX = [gX] ++ bkX ∧
      s'.stk Div.stB = Bb.reverse ++ [gB] ++ bkB ∧
      (∀ j : HvdH.Stk, j ≠ Div.stX → j ≠ Div.stB → s'.stk j = s.stk j) := by
  have hne : Div.stX ≠ Div.stB := by decide
  have hX' : s.stk Div.stX = Bb ++ gX :: bkX := by
    rw [hX, List.append_assoc, List.singleton_append]
  obtain ⟨s1, n1, hev1, hn1, h1X, h1B, hfr1⟩ :=
    mvRevOntoTight main Div.stX gX Div.stB Div.rgT Bb bkX ([gB] ++ bkB) s hT hX' hB hne
  set s2 : State := State.tSet s1 Div.rgT gX with hs2
  set s3 : State := State.tPush s2 Div.stX Div.rgT with hs3
  have hs2r : s2.reg Div.rgT = gX := by rw [hs2, de_tSet_reg_self]
  have e2 : Eval main (.set Div.rgT gX) s1 s2 1 := by
    rw [hs2]; exact Work.Kernel.eval_set main Div.rgT gX s1
  have e3 : Eval main (.push Div.stX Div.rgT) s2 s3 1 := by
    rw [hs3]; exact Work.Kernel.eval_push main Div.stX Div.rgT s2
  have e4 : Eval main (.skip : HvdH.Cmd) s3 s3 1 := Eval.skip s3
  refine ⟨s3, n1 + ((1 + 1) + 1),
    Eval.seq hev1 (Eval.seq (Eval.seq e2 e3) e4), by omega, ?_, ?_, ?_⟩
  · rw [hs3, de_tPush_stk_self, hs2r, hs2, de_tSet_stk, h1X, List.singleton_append]
  · rw [hs3, de_tPush_stk_of_ne s2 Div.stX Div.rgT Div.stB (by decide), hs2, de_tSet_stk, h1B,
      List.append_assoc]
  · intro j hjX hjB
    rw [hs3, de_tPush_stk_of_ne s2 Div.stX Div.rgT j hjX, hs2, de_tSet_stk]
    exact hfr1 j hjX hjB

theorem div_extract (main : HvdH.Cmd) (b0 : HvdH.State) (a b : ℤ) (R : List HvdH.Glyph)
    (hb : b ≠ 0) (S : HvdH.State)
    (h0 : S.stk 0 = (HvdH.Val.int a).enc ++ (HvdH.Val.int b).enc ++ R)
    (hP : S.stk Work.IntLib.Div.stP = [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP)
    (hB : S.stk Work.IntLib.Div.stB = [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
    (hR : S.stk Work.IntLib.Div.stR = [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hQ : S.stk Work.IntLib.Div.stQ = [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ)
    (hS5 : S.stk Work.IntLib.Div.stS = [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
    (hS6 : S.stk Work.IntLib.Div.stC = [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
    (hS7 : S.stk Work.IntLib.Div.stD = [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD)
    (hS8 : S.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hS9 : S.stk Work.IntLib.Div.stY = [Work.IntLib.gY] ++ b0.stk Work.IntLib.Div.stY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → S.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.extract S s' n ∧
      n ≤ 40 * (HvdH.isz a + HvdH.isz b + 1) ∧
      s'.stk 0 = R ∧
      s'.stk Work.IntLib.Div.stP = Work.IntLib.bitsG a.natAbs.bits.reverse ++ [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP ∧
      s'.stk Work.IntLib.Div.stB = Work.IntLib.bitsG (Work.IntLib.padBits b.natAbs (b.natAbs.size + 1)) ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB ∧
      s'.stk Work.IntLib.Div.stR = Work.IntLib.bitsG (Work.IntLib.padBits 0 (b.natAbs.size + 1)) ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR ∧
      s'.stk Work.IntLib.Div.stQ = [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ ∧
      s'.stk Work.IntLib.Div.stS = [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS ∧
      s'.stk Work.IntLib.Div.stC = [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC ∧
      s'.stk Work.IntLib.Div.stD = [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD ∧
      s'.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX ∧
      s'.stk Work.IntLib.Div.stY = [if b < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos, if a < 0 then HvdH.Glyph.neg else HvdH.Glyph.pos] ++ [Work.IntLib.gY] ++ b0.stk Work.IntLib.Div.stY ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.Div.stP → j ≠ Work.IntLib.Div.stB →
        j ≠ Work.IntLib.Div.stR → j ≠ Work.IntLib.Div.stQ → j ≠ Work.IntLib.Div.stS →
        j ≠ Work.IntLib.Div.stC → j ≠ Work.IntLib.Div.stD → j ≠ Work.IntLib.Div.stX →
        j ≠ Work.IntLib.Div.stY → s'.stk j = S.stk j) := by
  set sa : Glyph := (if a < 0 then Glyph.neg else Glyph.pos) with hsa
  set sb : Glyph := (if b < 0 then Glyph.neg else Glyph.pos) with hsb
  have hS0 : S.stk 0 = sa :: (bitsG a.natAbs.bits ++ Glyph.iend :: sb ::
      (bitsG b.natAbs.bits ++ Glyph.iend :: R)) := by
    rw [h0]
    simp only [enc_int, encodeNat_eq_bits, List.cons_append, List.nil_append, List.append_assoc,
      ← hsa, ← hsb]
  -- step 1: pop the sign of `a`; step 2: push it on stack 9
  set t1 : State := State.tPop S 0 Div.rgT with ht1
  set t2 : State := State.tPush t1 Div.stY Div.rgT with ht2
  have ht1reg : t1.reg Div.rgT = sa := by
    rw [ht1]
    have h := de_tPop_reg_self S 0 Div.rgT
    rw [hS0] at h
    rw [h, List.headD_cons]
  have hev1 : Eval main (.pop 0 Div.rgT) S t1 1 := by
    rw [ht1]; exact Work.Kernel.eval_pop main 0 Div.rgT S
  have hev2 : Eval main (.push Div.stY Div.rgT) t1 t2 1 := by
    rw [ht2]; exact Work.Kernel.eval_push main Div.stY Div.rgT t1
  have ht2stk0 : t2.stk 0 = bitsG a.natAbs.bits ++ Glyph.iend :: sb ::
      (bitsG b.natAbs.bits ++ Glyph.iend :: R) := by
    rw [ht2, de_tPush_stk_of_ne t1 Div.stY Div.rgT 0 (by decide), ht1, de_tPop_stk_self, hS0,
      List.tail_cons]
  have ht2stkY : t2.stk Div.stY = sa :: S.stk Div.stY := by
    rw [ht2, de_tPush_stk_self, ht1reg, ht1,
      de_tPop_stk_of_ne S 0 Div.rgT Div.stY (by decide)]
  have ht2frame : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stY → t2.stk j = S.stk j := by
    intro j hj0 hjY
    rw [ht2, de_tPush_stk_of_ne t1 Div.stY Div.rgT j hjY, ht1,
      de_tPop_stk_of_ne S 0 Div.rgT j hj0]
  -- step 3: consume the bits of `a` onto stack 1
  have hTA : ∀ g ∈ bitsG a.natAbs.bits, g ≠ Glyph.iend := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg
    exact fun h => nomatch h
  have ht2P : t2.stk Div.stP = [gP] ++ b0.stk Div.stP := by
    rw [ht2frame Div.stP (by decide) (by decide)]
    exact hP
  obtain ⟨u2, m2, hev3, hm2, hu2_0, hu2_P, hu2fr⟩ :=
    consume_push_rev main 0 Glyph.iend Div.stP rLoop (bitsG a.natAbs.bits)
      (sb :: (bitsG b.natAbs.bits ++ Glyph.iend :: R)) ([gP] ++ b0.stk Div.stP)
      (by decide) hTA t2 ht2stk0 ht2P
  -- steps 4-6: pop the `iend` of `a`, pop the sign of `b`, push it on stack 9
  set w1 : State := State.tPop u2 0 rLoop with hw1
  set w2 : State := State.tPop w1 0 Div.rgT with hw2
  set w3 : State := State.tPush w2 Div.stY Div.rgT with hw3
  have hev4 : Eval main (.pop 0 rLoop) u2 w1 1 := by
    rw [hw1]; exact Work.Kernel.eval_pop main 0 rLoop u2
  have hev5 : Eval main (.pop 0 Div.rgT) w1 w2 1 := by
    rw [hw2]; exact Work.Kernel.eval_pop main 0 Div.rgT w1
  have hev6 : Eval main (.push Div.stY Div.rgT) w2 w3 1 := by
    rw [hw3]; exact Work.Kernel.eval_push main Div.stY Div.rgT w2
  have hw2reg : w2.reg Div.rgT = sb := by
    rw [hw2]
    have h := de_tPop_reg_self w1 0 Div.rgT
    rw [hw1] at h
    rw [de_tPop_stk_self] at h
    rw [hu2_0, List.tail_cons] at h
    rw [h, List.headD_cons]
  have hw3stk0 : w3.stk 0 = bitsG b.natAbs.bits ++ Glyph.iend :: R := by
    rw [hw3, de_tPush_stk_of_ne w2 Div.stY Div.rgT 0 (by decide), hw2, de_tPop_stk_self, hw1,
      de_tPop_stk_self, hu2_0, List.tail_cons, List.tail_cons]
  have hw3stkY : w3.stk Div.stY = sb :: u2.stk Div.stY := by
    rw [hw3, de_tPush_stk_self, hw2reg, hw2,
      de_tPop_stk_of_ne w1 0 Div.rgT Div.stY (by decide), hw1,
      de_tPop_stk_of_ne u2 0 rLoop Div.stY (by decide)]
  have hw3frame : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stY → w3.stk j = u2.stk j := by
    intro j hj0 hjY
    rw [hw3, de_tPush_stk_of_ne w2 Div.stY Div.rgT j hjY, hw2,
      de_tPop_stk_of_ne w1 0 Div.rgT j hj0, hw1, de_tPop_stk_of_ne u2 0 rLoop j hj0]
  -- step 7: consume the bits of `b`
  have hTB : ∀ g ∈ bitsG b.natAbs.bits, g ≠ Glyph.iend := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg
    exact fun h => nomatch h
  have hw3X : w3.stk Div.stX = [gX] ++ b0.stk Div.stX := by
    rw [hw3frame Div.stX (by decide) (by decide), hu2fr Div.stX (by decide) (by decide),
      ht2frame Div.stX (by decide) (by decide), hS8]
  have hw3R : w3.stk Div.stR = [gR] ++ b0.stk Div.stR := by
    rw [hw3frame Div.stR (by decide) (by decide), hu2fr Div.stR (by decide) (by decide),
      ht2frame Div.stR (by decide) (by decide), hR]
  obtain ⟨u4, m4, hev7, hm4, hu4_0, hu4_X, hu4_R, hu4fr⟩ :=
    consumeBitsExtract_ev main w3 (bitsG b.natAbs.bits) R ([gX] ++ b0.stk Div.stX)
      ([gR] ++ b0.stk Div.stR) hw3stk0 hw3X hw3R hTB
  -- steps 8-12: pop the `iend` of `b`, push the padding zero on stack 3 and on stack 8
  set v1 : State := State.tPop u4 0 rLoop with hv1
  set v2 : State := State.tSet v1 Div.rgS (Glyph.bit false) with hv2
  set v3 : State := State.tPush v2 Div.stR Div.rgS with hv3
  set v4 : State := State.tSet v3 Div.rgS (Glyph.bit false) with hv4
  set v5 : State := State.tPush v4 Div.stX Div.rgS with hv5
  have hev8 : Eval main (.pop 0 rLoop) u4 v1 1 := by
    rw [hv1]; exact Work.Kernel.eval_pop main 0 rLoop u4
  have hev9 : Eval main (.set Div.rgS (Glyph.bit false)) v1 v2 1 := by
    rw [hv2]; exact Work.Kernel.eval_set main Div.rgS (Glyph.bit false) v1
  have hev10 : Eval main (.push Div.stR Div.rgS) v2 v3 1 := by
    rw [hv3]; exact Work.Kernel.eval_push main Div.stR Div.rgS v2
  have hev11 : Eval main (.set Div.rgS (Glyph.bit false)) v3 v4 1 := by
    rw [hv4]; exact Work.Kernel.eval_set main Div.rgS (Glyph.bit false) v3
  have hev12 : Eval main (.push Div.stX Div.rgS) v4 v5 1 := by
    rw [hv5]; exact Work.Kernel.eval_push main Div.stX Div.rgS v4
  have hv1stk0 : v1.stk 0 = R := by rw [hv1, de_tPop_stk_self, hu4_0, List.tail_cons]
  have hv5stk0 : v5.stk 0 = R := by
    rw [hv5, de_tPush_stk_of_ne v4 Div.stX Div.rgS 0 (by decide), hv4, de_tSet_stk, hv3,
      de_tPush_stk_of_ne v2 Div.stR Div.rgS 0 (by decide), hv2, de_tSet_stk, hv1stk0]
  have hv5stkR : v5.stk Div.stR =
      List.replicate (b.natAbs.size + 1) (Glyph.bit false) ++ [gR] ++ b0.stk Div.stR := by
    rw [hv5, de_tPush_stk_of_ne v4 Div.stX Div.rgS Div.stR (by decide), hv4, de_tSet_stk, hv3,
      de_tPush_stk_self, hv2, de_tSet_reg_self, de_tSet_stk, hv1,
      de_tPop_stk_of_ne u4 0 rLoop Div.stR (by decide), hu4_R, de_bitsG_length,
      Nat.size_eq_bits_len]
    simp [List.replicate_succ, List.cons_append]
  have hv5stkX : v5.stk Div.stX =
      (Glyph.bit false :: (bitsG b.natAbs.bits).reverse) ++ [gX] ++ b0.stk Div.stX := by
    rw [hv5, de_tPush_stk_self, hv4, de_tSet_reg_self, de_tSet_stk, hv3,
      de_tPush_stk_of_ne v2 Div.stR Div.rgS Div.stX (by decide), hv2, de_tSet_stk, hv1,
      de_tPop_stk_of_ne u4 0 rLoop Div.stX (by decide), hu4_X]
    simp [List.cons_append, List.append_assoc]
  have hv5fr : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stR → j ≠ Div.stX → v5.stk j = u4.stk j := by
    intro j hj0 hjR hjX
    rw [hv5, de_tPush_stk_of_ne v4 Div.stX Div.rgS j hjX, hv4, de_tSet_stk, hv3,
      de_tPush_stk_of_ne v2 Div.stR Div.rgS j hjR, hv2, de_tSet_stk, hv1,
      de_tPop_stk_of_ne u4 0 rLoop j hj0]
  have hv5B : v5.stk Div.stB = [gB] ++ b0.stk Div.stB := by
    rw [hv5fr Div.stB (by decide) (by decide) (by decide),
      hu4fr Div.stB (by decide) (by decide) (by decide),
      hw3frame Div.stB (by decide) (by decide), hu2fr Div.stB (by decide) (by decide),
      ht2frame Div.stB (by decide) (by decide)]
    exact hB
  -- the tail of the program
  have hTBb : ∀ g ∈ Glyph.bit false :: (bitsG b.natAbs.bits).reverse, g ≠ gX := by
    intro g hg
    rw [List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact fun h => nomatch h
    · rw [List.mem_reverse] at hg
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg
      exact fun h => nomatch h
  obtain ⟨z6, m6, hevT, hm6, hz6X, hz6B, hz6fr⟩ :=
    extractFinishEval main (Glyph.bit false :: (bitsG b.natAbs.bits).reverse) (b0.stk Div.stX)
      (b0.stk Div.stB) v5 hv5stkX hv5B hTBb
  have hevMain : Eval main Div.extract S z6
      (1 + (1 + (m2 + (1 + (1 + (1 + (m4 + (1 + (1 + (1 + (1 + (1 + m6)))))))))))) :=
    Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 (Eval.seq hev5
      (Eval.seq hev6 (Eval.seq hev7 (Eval.seq hev8 (Eval.seq hev9 (Eval.seq hev10
        (Eval.seq hev11 (Eval.seq hev12 hevT)))))))))))
  have frChain : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Div.stP → j ≠ Div.stB → j ≠ Div.stR →
      j ≠ Div.stX → j ≠ Div.stY → z6.stk j = S.stk j := by
    intro j hj0 hjP hjB hjR hjX hjY
    rw [hz6fr j hjX hjB, hv5fr j hj0 hjR hjX, hu4fr j hj0 hjX hjR, hw3frame j hj0 hjY,
      hu2fr j hj0 hjP, ht2frame j hj0 hjY]
  refine ⟨z6, 1 + (1 + (m2 + (1 + (1 + (1 + (m4 + (1 + (1 + (1 + (1 + (1 + m6))))))))))),
    hevMain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have hlenA : (bitsG a.natAbs.bits).length = a.natAbs.size := by
      rw [de_bitsG_length, Nat.size_eq_bits_len]
    have hlenB : (bitsG b.natAbs.bits).length = b.natAbs.size := by
      rw [de_bitsG_length, Nat.size_eq_bits_len]
    have hlenBb : (Glyph.bit false :: (bitsG b.natAbs.bits).reverse).length =
        b.natAbs.size + 1 := by
      rw [List.length_cons, List.length_reverse, hlenB]
    rw [hlenA] at hm2
    rw [hlenB] at hm4
    rw [hlenBb] at hm6
    have h1 : HvdH.isz a + HvdH.isz b + 1 = a.natAbs.size + b.natAbs.size + 5 := by
      simp only [HvdH.isz]
      omega
    rw [h1]
    omega
  · -- stack 0
    rw [hz6fr 0 (by decide) (by decide)]
    exact hv5stk0
  · -- stack 1 (`stP`)
    have h := hu2_P
    rw [de_bitsG_reverse] at h
    rw [hz6fr Div.stP (by decide) (by decide), hv5fr Div.stP (by decide) (by decide) (by decide),
      hu4fr Div.stP (by decide) (by decide) (by decide), hw3frame Div.stP (by decide) (by decide),
      List.append_assoc]
    exact h
  · -- stack 2 (`stB`)
    have hrevB : (Glyph.bit false :: (bitsG b.natAbs.bits).reverse).reverse =
        bitsG b.natAbs.bits ++ [Glyph.bit false] := by
      rw [List.reverse_cons, List.reverse_reverse]
    rw [de_padBits_succ_size, de_bitsG_append, de_bitsG_singleton, ← hrevB]
    exact hz6B
  · -- stack 3 (`stR`)
    rw [hz6fr Div.stR (by decide) (by decide), de_bitsG_padBits_zero]
    exact hv5stkR
  · -- stack 4 (`stQ`)
    rw [frChain Div.stQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hQ
  · -- stack 5 (`stS`)
    rw [frChain Div.stS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hS5
  · -- stack 6 (`stC`)
    rw [frChain Div.stC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hS6
  · -- stack 7 (`stD`)
    rw [frChain Div.stD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hS7
  · -- stack 8 (`stX`)
    exact hz6X
  · -- stack 9 (`stY`)
    rw [hz6fr Div.stY (by decide) (by decide), hv5fr Div.stY (by decide) (by decide) (by decide),
      hu4fr Div.stY (by decide) (by decide) (by decide), hw3stkY,
      hu2fr Div.stY (by decide) (by decide), ht2stkY, hS9]
    simp [List.cons_append]
  · -- the frame
    intro j hj0 hjP hjB hjR hjQ hjS hjC hjD hjX hjY
    exact frChain j hj0 hjP hjB hjR hjX hjY

end Work.IntLib
