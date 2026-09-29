import Mathlib
import Submission.Work.MainP.crtJoinDefs
import Submission.Work.MainP.crtJoinScan

/-!
# `crtJoinElems`: the element-consuming pass of the CRT join

This file proves `Work.MainP.crtJoinElems` (see the statement at the bottom): the program
`Work.MainP.consumeListN dst cnt` of `Submission/Work/MainP/crtJoinDefs.lean` consumes the encoded
list `Gs` on stack 0, pushing the element encodings in reverse on the buffer stack `dst`
(`Work.MainP.bufReg`) and one `jtok` per consumed glyph, in blocks separated by `jdelim`, on the
count stack `cnt` (`Work.MainP.cntReg`).

The development follows the Kernel pattern of `Submission/Work/Kernel/dropValue.lean`:

* `scanSt_final_eq` — state-level bookkeeping for the two closing steps `set 2 jbase ;; peek 1 1`;
* `scanBodyEval` — one round of the pending-subtree scan of `Work.MainP.scanBody` (the Kernel body
  plus the two extra pushes, cost `≤ 10`);
* `scanValOfBody` / `scanValEval` — the unrolling of the scan loop over a whole element
  `Work.MainP.scanVal` (via `Work.Kernel.dropValueLoopLe` and `HvdH.PendOK`);
* `elemBodyEval` — one element of the list (`Work.MainP.elemBody`);
* `consumeListLoopEval` — the whole list loop `Work.MainP.consumeList`;
* `crtJoinElems` — the assembly.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-- `jtok` is the Kernel pending-subtree token. -/
theorem jtok_eq_dropValue_tok : jtok = Work.Kernel.dropValue_tok := rfl

/-- The base marker and the token of the counter region are distinct. -/
theorem dropValue_base_ne_tok : Work.Kernel.dropValue_base ≠ jtok := by
  rw [jtok_eq_dropValue_tok]; decide

/-- **Bookkeeping of `set 2 jbase ;; peek 1 1`.**  If a state `Y` still has to be updated on the two
extra stacks, carries the unary counter for `p'` tokens on stack 1 (above the tail `X.stk 1`), agrees
with `X` off stacks `0,1,dst,cnt` and off registers `1,2,3`, and has the token in register 3, then
running `set 2 jbase` and refreshing register 1 from stack 1 lands exactly in the canonical scan
state `scanSt`. -/
theorem scanSt_final_eq (X Y : State) (dst cnt : Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt)
    (t' B' C' : List Glyph) (p' : ℕ)
    (h0 : Y.stk 0 = t') (hd : Y.stk dst = B') (hc : Y.stk cnt = C')
    (h1 : Y.stk 1 = Work.Kernel.dropValue_stk1 p' (X.stk 1))
    (hk : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ dst → k ≠ cnt → Y.stk k = X.stk k)
    (hr : ∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 3 → Y.reg r = X.reg r)
    (hr3 : Y.reg 3 = Work.Kernel.dropValue_tok) :
    State.tPeek (State.tSet Y 2 Work.Kernel.dropValue_base) 1 1
      = scanSt X dst cnt t' B' C' p' := by
  apply Work.Kernel.dropValue_state_ext
  · intro r
    rw [Work.Kernel.dropValue_tPeek_reg, Work.Kernel.dropValue_compSet_stk,
      Work.Kernel.dropValue_compSet_reg, h1]
    by_cases h1' : r = 1
    · rw [h1', if_pos rfl, Work.Kernel.dropValue_stk1_headD, scanSt_reg1]
    · rw [if_neg h1']
      by_cases h2' : r = 2
      · rw [h2', if_pos rfl, scanSt_reg2]
      · rw [if_neg h2']
        by_cases h3' : r = 3
        · rw [h3', hr3, scanSt_reg3]
        · rw [hr r h1' h2' h3', scanSt_reg_other X dst cnt t' B' C' p' r h1' h2' h3']
  · intro k
    rw [Work.Kernel.dropValue_tPeek_stk, Work.Kernel.dropValue_compSet_stk]
    by_cases hk0 : k = 0
    · rw [hk0, h0, scanSt_stk0 X dst cnt h0d h0c t' B' C' p']
    · by_cases hk1 : k = 1
      · rw [hk1, h1, scanSt_stk1 X dst cnt h1d h1c t' B' C' p']
      · by_cases hkd : k = dst
        · rw [hkd, hd, scanSt_stk_dst X dst cnt hdc t' B' C' p']
        · by_cases hkc : k = cnt
          · rw [hkc, hc, scanSt_stk_cnt]
          · rw [hk k hk0 hk1 hkd hkc,
              scanSt_stk_other X dst cnt h0d h0c h1d h1c t' B' C' p' k hk0 hk1 hkd hkc]

/-- **One round of the element scan.**  One iteration of `scanBody dst cnt` consumes the top glyph
`g'` of stack 0, pushes it on `dst`, pushes one token on `cnt`, and advances the unary
pending-subtree counter on stack 1 from `p` to `pendStep g' p`; cost at most 10. -/
theorem scanBodyEval (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt)
    (X : HvdH.State) (g' : HvdH.Glyph) (t' B C : List HvdH.Glyph) (p : ℕ) (hp : 1 ≤ p) :
    ∃ c ≤ 10, HvdH.Eval main (Work.MainP.scanBody dst cnt)
      (Work.MainP.scanSt X dst cnt (g' :: t') B C p)
      (Work.MainP.scanSt X dst cnt t' (g' :: B) (Work.MainP.jtok :: C) (HvdH.pendStep g' p)) c := by
  set A := Work.MainP.scanSt X dst cnt (g' :: t') B C p with hA
  set A1 := State.tPop A 1 2 with hA1
  set A2 := State.tPop A1 0 2 with hA2
  set A3 := State.tPush A2 dst 2 with hA3
  set A4 := State.tPush A3 cnt 3 with hA4
  -- components of `A`
  have hA_stk0 : A.stk 0 = g' :: t' := by
    rw [hA]; exact Work.MainP.scanSt_stk0 X dst cnt h0d h0c (g' :: t') B C p
  have hA_stk1 : A.stk 1 = Work.Kernel.dropValue_stk1 p (X.stk 1) := by
    rw [hA]; exact Work.MainP.scanSt_stk1 X dst cnt h1d h1c (g' :: t') B C p
  have hA_stkd : A.stk dst = B := by
    rw [hA]; exact Work.MainP.scanSt_stk_dst X dst cnt hdc (g' :: t') B C p
  have hA_stkc : A.stk cnt = C := by
    rw [hA]; exact Work.MainP.scanSt_stk_cnt X dst cnt (g' :: t') B C p
  have hA_stk_other : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ dst → k ≠ cnt → A.stk k = X.stk k := by
    intro k hk0 hk1 hkd hkc
    rw [hA]
    exact Work.MainP.scanSt_stk_other X dst cnt h0d h0c h1d h1c (g' :: t') B C p k hk0 hk1 hkd hkc
  have hA_reg1 : A.reg 1 = Work.Kernel.dropValue_tok := by
    rw [hA, Work.MainP.scanSt_reg1, if_neg (by omega : ¬ p = 0)]
  have hA_reg2 : A.reg 2 = Work.Kernel.dropValue_base := by
    rw [hA]; exact Work.MainP.scanSt_reg2 X dst cnt (g' :: t') B C p
  have hA_reg3 : A.reg 3 = Work.Kernel.dropValue_tok := by
    rw [hA]; exact Work.MainP.scanSt_reg3 X dst cnt (g' :: t') B C p
  have hA_reg_other : ∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 3 → A.reg r = X.reg r := by
    intro r hr1 hr2 hr3
    rw [hA]
    exact Work.MainP.scanSt_reg_other X dst cnt (g' :: t') B C p r hr1 hr2 hr3
  -- the two pops
  have hA1_stk1 : A1.stk 1 = Work.Kernel.dropValue_stk1 (p - 1) (X.stk 1) := by
    rw [hA1, Work.Kernel.dropValue_scan_pop_stk_same, hA_stk1,
      Work.Kernel.dropValue_stk1_tail p (X.stk 1) hp]
  have hA1_stk0 : A1.stk 0 = g' :: t' := by
    rw [hA1, Work.Kernel.dropValue_scan_pop_stk_ne A 1 2 (by decide : ¬ ((0 : Stk) = 1)), hA_stk0]
  have hA1_reg2 : A1.reg 2 = Work.Kernel.dropValue_tok := by
    rw [hA1, Work.Kernel.dropValue_scan_pop_reg_same, hA_stk1, Work.Kernel.dropValue_stk1_headD,
      if_neg (by omega : ¬ p = 0)]
  have hA1_reg1 : A1.reg 1 = Work.Kernel.dropValue_tok := by
    rw [hA1, Work.Kernel.dropValue_scan_pop_reg_ne A 1 2 (by decide : ¬ ((1 : Reg) = 2)), hA_reg1]
  have hA1_reg3 : A1.reg 3 = Work.Kernel.dropValue_tok := by
    rw [hA1, Work.Kernel.dropValue_scan_pop_reg_ne A 1 2 (by decide : ¬ ((3 : Reg) = 2)), hA_reg3]
  have hA1_reg_ne : ∀ r : Reg, r ≠ 2 → A1.reg r = A.reg r := by
    intro r hr; rw [hA1, Work.Kernel.dropValue_scan_pop_reg_ne A 1 2 hr]
  have hA1_stk_ne : ∀ k : Stk, k ≠ 1 → A1.stk k = A.stk k := by
    intro k hk; rw [hA1, Work.Kernel.dropValue_scan_pop_stk_ne A 1 2 hk]
  -- the second pop
  have hA2_stk0 : A2.stk 0 = t' := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_stk_same, hA1_stk0, List.tail_cons]
  have hA2_stk1 : A2.stk 1 = Work.Kernel.dropValue_stk1 (p - 1) (X.stk 1) := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_stk_ne A1 0 2 (by decide : ¬ ((1 : Stk) = 0)), hA1_stk1]
  have hA2_reg2 : A2.reg 2 = g' := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_reg_same, hA1_stk0, List.headD_cons]
  have hA2_stkd : A2.stk dst = B := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_stk_ne A1 0 2 h0d, hA1_stk_ne dst h1d, hA_stkd]
  have hA2_stkc : A2.stk cnt = C := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_stk_ne A1 0 2 h0c, hA1_stk_ne cnt h1c, hA_stkc]
  have hA2_reg1 : A2.reg 1 = Work.Kernel.dropValue_tok := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_reg_ne A1 0 2 (by decide : ¬ ((1 : Reg) = 2)), hA1_reg1]
  have hA2_reg3 : A2.reg 3 = Work.Kernel.dropValue_tok := by
    rw [hA2, Work.Kernel.dropValue_scan_pop_reg_ne A1 0 2 (by decide : ¬ ((3 : Reg) = 2)), hA1_reg3]
  have hA2_reg_ne : ∀ r : Reg, r ≠ 2 → A2.reg r = A1.reg r := by
    intro r hr; rw [hA2, Work.Kernel.dropValue_scan_pop_reg_ne A1 0 2 hr]
  have hA2_stk_ne : ∀ k : Stk, k ≠ 0 → A2.stk k = A1.stk k := by
    intro k hk; rw [hA2, Work.Kernel.dropValue_scan_pop_stk_ne A1 0 2 hk]
  -- the two pushes
  have hA3_stkd : A3.stk dst = g' :: B := by
    rw [hA3, Work.Kernel.dropValue_scan_push_stk, hA2_reg2, hA2_stkd]
  have hA3_stk0 : A3.stk 0 = t' := by
    rw [hA3, Work.Kernel.dropValue_scan_push_stk_ne A2 dst 2 (fun h : (0 : Stk) = dst => h0d h.symm),
      hA2_stk0]
  have hA3_stk1 : A3.stk 1 = Work.Kernel.dropValue_stk1 (p - 1) (X.stk 1) := by
    rw [hA3, Work.Kernel.dropValue_scan_push_stk_ne A2 dst 2 (fun h : (1 : Stk) = dst => h1d h.symm),
      hA2_stk1]
  have hA3_stkc : A3.stk cnt = C := by
    rw [hA3, Work.Kernel.dropValue_scan_push_stk_ne A2 dst 2 (fun h : cnt = dst => hdc h.symm),
      hA2_stkc]
  have hA3_reg : ∀ r : Reg, A3.reg r = A2.reg r := by
    intro r; rw [hA3, Work.Kernel.dropValue_scan_push_reg]
  have hA3_reg2 : A3.reg 2 = g' := by rw [hA3_reg 2, hA2_reg2]
  have hA3_reg3 : A3.reg 3 = Work.Kernel.dropValue_tok := by rw [hA3_reg 3, hA2_reg3]
  have hA3_stk_ne : ∀ k : Stk, k ≠ dst → A3.stk k = A2.stk k := by
    intro k hk; rw [hA3, Work.Kernel.dropValue_scan_push_stk_ne A2 dst 2 hk]
  have hA4_stkc : A4.stk cnt = jtok :: C := by
    rw [hA4, Work.Kernel.dropValue_scan_push_stk, hA3_reg3, hA3_stkc]
  have hA4_stk0 : A4.stk 0 = t' := by
    rw [hA4, Work.Kernel.dropValue_scan_push_stk_ne A3 cnt 3 (fun h : (0 : Stk) = cnt => h0c h.symm),
      hA3_stk_ne (0 : Stk) (fun h : (0 : Stk) = dst => h0d h.symm), hA2_stk0]
  have hA4_stk1 : A4.stk 1 = Work.Kernel.dropValue_stk1 (p - 1) (X.stk 1) := by
    rw [hA4, Work.Kernel.dropValue_scan_push_stk_ne A3 cnt 3 (fun h : (1 : Stk) = cnt => h1c h.symm),
      hA3_stk_ne (1 : Stk) (fun h : (1 : Stk) = dst => h1d h.symm), hA2_stk1]
  have hA4_stkd : A4.stk dst = g' :: B := by
    rw [hA4, Work.Kernel.dropValue_scan_push_stk_ne A3 cnt 3 hdc, hA3_stkd]
  have hA4_reg : ∀ r : Reg, A4.reg r = A3.reg r := by
    intro r; rw [hA4, Work.Kernel.dropValue_scan_push_reg]
  have hA4_reg2 : A4.reg 2 = g' := by rw [hA4_reg 2, hA3_reg2]
  have hA4_reg3 : A4.reg 3 = Work.Kernel.dropValue_tok := by rw [hA4_reg 3, hA3_reg3]
  have hA4_stk_ne : ∀ k : Stk, k ≠ cnt → A4.stk k = A3.stk k := by
    intro k hk; rw [hA4, Work.Kernel.dropValue_scan_push_stk_ne A3 cnt 3 hk]
  -- the pending-subtree chain and the final refresh
  obtain ⟨c5, hc5, e5⟩ := Work.Kernel.dropValueChainEval main A4 g' hA4_reg2 hA4_reg3
  set Y := A4.updStk 1 (List.replicate (HvdH.pendStep g' 1) Work.Kernel.dropValue_tok ++ A4.stk 1)
    with hY
  have hp1 : p - 1 + 1 = p := by omega
  have hY_stk1 : Y.stk 1 = Work.Kernel.dropValue_stk1 (HvdH.pendStep g' p) (X.stk 1) := by
    rw [hY, State.updStk_same, hA4_stk1, Work.Kernel.dropValueStk1PendStep g' (p - 1) (X.stk 1), hp1]
  have hY_stk0 : Y.stk 0 = t' := by
    rw [hY, State.updStk_apply, if_neg (by decide : ¬ ((0 : Stk) = 1)), hA4_stk0]
  have hY_stkd : Y.stk dst = g' :: B := by
    rw [hY, State.updStk_apply, if_neg (fun h : dst = 1 => h1d h), hA4_stkd]
  have hY_stkc : Y.stk cnt = jtok :: C := by
    rw [hY, State.updStk_apply, if_neg (fun h : cnt = 1 => h1c h), hA4_stkc]
  have hY_reg3 : Y.reg 3 = Work.Kernel.dropValue_tok := by
    rw [hY, State.updStk_reg, hA4_reg3]
  have hY_other : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ dst → k ≠ cnt → Y.stk k = X.stk k := by
    intro k hk0 hk1 hkd hkc
    rw [hY, State.updStk_apply, if_neg (fun h : k = 1 => hk1 h), hA4_stk_ne k hkc, hA3_stk_ne k hkd,
      hA2_stk_ne k hk0, hA1_stk_ne k hk1, hA_stk_other k hk0 hk1 hkd hkc]
  have hY_reg_other : ∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 3 → Y.reg r = X.reg r := by
    intro r hr1 hr2 hr3
    rw [hY, State.updStk_reg, hA4_reg r, hA3_reg r, hA2_reg_ne r hr2, hA1_reg_ne r hr2,
      hA_reg_other r hr1 hr2 hr3]
  have hfinal : State.tPeek (State.tSet Y 2 Work.Kernel.dropValue_base) 1 1
      = Work.MainP.scanSt X dst cnt t' (g' :: B) (Work.MainP.jtok :: C) (HvdH.pendStep g' p) :=
    scanSt_final_eq X Y dst cnt h0d h0c h1d h1c hdc t' (g' :: B) (Work.MainP.jtok :: C)
      (HvdH.pendStep g' p) hY_stk0 hY_stkd hY_stkc hY_stk1 hY_other hY_reg_other hY_reg3
  refine ⟨1 + (1 + (1 + (1 + (c5 + (1 + 1))))), by omega, ?_⟩
  rw [← hfinal]
  exact Eval.seq (Eval.pop 1 2 A)
    (Eval.seq (Eval.pop 0 2 A1)
      (Eval.seq (Eval.push dst 2 A2)
        (Eval.seq (Eval.push cnt 3 A3)
          (Eval.seq e5
            (Eval.seq (Eval.set 2 Work.Kernel.dropValue_base Y)
              (Eval.peek 1 1 (State.tSet Y 2 Work.Kernel.dropValue_base)))))))

/-- **`scanVal` unrolls the element scan.**  Given the one-round lemma `hstep` for
`Work.MainP.scanBody`, the program `Work.MainP.scanVal dst cnt` copies the whole element `g` from
stack 0 to `dst` (reversed) while pushing one token per glyph on `cnt`, provided `g` is a pending
subtree (`HvdH.PendOK g 1`, which is what the values of stack 0 satisfy). -/
theorem scanValOfBody (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt)
    (hstep : ∀ (X : HvdH.State) (g' : HvdH.Glyph) (t' B C : List HvdH.Glyph) (p : ℕ), 1 ≤ p →
      ∃ c ≤ 10, HvdH.Eval main (Work.MainP.scanBody dst cnt)
        (Work.MainP.scanSt X dst cnt (g' :: t') B C p)
        (Work.MainP.scanSt X dst cnt t' (g' :: B) (Work.MainP.jtok :: C) (HvdH.pendStep g' p)) c) :
    ∀ (g rest B C : List HvdH.Glyph), HvdH.PendOK g 1 → ∀ X : HvdH.State,
      X.stk 0 = g ++ rest → X.stk dst = B → X.stk cnt = C →
      ∃ X' n, n ≤ 11 * g.length + 8 ∧ HvdH.Eval main (Work.MainP.scanVal dst cnt) X X' n ∧
        X'.stk 0 = rest ∧ X'.stk dst = g.reverse ++ B ∧
        X'.stk cnt = List.replicate g.length Work.MainP.jtok ++ C ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k) ∧
        (∀ r : HvdH.Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → X'.reg r = X.reg r) := by
  intro g rest B C hP X h0 hd hc
  set f : ℕ → State := fun i => Work.MainP.scanSt X dst cnt (g.drop i ++ rest)
    ((g.take i).reverse ++ B) (List.replicate i Work.MainP.jtok ++ C)
    (HvdH.pendFold (g.take i) 1) with hf
  -- step 1: the pending-counter set-up
  have hdvi : Work.Kernel.dropValue_iter X (g ++ rest) 1 = f 0 := by
    have h1 : (Work.Kernel.dropValue_iter X (g ++ rest) 1).stk dst = B := by
      rw [Work.Kernel.dropValue_iter_stk X (g ++ rest) 1 dst h0d h1d, hd]
    have h2 : (Work.Kernel.dropValue_iter X (g ++ rest) 1).stk cnt = C := by
      rw [Work.Kernel.dropValue_iter_stk X (g ++ rest) 1 cnt h0c h1c, hc]
    rw [Work.MainP.dropValue_iter_eq_scanSt X dst cnt (g ++ rest) B C 1 h1 h2]
    simp [hf]
  have e1 : HvdH.Eval main Work.Kernel.dropValue_pre X (f 0) 6 := by
    have h := Work.Kernel.dropValuePreEval main X
    rw [h0, hdvi] at h
    exact h
  -- step 2: the scan loop over the whole encoding
  have hstepf : ∀ i < g.length, (f i).reg 1 = Work.MainP.jtok ∧
      ∃ c ≤ 10, HvdH.Eval main (Work.MainP.scanBody dst cnt) (f i) (f (i + 1)) c := by
    intro i hi
    have hpos : 1 ≤ HvdH.pendFold (g.take i) 1 := hP.2 i hi
    constructor
    · have hh : (f i).reg 1 = Work.Kernel.dropValue_tok := by
        rw [hf, Work.MainP.scanSt_reg1,
          if_neg (by omega : ¬ HvdH.pendFold (g.take i) 1 = 0)]
      exact hh
    · set g' : HvdH.Glyph := (g.drop i).headD Work.Kernel.dropValue_base with hg'
      have hdrop : g.drop i = g' :: g.drop (i + 1) := by
        rw [hg']; exact Work.Kernel.dropValue_scan_drop_cons g i hi
      obtain ⟨c, hcle, hev⟩ := hstep X g' (g.drop (i + 1) ++ rest) ((g.take i).reverse ++ B)
        (List.replicate i Work.MainP.jtok ++ C) (HvdH.pendFold (g.take i) 1) hpos
      refine ⟨c, hcle, ?_⟩
      have hsrc : f i = Work.MainP.scanSt X dst cnt (g' :: (g.drop (i + 1) ++ rest))
          ((g.take i).reverse ++ B) (List.replicate i Work.MainP.jtok ++ C)
          (HvdH.pendFold (g.take i) 1) := by
        simp only [hf]
        rw [hdrop, List.cons_append]
      have hB' : (g.take (i + 1)).reverse = g' :: (g.take i).reverse := by
        have h1 : g.take (i + 1) = g.take i ++ [g[i]] := (List.take_append_getElem hi).symm
        have h2 : g' = g[i] := by
          rw [hg', List.drop_eq_getElem_cons hi, List.headD_cons]
        rw [h1, List.reverse_append, h2]
        rfl
      have hB : (g.take (i + 1)).reverse ++ B = g' :: ((g.take i).reverse ++ B) := by
        rw [hB']; rfl
      have hC : List.replicate (i + 1) Work.MainP.jtok ++ C
          = Work.MainP.jtok :: (List.replicate i Work.MainP.jtok ++ C) := by
        rw [List.replicate_succ]; rfl
      have hpnd : HvdH.pendFold (g.take (i + 1)) 1
          = HvdH.pendStep g' (HvdH.pendFold (g.take i) 1) := by
        rw [hg']; exact Work.Kernel.dropValue_scan_pendFold_take_succ g 1 i hi
      have htgt : Work.MainP.scanSt X dst cnt (g.drop (i + 1) ++ rest)
            (g' :: ((g.take i).reverse ++ B)) (Work.MainP.jtok :: (List.replicate i Work.MainP.jtok ++ C))
            (HvdH.pendStep g' (HvdH.pendFold (g.take i) 1)) = f (i + 1) := by
        simp only [hf]
        rw [← hB, ← hC, ← hpnd]
      rw [hsrc, ← htgt]
      exact hev
  have hstop : (f g.length).reg 1 ≠ Work.MainP.jtok := by
    have hzero : HvdH.pendFold (g.take g.length) 1 = 0 := by
      rw [List.take_length]; exact hP.1
    have hbase : (f g.length).reg 1 = Work.Kernel.dropValue_base := by
      simp only [hf]
      rw [hzero, Work.MainP.scanSt_reg1, if_pos rfl]
    rw [hbase]; exact Work.MainP.dropValue_base_ne_tok
  obtain ⟨m, hmle, hloop⟩ :=
    Work.Kernel.dropValueLoopLe main 1 Work.MainP.jtok (Work.MainP.scanBody dst cnt) 10 g.length f
      hstepf hstop
  -- step 3: the final drop of the counter region
  have hfend : f g.length = Work.MainP.scanSt X dst cnt rest (g.reverse ++ B)
      (List.replicate g.length Work.MainP.jtok ++ C) 0 := by
    simp only [hf]
    simp [List.drop_length, List.take_length, hP.1]
  set Z := State.tPop (f g.length) 1 0 with hZ
  have hZ_stk0 : Z.stk 0 = rest := by
    rw [hZ, Work.Kernel.dropValue_scan_pop_stk_ne (f g.length) 1 0 (by decide : ¬ ((0 : Stk) = 1)),
      hfend]
    exact Work.MainP.scanSt_stk0 X dst cnt h0d h0c rest (g.reverse ++ B)
      (List.replicate g.length Work.MainP.jtok ++ C) 0
  have hZ_stkd : Z.stk dst = g.reverse ++ B := by
    rw [hZ, Work.Kernel.dropValue_scan_pop_stk_ne (f g.length) 1 0
      (fun h : dst = 1 => h1d h), hfend]
    exact Work.MainP.scanSt_stk_dst X dst cnt hdc rest (g.reverse ++ B)
      (List.replicate g.length Work.MainP.jtok ++ C) 0
  have hZ_stkc : Z.stk cnt = List.replicate g.length Work.MainP.jtok ++ C := by
    rw [hZ, Work.Kernel.dropValue_scan_pop_stk_ne (f g.length) 1 0
      (fun h : cnt = 1 => h1c h), hfend]
    exact Work.MainP.scanSt_stk_cnt X dst cnt rest (g.reverse ++ B)
      (List.replicate g.length Work.MainP.jtok ++ C) 0
  have hZ_stk1 : Z.stk 1 = X.stk 1 := by
    rw [hZ, Work.Kernel.dropValue_scan_pop_stk_same, hfend,
      Work.MainP.scanSt_stk1 X dst cnt h1d h1c rest (g.reverse ++ B)
        (List.replicate g.length Work.MainP.jtok ++ C) 0,
      Work.Kernel.dropValue_stk1_zero, List.tail_cons]
  have hZ_other : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → Z.stk k = X.stk k := by
    intro k hk0 hkd hkc
    by_cases hk1 : k = 1
    · rw [hk1]; exact hZ_stk1
    · rw [hZ, Work.Kernel.dropValue_scan_pop_stk_ne (f g.length) 1 0
        (fun h : k = 1 => hk1 h), hfend]
      exact Work.MainP.scanSt_stk_other X dst cnt h0d h0c h1d h1c rest (g.reverse ++ B)
        (List.replicate g.length Work.MainP.jtok ++ C) 0 k hk0 hk1 hkd hkc
  have hZ_reg_other : ∀ r : HvdH.Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → Z.reg r = X.reg r := by
    intro r hr0 hr1 hr2 hr3
    rw [hZ, Work.Kernel.dropValue_scan_pop_reg_ne (f g.length) 1 0 hr0, hfend]
    exact Work.MainP.scanSt_reg_other X dst cnt rest (g.reverse ++ B)
      (List.replicate g.length Work.MainP.jtok ++ C) 0 r hr1 hr2 hr3
  refine ⟨Z, 6 + (m + 1), by omega, ?_, hZ_stk0, hZ_stkd, hZ_stkc, hZ_other, hZ_reg_other⟩
  rw [hZ, Work.MainP.scanVal]
  exact Eval.seq e1 (Eval.seq hloop (Eval.pop 1 0 (f g.length)))

/-- **The element copy.**  `Work.MainP.scanVal dst cnt` copies the value encoding `g` (a pending
subtree) from stack 0 to the buffer `dst`, reversed, pushing one token per glyph on `cnt`. -/
theorem scanValEval (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt) :
    ∀ (g rest B C : List HvdH.Glyph), HvdH.PendOK g 1 → ∀ X : HvdH.State,
      X.stk 0 = g ++ rest → X.stk dst = B → X.stk cnt = C →
      ∃ X' n, n ≤ 11 * g.length + 8 ∧ HvdH.Eval main (Work.MainP.scanVal dst cnt) X X' n ∧
        X'.stk 0 = rest ∧ X'.stk dst = g.reverse ++ B ∧
        X'.stk cnt = List.replicate g.length Work.MainP.jtok ++ C ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k) ∧
        (∀ r : HvdH.Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → X'.reg r = X.reg r) :=
  scanValOfBody main dst cnt h0d h0c h1d h1c hdc
    (scanBodyEval main dst cnt h0d h0c h1d h1c hdc)

/-- **One element of the list.**  Given the element copy `hscan` (`Work.MainP.scanVal`),
`Work.MainP.elemBody dst cnt` consumes one `cons` of the list encoding on stack 0, copies the
element `g` to `dst` (reversed) and records its block `tok^{|g|} jdelim` on `cnt`. -/
theorem elemBodyOfScan (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt)
    (hscan : ∀ (g rest B C : List HvdH.Glyph), HvdH.PendOK g 1 → ∀ X : HvdH.State,
      X.stk 0 = g ++ rest → X.stk dst = B → X.stk cnt = C →
      ∃ X' n, n ≤ 11 * g.length + 8 ∧ HvdH.Eval main (Work.MainP.scanVal dst cnt) X X' n ∧
        X'.stk 0 = rest ∧ X'.stk dst = g.reverse ++ B ∧
        X'.stk cnt = List.replicate g.length Work.MainP.jtok ++ C ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k) ∧
        (∀ r : HvdH.Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → X'.reg r = X.reg r)) :
    ∀ (g : List HvdH.Glyph) (Gs : List (List HvdH.Glyph)) (t B C : List HvdH.Glyph),
      HvdH.PendOK g 1 → ∀ X : HvdH.State,
      X.stk 0 = HvdH.Glyph.cons :: (g ++ (Work.MainP.listEncR Gs ++ t)) → X.stk dst = B →
      X.stk cnt = C → X.reg 5 = Work.MainP.jdelim →
      ∃ X' n, n ≤ 11 * g.length + 11 ∧ HvdH.Eval main (Work.MainP.elemBody dst cnt) X X' n ∧
        X'.stk 0 = Work.MainP.listEncR Gs ++ t ∧ X'.stk dst = g.reverse ++ B ∧
        X'.stk cnt = List.replicate g.length Work.MainP.jtok ++ Work.MainP.jdelim :: C ∧
        X'.reg 1 = (Work.MainP.listEncR Gs ++ t).headD HvdH.Glyph.eos ∧
        X'.reg 5 = Work.MainP.jdelim ∧
        ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k := by
  intro g Gs t B C hP X h0 hd hc h5
  set X1 := State.tPop X 0 1 with hX1
  set X2 := State.tPush X1 cnt 5 with hX2
  have hX1_stk0 : X1.stk 0 = g ++ (Work.MainP.listEncR Gs ++ t) := by
    rw [hX1, Work.Kernel.dropValue_scan_pop_stk_same, h0, List.tail_cons]
  have hX1_reg5 : X1.reg 5 = Work.MainP.jdelim := by
    rw [hX1, Work.Kernel.dropValue_scan_pop_reg_ne X 0 1 (by decide : ¬ ((5 : Reg) = 1)), h5]
  have hX1_stkd : X1.stk dst = B := by
    rw [hX1, Work.Kernel.dropValue_scan_pop_stk_ne X 0 1 h0d, hd]
  have hX1_stkc : X1.stk cnt = C := by
    rw [hX1, Work.Kernel.dropValue_scan_pop_stk_ne X 0 1 h0c, hc]
  have hX1_stk_ne : ∀ k : HvdH.Stk, k ≠ 0 → X1.stk k = X.stk k := by
    intro k hk; rw [hX1, Work.Kernel.dropValue_scan_pop_stk_ne X 0 1 hk]
  have hX2_stkc : X2.stk cnt = Work.MainP.jdelim :: C := by
    rw [hX2, Work.Kernel.dropValue_scan_push_stk, hX1_reg5, hX1_stkc]
  have hX2_stk0 : X2.stk 0 = g ++ (Work.MainP.listEncR Gs ++ t) := by
    rw [hX2, Work.Kernel.dropValue_scan_push_stk_ne X1 cnt 5 (fun h : (0 : Stk) = cnt => h0c h.symm),
      hX1_stk0]
  have hX2_stkd : X2.stk dst = B := by
    rw [hX2, Work.Kernel.dropValue_scan_push_stk_ne X1 cnt 5 hdc, hX1_stkd]
  have hX2_reg5 : X2.reg 5 = Work.MainP.jdelim := by
    rw [hX2, Work.Kernel.dropValue_scan_push_reg, hX1_reg5]
  have hX2_stk_ne : ∀ k : HvdH.Stk, k ≠ cnt → X2.stk k = X1.stk k := by
    intro k hk; rw [hX2, Work.Kernel.dropValue_scan_push_stk_ne X1 cnt 5 hk]
  obtain ⟨X3, n3, hn3, hev3, h3_stk0, h3_stkd, h3_stkc, h3_other, h3_reg⟩ :=
    hscan g (Work.MainP.listEncR Gs ++ t) B (Work.MainP.jdelim :: C) hP X2 hX2_stk0 hX2_stkd
      hX2_stkc
  set X4 := State.tPeek X3 0 1 with hX4
  have h3_reg5 : X3.reg 5 = Work.MainP.jdelim := by
    rw [h3_reg 5 (by decide) (by decide) (by decide) (by decide), hX2_reg5]
  have hX4_reg1 : X4.reg 1 = (Work.MainP.listEncR Gs ++ t).headD HvdH.Glyph.eos := by
    rw [hX4, Work.Kernel.dropValue_tPeek_reg, if_pos rfl, h3_stk0]
  have hX4_reg5 : X4.reg 5 = Work.MainP.jdelim := by
    rw [hX4, Work.Kernel.dropValue_tPeek_reg, if_neg (by decide : ¬ ((5 : Reg) = 1)), h3_reg5]
  have hX4_stk0 : X4.stk 0 = Work.MainP.listEncR Gs ++ t := by
    rw [hX4, Work.Kernel.dropValue_tPeek_stk, h3_stk0]
  have hX4_stkd : X4.stk dst = g.reverse ++ B := by
    rw [hX4, Work.Kernel.dropValue_tPeek_stk, h3_stkd]
  have hX4_stkc : X4.stk cnt = List.replicate g.length Work.MainP.jtok ++ Work.MainP.jdelim :: C := by
    rw [hX4, Work.Kernel.dropValue_tPeek_stk, h3_stkc]
  have hX4_other : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X4.stk k = X.stk k := by
    intro k hk0 hkd hkc
    rw [hX4, Work.Kernel.dropValue_tPeek_stk, h3_other k hk0 hkd hkc, hX2_stk_ne k hkc,
      hX1_stk_ne k hk0]
  refine ⟨X4, 1 + (1 + (n3 + 1)), by omega, ?_, hX4_stk0, hX4_stkd, hX4_stkc, hX4_reg1, hX4_reg5,
    hX4_other⟩
  rw [hX4, Work.MainP.elemBody]
  exact Eval.seq (Eval.pop 0 1 X)
    (Eval.seq (Eval.push cnt 5 X1) (Eval.seq hev3 (Eval.peek 0 1 X3)))

/-- Block bookkeeping of `cntReg` over one more element. -/
theorem cntReg_cons_append (g : List Glyph) (Gs : List (List Glyph)) (C : List Glyph) :
    cntReg (g :: Gs) ++ C = cntReg Gs ++ (List.replicate g.length jtok ++ jdelim :: C) := by
  rw [cntReg_cons]
  simp [List.append_assoc, List.singleton_append]

/-- **One element of the list** (specialised to `Work.MainP.scanValEval`). -/
theorem elemBodyEval (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt) :
    ∀ (g : List HvdH.Glyph) (Gs : List (List HvdH.Glyph)) (t B C : List HvdH.Glyph),
      HvdH.PendOK g 1 → ∀ X : HvdH.State,
      X.stk 0 = HvdH.Glyph.cons :: (g ++ (Work.MainP.listEncR Gs ++ t)) → X.stk dst = B →
      X.stk cnt = C → X.reg 5 = Work.MainP.jdelim →
      ∃ X' n, n ≤ 11 * g.length + 11 ∧ HvdH.Eval main (Work.MainP.elemBody dst cnt) X X' n ∧
        X'.stk 0 = Work.MainP.listEncR Gs ++ t ∧ X'.stk dst = g.reverse ++ B ∧
        X'.stk cnt = List.replicate g.length Work.MainP.jtok ++ Work.MainP.jdelim :: C ∧
        X'.reg 1 = (Work.MainP.listEncR Gs ++ t).headD HvdH.Glyph.eos ∧
        X'.reg 5 = Work.MainP.jdelim ∧
        ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k :=
  elemBodyOfScan main dst cnt h0d h0c h1d h1c hdc (scanValEval main dst cnt h0d h0c h1d h1c hdc)

/-- **The list loop.**  Given the one-element step `helem`, the loop `Work.MainP.consumeList` walks
through the elements `Gs` of the list encoding on stack 0: each round copies one element to `dst`
and records its block on `cnt`, so that at the end stack 0 only carries the terminating `nil`. -/
theorem consumeListLoopOfElem (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt)
    (helem : ∀ (g : List HvdH.Glyph) (Gs : List (List HvdH.Glyph)) (t B C : List HvdH.Glyph),
      HvdH.PendOK g 1 → ∀ X : HvdH.State,
      X.stk 0 = HvdH.Glyph.cons :: (g ++ (Work.MainP.listEncR Gs ++ t)) → X.stk dst = B →
      X.stk cnt = C → X.reg 5 = Work.MainP.jdelim →
      ∃ X' n, n ≤ 11 * g.length + 11 ∧ HvdH.Eval main (Work.MainP.elemBody dst cnt) X X' n ∧
        X'.stk 0 = Work.MainP.listEncR Gs ++ t ∧ X'.stk dst = g.reverse ++ B ∧
        X'.stk cnt = List.replicate g.length Work.MainP.jtok ++ Work.MainP.jdelim :: C ∧
        X'.reg 1 = (Work.MainP.listEncR Gs ++ t).headD HvdH.Glyph.eos ∧
        X'.reg 5 = Work.MainP.jdelim ∧
        ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k) :
    ∀ (Gs : List (List HvdH.Glyph)) (t B C : List HvdH.Glyph),
      (∀ G ∈ Gs, HvdH.PendOK G 1) → (∀ G ∈ Gs, G ≠ []) →
      ∀ X : HvdH.State,
        X.stk 0 = Work.MainP.listEncR Gs ++ t → X.stk dst = B → X.stk cnt = C →
        X.reg 1 = (Work.MainP.listEncR Gs ++ t).headD HvdH.Glyph.eos →
        X.reg 5 = Work.MainP.jdelim →
        ∃ X' n, n ≤ 11 * (Gs.map List.length).sum + 12 * Gs.length + 1 ∧
          HvdH.Eval main (HvdH.Cmd.loop 1 HvdH.Glyph.cons (Work.MainP.elemBody dst cnt)) X X' n ∧
          X'.stk 0 = Work.MainP.listEncR ([] : List (List HvdH.Glyph)) ++ t ∧
          X'.stk dst = Work.MainP.bufReg Gs ++ B ∧ X'.stk cnt = Work.MainP.cntReg Gs ++ C ∧
          ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k := by
  intro Gs
  induction Gs with
  | nil =>
    intro t B C hP hne X h0 hd hc h1 h5
    have hreg : X.reg 1 ≠ HvdH.Glyph.cons := by
      rw [h1]
      simp [Work.MainP.listEncR]
    refine ⟨X, 1, by simp, Eval.loopF hreg, h0, ?_, ?_, ?_⟩
    · rw [hd, Work.MainP.bufReg_nil, List.nil_append]
    · rw [hc, Work.MainP.cntReg_nil, List.nil_append]
    · intro k _ _ _; rfl
  | cons g Gs ih =>
    intro t B C hP hne X h0 hd hc h1 h5
    have hPg : HvdH.PendOK g 1 := hP g (by simp)
    have hmem : ∀ G ∈ Gs, HvdH.PendOK G 1 := fun G hG => hP G (List.mem_cons_of_mem g hG)
    have hne' : ∀ G ∈ Gs, G ≠ [] := fun G hG => hne G (List.mem_cons_of_mem g hG)
    have h0' : X.stk 0 = HvdH.Glyph.cons :: (g ++ (Work.MainP.listEncR Gs ++ t)) := by
      rw [h0, Work.MainP.listEncR_cons, List.cons_append, List.append_assoc]
    have h1' : X.reg 1 = HvdH.Glyph.cons := by
      rw [h1]
      show (Work.MainP.listEncR (g :: Gs) ++ t).headD HvdH.Glyph.eos = HvdH.Glyph.cons
      rw [Work.MainP.listEncR_cons, List.cons_append]
      rfl
    obtain ⟨X2, n2, hn2, hev2, h2_stk0, h2_stkd, h2_stkc, h2_reg1, h2_reg5, h2_other⟩ :=
      helem g Gs t B C hPg X h0' hd hc h5
    obtain ⟨X3, n3, hn3, hev3, h3_stk0, h3_stkd, h3_stkc, h3_other⟩ :=
      ih t (g.reverse ++ B) (List.replicate g.length Work.MainP.jtok ++ Work.MainP.jdelim :: C)
        hmem hne' X2 h2_stk0 h2_stkd h2_stkc h2_reg1 h2_reg5
    have hsum : ((g :: Gs).map List.length).sum = g.length + (Gs.map List.length).sum := by simp
    have hlen : (g :: Gs).length = Gs.length + 1 := by simp
    refine ⟨X3, n2 + (n3 + 1), ?_, Eval.loopT h1' hev2 hev3, h3_stk0, ?_, ?_, ?_⟩
    · rw [hsum, hlen]; omega
    · rw [h3_stkd, Work.MainP.bufReg_cons, List.append_assoc]
    · rw [h3_stkc, cntReg_cons_append]
    · intro k hk0 hkd hkc
      rw [h3_other k hk0 hkd hkc, h2_other k hk0 hkd hkc]

/-- **The list loop** (specialised to `Work.MainP.elemBodyEval`). -/
theorem consumeListLoopEval (main : HvdH.Cmd) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1) (hdc : dst ≠ cnt) :
    ∀ (Gs : List (List HvdH.Glyph)) (t B C : List HvdH.Glyph),
      (∀ G ∈ Gs, HvdH.PendOK G 1) → (∀ G ∈ Gs, G ≠ []) →
      ∀ X : HvdH.State,
        X.stk 0 = Work.MainP.listEncR Gs ++ t → X.stk dst = B → X.stk cnt = C →
        X.reg 1 = (Work.MainP.listEncR Gs ++ t).headD HvdH.Glyph.eos →
        X.reg 5 = Work.MainP.jdelim →
        ∃ X' n, n ≤ 11 * (Gs.map List.length).sum + 12 * Gs.length + 1 ∧
          HvdH.Eval main (HvdH.Cmd.loop 1 HvdH.Glyph.cons (Work.MainP.elemBody dst cnt)) X X' n ∧
          X'.stk 0 = Work.MainP.listEncR ([] : List (List HvdH.Glyph)) ++ t ∧
          X'.stk dst = Work.MainP.bufReg Gs ++ B ∧ X'.stk cnt = Work.MainP.cntReg Gs ++ C ∧
          ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X'.stk k = X.stk k :=
  consumeListLoopOfElem main dst cnt h0d h0c h1d h1c hdc
    (elemBodyEval main dst cnt h0d h0c h1d h1c hdc)

/-! ## Components of the pre-state `clPre` -/

theorem clPre_stk0 (s : State) (dst cnt : Stk) (h0d : dst ≠ 0) (h0c : cnt ≠ 0)
    (Gs : List (List Glyph)) (t b c : List Glyph) :
    (clPre s dst cnt Gs t b c).stk 0 = listEncR Gs ++ t := by
  have h1 : ¬ ((0 : Stk) = cnt) := fun h => h0c h.symm
  have h2 : ¬ ((0 : Stk) = dst) := fun h => h0d h.symm
  simp [clPre, h1, h2]

theorem clPre_stk_dst (s : State) (dst cnt : Stk) (h0d : dst ≠ 0) (hdc : dst ≠ cnt)
    (Gs : List (List Glyph)) (t b c : List Glyph) :
    (clPre s dst cnt Gs t b c).stk dst = b := by
  have h1 : ¬ (dst = cnt) := hdc
  have h2 : ¬ (dst = 0) := fun h => h0d h
  simp [clPre, h1, h2]

theorem clPre_stk_cnt (s : State) (dst cnt : Stk) (h0c : cnt ≠ 0)
    (Gs : List (List Glyph)) (t b c : List Glyph) :
    (clPre s dst cnt Gs t b c).stk cnt = jcb :: c := by
  have h1 : ¬ (cnt = 0) := h0c
  simp [clPre, h1]

theorem clPre_stk_other (s : State) (dst cnt : Stk) (h0d : dst ≠ 0) (h0c : cnt ≠ 0)
    (Gs : List (List Glyph)) (t b c : List Glyph) (k : Stk)
    (hk0 : k ≠ 0) (hkd : k ≠ dst) (hkc : k ≠ cnt) :
    (clPre s dst cnt Gs t b c).stk k = s.stk k := by
  have h1 : ¬ (k = cnt) := hkc
  have h2 : ¬ (k = dst) := hkd
  have h3 : ¬ (k = 0) := hk0
  simp [clPre, h1, h2, h3]

theorem clPre_reg5 (s : State) (dst cnt : Stk) (Gs : List (List Glyph)) (t b c : List Glyph) :
    (clPre s dst cnt Gs t b c).reg 5 = jdelim := by
  simp [clPre]

/-! ## `crtJoinElems` -/

theorem crtJoinElems (main : HvdH.Cmd) (s : HvdH.State) (dst cnt : HvdH.Stk)
    (h0d : dst ≠ 0) (h0c : cnt ≠ 0) (h1d : dst ≠ 1) (h1c : cnt ≠ 1)
    (h5d : dst ≠ 5) (h5c : cnt ≠ 5) (hdc : dst ≠ cnt) :
    ∀ (Gs : List (List HvdH.Glyph)) (t b c : List HvdH.Glyph),
      (∀ G ∈ Gs, HvdH.PendOK G 1) → (∀ G ∈ Gs, G ≠ []) →
      ∃ (s' : HvdH.State) (n : ℕ),
        n ≤ 30 * ((Gs.map List.length).sum + Gs.length + 1) + 10 ∧
        HvdH.Eval main (Work.MainP.consumeListN dst cnt) (Work.MainP.clPre s dst cnt Gs t b c) s' n ∧
        s'.stk 0 = t ∧ s'.stk dst = Work.MainP.bufReg Gs ++ b ∧
        s'.stk cnt = Work.MainP.cntReg Gs ++ (Work.MainP.jcb :: c) ∧
        ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → s'.stk k = s.stk k := by
  intro Gs t b c hP hne
  set X := clPre s dst cnt Gs t b c with hX
  -- the pre-state
  have hX_stk0 : X.stk 0 = listEncR Gs ++ t := by rw [hX]; exact clPre_stk0 s dst cnt h0d h0c Gs t b c
  have hX_stkd : X.stk dst = b := by rw [hX]; exact clPre_stk_dst s dst cnt h0d hdc Gs t b c
  have hX_stkc : X.stk cnt = jcb :: c := by rw [hX]; exact clPre_stk_cnt s dst cnt h0c Gs t b c
  have hX_reg5 : X.reg 5 = jdelim := by rw [hX]; exact clPre_reg5 s dst cnt Gs t b c
  have hX_other : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X.stk k = s.stk k := by
    intro k hk0 hkd hkc
    rw [hX]; exact clPre_stk_other s dst cnt h0d h0c Gs t b c k hk0 hkd hkc
  -- step 1: `peek 0 1`
  set X1 := State.tPeek X 0 1 with hX1
  have hX1_stk0 : X1.stk 0 = listEncR Gs ++ t := by
    rw [hX1, Work.Kernel.dropValue_tPeek_stk, hX_stk0]
  have hX1_stkd : X1.stk dst = b := by
    rw [hX1, Work.Kernel.dropValue_tPeek_stk, hX_stkd]
  have hX1_stkc : X1.stk cnt = jcb :: c := by
    rw [hX1, Work.Kernel.dropValue_tPeek_stk, hX_stkc]
  have hX1_reg1 : X1.reg 1 = (listEncR Gs ++ t).headD HvdH.Glyph.eos := by
    rw [hX1, Work.Kernel.dropValue_tPeek_reg, if_pos rfl, hX_stk0]
  have hX1_reg5 : X1.reg 5 = jdelim := by
    rw [hX1, Work.Kernel.dropValue_tPeek_reg, if_neg (by decide : ¬ ((5 : Reg) = 1)), hX_reg5]
  have hX1_other : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X1.stk k = s.stk k := by
    intro k hk0 hkd hkc
    rw [hX1, Work.Kernel.dropValue_tPeek_stk, hX_other k hk0 hkd hkc]
  -- step 2: the list loop
  obtain ⟨X2, n2, hn2, hev2, h2_stk0, h2_stkd, h2_stkc, h2_other⟩ :=
    consumeListLoopEval main dst cnt h0d h0c h1d h1c hdc Gs t b (jcb :: c) hP hne X1
      hX1_stk0 hX1_stkd hX1_stkc hX1_reg1 hX1_reg5
  -- step 3: discard the terminating `nil`
  have h2_stk0' : X2.stk 0 = HvdH.Glyph.nil :: t := by
    rw [h2_stk0]
    simp [Work.MainP.listEncR]
  set X3 := State.tPop X2 0 1 with hX3
  have hX3_stk0 : X3.stk 0 = t := by
    rw [hX3, Work.Kernel.dropValue_scan_pop_stk_same, h2_stk0', List.tail_cons]
  have hX3_stkd : X3.stk dst = bufReg Gs ++ b := by
    rw [hX3, Work.Kernel.dropValue_scan_pop_stk_ne X2 0 1 h0d, h2_stkd]
  have hX3_stkc : X3.stk cnt = cntReg Gs ++ (jcb :: c) := by
    rw [hX3, Work.Kernel.dropValue_scan_pop_stk_ne X2 0 1 h0c, h2_stkc]
  have hX3_other : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → k ≠ cnt → X3.stk k = s.stk k := by
    intro k hk0 hkd hkc
    rw [hX3, Work.Kernel.dropValue_scan_pop_stk_ne X2 0 1 hk0, h2_other k hk0 hkd hkc,
      hX1_other k hk0 hkd hkc]
  refine ⟨X3, (1 + n2) + 1, ?_, ?_, hX3_stk0, hX3_stkd, hX3_stkc, hX3_other⟩
  · omega
  · rw [hX3, Work.MainP.consumeListN, Work.MainP.consumeList]
    exact Eval.seq (Eval.seq (Eval.peek 0 1 X) hev2) (Eval.pop 0 1 X2)

end Work.MainP
