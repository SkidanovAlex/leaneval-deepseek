import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Kernel.dropValueDefs
import Submission.Work.Kernel.dropValueLoopLe
import Submission.Work.Kernel.dropValuePreEval

/-!
# Kernel: `drop` — drop the top value of stack 0

`HvdH.KernelLib.drop`: there is a StackLang program dropping the value on top of stack 0 at cost
`O(vsz v)` (uniformly in `vs`, the state and the enclosing program `main`).

The program `Work.Kernel.dropValue_prog` (in `Submission/Work/Kernel/dropValueDefs.lean`) scans the
self-delimiting encoding `v.enc` with a *unary* pending-subtree counter on stack 1 above a frame
marker: one token = one pending subtree; `cons` pushes a token, `nil`/`iend` pop one, other glyphs
leave the count alone; the scan stops as soon as no token is left.  By `HvdH.pendFold_enc` (the
counter returns to `0` exactly at the end of a value) and `HvdH.pendFold_take_pos` (it is positive on
every proper prefix) this is precisely after `v.enc` has been consumed.

This file assembles the `WordR` statement: `dropValue_scan_body` (one scan iteration),
`Work.Kernel.dropValueLoopLe` (unrolling), `Work.Kernel.dropValuePreEval` (the six setup steps).
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-! ## Component lemmas for the scan states -/

/-- `pendStep` does nothing except on `cons`, `nil`, `iend`. -/
theorem dropValue_scan_pendStep_of_ne (g : Glyph) (p : ℕ) (h1 : g ≠ .cons) (h2 : g ≠ .nil)
    (h3 : g ≠ .iend) : pendStep g p = p := by
  cases g <;> simp_all [pendStep]

theorem dropValue_scan_push_stk (X : State) (k : Stk) (r : Reg) :
    (State.tPush X k r).stk k = X.reg r :: X.stk k := by
  simp [State.tPush]

theorem dropValue_scan_push_stk_ne (X : State) (k : Stk) (r : Reg) {j : Stk} (h : j ≠ k) :
    (State.tPush X k r).stk j = X.stk j := by
  simp [State.tPush, h]

theorem dropValue_scan_push_reg (X : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPush X k r).reg r' = X.reg r' := by
  simp [State.tPush]

theorem dropValue_scan_pop_stk_same (X : State) (k : Stk) (r : Reg) :
    (State.tPop X k r).stk k = (X.stk k).tail := by
  simp [State.tPop]

theorem dropValue_scan_pop_stk_ne (X : State) (k : Stk) (r : Reg) {j : Stk} (h : j ≠ k) :
    (State.tPop X k r).stk j = X.stk j := by
  simp [State.tPop, h]

theorem dropValue_scan_pop_reg_same (X : State) (k : Stk) (r : Reg) :
    (State.tPop X k r).reg r = (X.stk k).headD .eos := by
  simp [State.tPop]

theorem dropValue_scan_pop_reg_ne (X : State) (k : Stk) (r : Reg) {r' : Reg} (h : r' ≠ r) :
    (State.tPop X k r).reg r' = X.reg r' := by
  simp [State.tPop, h]

/-- If `X` carries the scan invariant — stack 0 is `t`, stack 1 is the counter region with `q`
tokens above the (unchanged) tail of stack 1 of `s`, all other components as in `s` — then
`set 2 base ;; peek 1 1` turns it into the canonical scan state `dropValue_iter s t q`. -/
theorem dropValue_scan_final_eq (s X : State) (t : List Glyph) (q : ℕ)
    (h0 : X.stk 0 = t) (h1 : X.stk 1 = dropValue_stk1 q (s.stk 1))
    (hk : ∀ k, k ≠ 0 → k ≠ 1 → X.stk k = s.stk k)
    (hr : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → X.reg r = s.reg r)
    (hr3 : X.reg 3 = dropValue_tok) :
    State.tPeek (State.tSet X 2 dropValue_base) 1 1 = dropValue_iter s t q := by
  apply dropValue_state_ext
  · intro r
    rw [dropValue_tPeek_reg, dropValue_compSet_stk, dropValue_compSet_reg]
    by_cases h1' : r = 1
    · subst h1'
      rw [if_pos rfl, h1, dropValue_stk1_headD, dropValue_iter_reg1]
    · rw [if_neg h1']
      by_cases h2' : r = 2
      · subst h2'
        rw [if_pos rfl, dropValue_iter_reg2]
      · rw [if_neg h2']
        by_cases h3' : r = 3
        · subst h3'
          rw [hr3, dropValue_iter_reg3]
        · rw [hr r h1' h2' h3', dropValue_iter_reg s t q r h1' h2' h3']
  · intro j
    rw [dropValue_tPeek_stk, dropValue_compSet_stk]
    by_cases j0 : j = 0
    · subst j0
      rw [h0, dropValue_iter_stk0]
    · by_cases j1 : j = 1
      · subst j1
        rw [h1, dropValue_iter_stk1]
      · rw [hk j j0 j1, dropValue_iter_stk s t q j j0 j1]

/-! ## One scan iteration -/

/-- One iteration of the scan: with `p ≥ 1` tokens on stack 1 and `g :: t` on stack 0,
`dropValue_body` consumes `g`, updates the token count by `HvdH.pendStep g p`, and lands exactly in
the canonical scan state `dropValue_iter s t (pendStep g p)`; cost ≤ 8 (it is 7 when `g` is
`cons`/`nil` and 8 otherwise). -/
theorem dropValue_scan_body (main : Cmd) (s : State) (g : Glyph) (t : List Glyph) (p : ℕ)
    (hp : 1 ≤ p) :
    ∃ c ≤ 8, Eval main dropValue_body (dropValue_iter s (g :: t) p)
      (dropValue_iter s t (pendStep g p)) c := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  set A : State := dropValue_iter s (g :: t) (q + 1) with hA
  have hA_stk0 : A.stk 0 = g :: t := by rw [hA]; exact dropValue_iter_stk0 s (g :: t) (q+1)
  have hA_stk1 : A.stk 1 = dropValue_tok :: dropValue_stk1 q (s.stk 1) := by
    rw [hA, dropValue_iter_stk1, dropValue_stk1_succ]
  have hA_stk : ∀ k, k ≠ 0 → k ≠ 1 → A.stk k = s.stk k := by
    intro k h0 h1; rw [hA]; exact dropValue_iter_stk s (g :: t) (q+1) k h0 h1
  have hA_reg : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → A.reg r = s.reg r := by
    intro r h1 h2 h3; rw [hA]; exact dropValue_iter_reg s (g :: t) (q+1) r h1 h2 h3
  have hA_reg3 : A.reg 3 = dropValue_tok := by rw [hA]; exact dropValue_iter_reg3 s (g :: t) (q+1)
  set A1 : State := State.tPop A 1 2 with hA1
  have hpop1 : Eval main (.pop 1 2) A A1 1 := by rw [hA1]; exact Eval.pop 1 2 A
  have hA1_stk0 : A1.stk 0 = g :: t := by
    rw [hA1, dropValue_scan_pop_stk_ne A 1 2 (by decide : ¬ ((0 : Stk) = 1)), hA_stk0]
  have hA1_stk1 : A1.stk 1 = dropValue_stk1 q (s.stk 1) := by
    rw [hA1, dropValue_scan_pop_stk_same, hA_stk1, List.tail_cons]
  have hA1_stk : ∀ k, k ≠ 0 → k ≠ 1 → A1.stk k = s.stk k := by
    intro k h0 h1; rw [hA1, dropValue_scan_pop_stk_ne A 1 2 h1]; exact hA_stk k h0 h1
  have hA1_reg : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → A1.reg r = s.reg r := by
    intro r h1 h2 h3; rw [hA1, dropValue_scan_pop_reg_ne A 1 2 h2]; exact hA_reg r h1 h2 h3
  have hA1_reg3 : A1.reg 3 = dropValue_tok := by
    rw [hA1, dropValue_scan_pop_reg_ne A 1 2 (by decide : ¬ ((3 : Reg) = 2)), hA_reg3]
  set A2 : State := State.tPop A1 0 2 with hA2
  have hpop2 : Eval main (.pop 0 2) A1 A2 1 := by rw [hA2]; exact Eval.pop 0 2 A1
  have hA2_stk0 : A2.stk 0 = t := by
    rw [hA2, dropValue_scan_pop_stk_same, hA1_stk0, List.tail_cons]
  have hA2_stk1 : A2.stk 1 = dropValue_stk1 q (s.stk 1) := by
    rw [hA2, dropValue_scan_pop_stk_ne A1 0 2 (by decide : ¬ ((1 : Stk) = 0)), hA1_stk1]
  have hA2_stk : ∀ k, k ≠ 0 → k ≠ 1 → A2.stk k = s.stk k := by
    intro k h0 h1; rw [hA2, dropValue_scan_pop_stk_ne A1 0 2 h0]; exact hA1_stk k h0 h1
  have hA2_reg : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → A2.reg r = s.reg r := by
    intro r h1 h2 h3; rw [hA2, dropValue_scan_pop_reg_ne A1 0 2 h2]; exact hA1_reg r h1 h2 h3
  have hA2_reg3 : A2.reg 3 = dropValue_tok := by
    rw [hA2, dropValue_scan_pop_reg_ne A1 0 2 (by decide : ¬ ((3 : Reg) = 2)), hA1_reg3]
  have hA2_reg2 : A2.reg 2 = g := by
    rw [hA2, dropValue_scan_pop_reg_same, hA1_stk0, List.headD_cons]
  have hset : ∀ (X : State),
      Eval main (.set 2 dropValue_base) X (State.tSet X 2 dropValue_base) 1 :=
    fun X => Eval.set 2 dropValue_base X
  have hpeek : ∀ (X : State),
      Eval main (.peek 1 1) (State.tSet X 2 dropValue_base)
        (State.tPeek (State.tSet X 2 dropValue_base) 1 1) 1 :=
    fun X => Eval.peek 1 1 (State.tSet X 2 dropValue_base)
  rcases eq_or_ne g .cons with hc | hc
  · -- `cons`: two tokens are pushed
    subst hc
    set X : State := State.tPush (State.tPush A2 1 3) 1 3 with hX
    have hX_stk0 : X.stk 0 = t := by
      rw [hX, dropValue_scan_push_stk_ne (State.tPush A2 1 3) 1 3 (by decide : ¬ ((0 : Stk) = 1)),
        dropValue_scan_push_stk_ne A2 1 3 (by decide : ¬ ((0 : Stk) = 1)), hA2_stk0]
    have hX_stk1 : X.stk 1 = dropValue_stk1 (pendStep .cons (q+1)) (s.stk 1) := by
      rw [hX, dropValue_scan_push_stk, dropValue_scan_push_stk, dropValue_scan_push_reg, hA2_reg3,
        hA2_stk1]
      simp only [show pendStep Glyph.cons (q+1) = q + 1 + 1 from rfl, dropValue_stk1_succ]
    have hX_stk : ∀ k, k ≠ 0 → k ≠ 1 → X.stk k = s.stk k := by
      intro k h0 h1
      rw [hX, dropValue_scan_push_stk_ne (State.tPush A2 1 3) 1 3 h1,
        dropValue_scan_push_stk_ne A2 1 3 h1, hA2_stk k h0 h1]
    have hX_reg : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → X.reg r = s.reg r := by
      intro r h1 h2 h3
      rw [hX, dropValue_scan_push_reg, dropValue_scan_push_reg]; exact hA2_reg r h1 h2 h3
    have hX_reg3 : X.reg 3 = dropValue_tok := by
      rw [hX, dropValue_scan_push_reg, dropValue_scan_push_reg]; exact hA2_reg3
    have hchain : Eval main dropValue_chain A2 X 3 := by
      rw [hX]
      exact Eval.iteT hA2_reg2
        (Eval.seq (Eval.push 1 3 A2) (Eval.push 1 3 (State.tPush A2 1 3)))
    have hfin : State.tPeek (State.tSet X 2 dropValue_base) 1 1
        = dropValue_iter s t (pendStep .cons (q+1)) :=
      dropValue_scan_final_eq s X t (pendStep .cons (q+1)) hX_stk0 hX_stk1 hX_stk hX_reg hX_reg3
    refine ⟨7, by decide, ?_⟩
    rw [← hfin]
    exact Eval.seq hpop1 (Eval.seq hpop2 (Eval.seq hchain (Eval.seq (hset X) (hpeek X))))
  rcases eq_or_ne g .nil with hn | hn
  · -- `nil`: the token is consumed
    subst hn
    have hq : (q + 1) - 1 = q := by omega
    have hnreg : A2.reg 2 ≠ Glyph.cons := by rw [hA2_reg2]; decide
    have hfin : State.tPeek (State.tSet A2 2 dropValue_base) 1 1
        = dropValue_iter s t (pendStep .nil (q+1)) := by
      rw [show pendStep Glyph.nil (q+1) = q from by rw [pendStep_nil]; exact hq]
      exact dropValue_scan_final_eq s A2 t q hA2_stk0 hA2_stk1 hA2_stk hA2_reg hA2_reg3
    have hchain : Eval main dropValue_chain A2 A2 3 := by
      exact Eval.iteF hnreg (Eval.iteT hA2_reg2 (Eval.skip A2))
    refine ⟨7, by decide, ?_⟩
    rw [← hfin]
    exact Eval.seq hpop1 (Eval.seq hpop2 (Eval.seq hchain (Eval.seq (hset A2) (hpeek A2))))
  rcases eq_or_ne g .iend with hi | hi
  · -- `iend`: the token is consumed
    subst hi
    have hq : (q + 1) - 1 = q := by omega
    have hnreg : A2.reg 2 ≠ Glyph.cons := by rw [hA2_reg2]; decide
    have hnnil : A2.reg 2 ≠ Glyph.nil := by rw [hA2_reg2]; decide
    have hfin : State.tPeek (State.tSet A2 2 dropValue_base) 1 1
        = dropValue_iter s t (pendStep .iend (q+1)) := by
      rw [show pendStep Glyph.iend (q+1) = q from by rw [pendStep_iend]; exact hq]
      exact dropValue_scan_final_eq s A2 t q hA2_stk0 hA2_stk1 hA2_stk hA2_reg hA2_reg3
    have hchain : Eval main dropValue_chain A2 A2 4 := by
      exact Eval.iteF hnreg (Eval.iteF hnnil (Eval.iteT hA2_reg2 (Eval.skip A2)))
    refine ⟨8, by decide, ?_⟩
    rw [← hfin]
    exact Eval.seq hpop1 (Eval.seq hpop2 (Eval.seq hchain (Eval.seq (hset A2) (hpeek A2))))
  · -- any other glyph: the token is put back
    set X : State := State.tPush A2 1 3 with hX
    have hstep : pendStep g (q+1) = q + 1 := dropValue_scan_pendStep_of_ne g (q+1) hc hn hi
    have hnreg : A2.reg 2 ≠ Glyph.cons := by rw [hA2_reg2]; exact hc
    have hnnil : A2.reg 2 ≠ Glyph.nil := by rw [hA2_reg2]; exact hn
    have hniend : A2.reg 2 ≠ Glyph.iend := by rw [hA2_reg2]; exact hi
    have hX_stk0 : X.stk 0 = t := by
      rw [hX, dropValue_scan_push_stk_ne A2 1 3 (by decide : ¬ ((0 : Stk) = 1)), hA2_stk0]
    have hX_stk1 : X.stk 1 = dropValue_stk1 (pendStep g (q+1)) (s.stk 1) := by
      rw [hX, dropValue_scan_push_stk, hA2_reg3, hA2_stk1, hstep]
      simp only [dropValue_stk1_succ]
    have hX_stk : ∀ k, k ≠ 0 → k ≠ 1 → X.stk k = s.stk k := by
      intro k h0 h1
      rw [hX, dropValue_scan_push_stk_ne A2 1 3 h1, hA2_stk k h0 h1]
    have hX_reg : ∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → X.reg r = s.reg r := by
      intro r h1 h2 h3
      rw [hX, dropValue_scan_push_reg]; exact hA2_reg r h1 h2 h3
    have hX_reg3 : X.reg 3 = dropValue_tok := by
      rw [hX, dropValue_scan_push_reg]; exact hA2_reg3
    have hchain : Eval main dropValue_chain A2 X 4 := by
      rw [hX]
      exact Eval.iteF hnreg (Eval.iteF hnnil (Eval.iteF hniend (Eval.push 1 3 A2)))
    have hfin : State.tPeek (State.tSet X 2 dropValue_base) 1 1
        = dropValue_iter s t (pendStep g (q+1)) :=
      dropValue_scan_final_eq s X t (pendStep g (q+1)) hX_stk0 hX_stk1 hX_stk hX_reg hX_reg3
    refine ⟨8, by decide, ?_⟩
    rw [← hfin]
    exact Eval.seq hpop1 (Eval.seq hpop2 (Eval.seq hchain (Eval.seq (hset X) (hpeek X))))

/-! ## Index facts for the scan along `v.enc` -/

/-- For a nonempty list, the head (as `headD`) consed to the tail gives the list back. -/
theorem dropValue_scan_headD_tail (l : List Glyph) (h : l ≠ []) :
    (l.headD dropValue_base) :: l.tail = l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- Splitting `l.drop i` into head and the next drop. -/
theorem dropValue_scan_drop_cons (l : List Glyph) (i : ℕ) (h : i < l.length) :
    l.drop i = (l.drop i).headD dropValue_base :: l.drop (i+1) := by
  have hne : l.drop i ≠ [] := by
    intro h0; rw [List.drop_eq_nil_iff] at h0; omega
  conv_lhs => rw [← dropValue_scan_headD_tail (l.drop i) hne]
  rw [List.tail_drop]

/-- One step of the pending-counter along `l`: appending the next glyph to the prefix `l.take i`
advances `pendFold` by `pendStep` of that glyph. -/
theorem dropValue_scan_pendFold_take_succ (l : List Glyph) (k i : ℕ) (h : i < l.length) :
    pendFold (l.take (i+1)) k
      = pendStep ((l.drop i).headD dropValue_base) (pendFold (l.take i) k) := by
  have h1 : l.take (i+1) = l.take i ++ [l[i]] := (List.take_append_getElem h).symm
  have h2 : (l.drop i).headD dropValue_base = l[i] := by
    rw [List.drop_eq_getElem_cons h]
    exact List.headD_cons
  rw [h1, h2, pendFold_append, pendFold_cons, pendFold_nil]

/-! ## `drop` -/

/-- `import Submission.Work.Kernel.Raw` and `Submission.Work.Kernel.Pend`, work in `namespace Work.Kernel`.  `HvdH.pendStep`/`HvdH.pendFold`/`HvdH.pendFold_enc`/`HvdH.pendFold_take_pos` are the pending-subtree counter facts needed to know when the top value of stack 0 has been fully consumed.  Helpers in this file must be named with the prefix `dropValue_`. -/
theorem dropValue : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ main : HvdH.Cmd, HvdH.WordR main prog (fun vs => vs ≠ [])
    (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
    (fun vs => K * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) := by
  refine ⟨dropValue_prog, 9, ?_⟩
  intro main vs hvs s R hR
  rcases vs with _ | ⟨v, rest⟩
  · exact absurd rfl hvs
  let rest' : List Glyph := encs rest ++ R
  have hR' : s.stk 0 = v.enc ++ rest' := by
    dsimp only [rest']
    rw [hR, encs_cons, List.append_assoc]
  let f : ℕ → State := fun i =>
    dropValue_iter s (v.enc.drop i ++ rest') (pendFold (v.enc.take i) 1)
  have hf0 : f 0 = dropValue_iter s (s.stk 0) 1 := by
    show dropValue_iter s (v.enc ++ rest') 1 = dropValue_iter s (s.stk 0) 1
    rw [hR']
  have hpre : Eval main dropValue_pre s (f 0) 6 := by
    rw [hf0]
    exact dropValuePreEval main s
  have hstep : ∀ i < vsz v,
      (f i).reg 1 = dropValue_tok ∧ ∃ c' ≤ 8, Eval main dropValue_body (f i) (f (i+1)) c' := by
    intro i hi
    have hlt : i < v.enc.length := by simpa [vsz] using hi
    have hpos : 1 ≤ pendFold (v.enc.take i) 1 := by
      have := pendFold_take_pos v i hi
      omega
    set g : Glyph := (v.enc.drop i).headD dropValue_base with hg
    have hdrop : v.enc.drop i = g :: v.enc.drop (i+1) := by
      rw [hg]
      exact dropValue_scan_drop_cons v.enc i hlt
    constructor
    · simp only [f]
      exact dropValue_iter_reg1_of_pos _ _ _ hpos
    · obtain ⟨c', hc'le, hev⟩ :=
        dropValue_scan_body main s g (v.enc.drop (i+1) ++ rest') (pendFold (v.enc.take i) 1) hpos
      refine ⟨c', hc'le, ?_⟩
      have hs : f i = dropValue_iter s (g :: (v.enc.drop (i+1) ++ rest'))
          (pendFold (v.enc.take i) 1) := by
        simp only [f, hdrop, List.cons_append]
      have ht : dropValue_iter s (v.enc.drop (i+1) ++ rest')
          (pendStep g (pendFold (v.enc.take i) 1)) = f (i+1) := by
        simp only [f, hg, dropValue_scan_pendFold_take_succ v.enc 1 i hlt]
      rw [hs, ← ht]
      exact hev
  have hfn : pendFold (v.enc.take (vsz v)) 1 = 0 := by
    rw [show v.enc.take (vsz v) = v.enc from by simpa [vsz] using List.take_length (l := v.enc)]
    simpa using pendFold_enc v 0
  have hstop : (f (vsz v)).reg 1 ≠ dropValue_tok := by
    simp only [f]
    rw [hfn, dropValue_iter_reg1_of_zero]
    decide
  obtain ⟨m, hmle, hloop⟩ :=
    dropValueLoopLe main 1 dropValue_tok dropValue_body 8 (vsz v) f hstep hstop
  have hfn0 : (f (vsz v)).stk 0 = rest' := by
    simp only [f, dropValue_iter_stk0]
    rw [show v.enc.drop (vsz v) = [] from by simpa [vsz] using List.drop_length (l := v.enc),
      List.nil_append]
  have hfn1 : (f (vsz v)).stk 1 = dropValue_base :: s.stk 1 := by
    simp only [f, dropValue_iter_stk1]
    rw [show v.enc.take (vsz v) = v.enc from by simpa [vsz] using List.take_length (l := v.enc),
      show pendFold v.enc 1 = 0 from by simpa using pendFold_enc v 0, dropValue_stk1_zero]
  have hpost : Eval main (.pop 1 0) (f (vsz v)) (State.tPop (f (vsz v)) 1 0) 1 := Eval.pop 1 0 _
  have hfnk : ∀ k : Stk, k ≠ 0 → k ≠ 1 → (f (vsz v)).stk k = s.stk k := by
    intro k hk0 hk1
    simp only [f]
    exact dropValue_iter_stk s (v.enc.drop (vsz v) ++ rest')
      (pendFold (v.enc.take (vsz v)) 1) k hk0 hk1
  refine ⟨rest, State.tPop (f (vsz v)) 1 0, 6 + (m + 1), ⟨v, rest, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · unfold dropValue_prog
    exact Eval.seq hpre (Eval.seq hloop hpost)
  · simp only [List.headD_cons]
    omega
  · rw [dropValue_tPop_stk, if_neg (show ¬ ((0 : Stk) = 1) from by decide), hfn0]
  · intro k hk
    rw [dropValue_tPop_stk]
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl, hfn1]
      rfl
    · rw [if_neg hk1]
      exact hfnk k hk hk1

end Work.Kernel
