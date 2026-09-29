import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.incBitsListAPI
import Submission.Work.IntLib.incBitsFinal_eval_false
import Submission.Work.IntLib.incBitsFinal_eval_other
import Submission.Work.IntLib.incBits_loop_eval
import Submission.Work.IntLib.eval_mvRev

/-!
# `incBits`: end-to-end specification (area IntLib)

`Work.IntLib.incBits k T S TS rr rs` increments the least-significant-first bit region of stack `k`
(delimited by its frame marker `T`), using stack `S` (whose frame marker is `TS`) as scratch, and
restores `S` to its original content.

The piece lemmas are `Work.IntLib.incBits_loop_eval` (the carry loop, cost `6 * j + 8`),
`Work.IntLib.incBitsFinal_eval_false` / `incBitsFinal_eval_other` (the final carry step) and
`Work.IntLib.eval_mvRev` (moving the result region back from `S` to `k`, cost
`6 * (len + 1) + 10`).  This file records the list-level bookkeeping (splitting `l` into
`replicate j true ++ r` with `r` empty or starting with `false`) and assembles the pieces.

The statement `Work.IntLib.incBitsSpec` is the lemma requested by the `intLib` area: it is what the
long-division word uses to propagate the "+1" carry of a quotient.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Splitting a bit list after its leading `true`s -/

/-- Every bit list is `replicate j true ++ r` where `r` is either empty or begins with `false`:
`j` is the length of the initial run of `true`s. -/
private theorem exists_replicate_true_append (l : List Bool) :
    ∃ (j : ℕ) (r : List Bool), l = List.replicate j true ++ r ∧
      (r = [] ∨ ∃ r', r = false :: r') := by
  induction l with
  | nil => exact ⟨0, [], rfl, Or.inl rfl⟩
  | cons b xs ih =>
    obtain ⟨j, r, hl, hr⟩ := ih
    cases b with
    | false => exact ⟨0, false :: xs, rfl, Or.inr ⟨xs, rfl⟩⟩
    | true =>
      refine ⟨j + 1, r, ?_, hr⟩
      rw [List.replicate_succ, List.cons_append, ← hl]

/-- `incBitsList` of an initial run of `true`s: it becomes a run of `false`s plus a final carry. -/
private theorem incBitsList_replicate_true (j : ℕ) :
    incBitsList (List.replicate j true) = List.replicate j false ++ [true] := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, incBitsList, ih]

/-- `incBitsList` after an initial run of `true`s, when the first remaining bit is `false`. -/
private theorem incBitsList_replicate_true_false_cons (j : ℕ) (r' : List Bool) :
    incBitsList (List.replicate j true ++ false :: r') = List.replicate j false ++ true :: r' := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, incBitsList, ih]

/-! ## The end-to-end specification -/

theorem incBitsSpec (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (S : HvdH.Stk)
    (TS : HvdH.Glyph) (rr rs : HvdH.Reg) (l : List Bool) (bk bsk : List HvdH.Glyph)
    (s : HvdH.State) (hT : ∀ b : Bool, HvdH.Glyph.bit b ≠ T)
    (hTS : ∀ b : Bool, HvdH.Glyph.bit b ≠ TS) (hrr : rr ≠ rs)
    (hk : s.stk k = Work.IntLib.bitsG l ++ T :: bk) (hS : s.stk k = s.stk k) (hS : s.stk S = bsk) (hne : k ≠ S) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.incBits k T S TS rr rs) s s' n ∧
      n ≤ 20 * (l.length + 1) + 40 ∧
      s'.stk k = Work.IntLib.bitsG (Work.IntLib.incBitsList l) ++ T :: bk ∧
      s'.stk S = bsk ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ S → s'.stk j = s.stk j := by
  obtain ⟨j, r, hl, hr⟩ := exists_replicate_true_append l
  have hk' : s.stk k = bitsG (List.replicate j true ++ r) ++ T :: bk := by rw [← hl]; exact hk
  -- the three prefix commands: `set rr TS`, `push S rr`, `set rr (bit true)`
  set s1 : State := s.updReg rr TS with hs1
  set s2 : State := s1.tPush S rr with hs2
  set s3 : State := s2.updReg rr (Glyph.bit true) with hs3
  have e1 : Eval main (.set rr TS) s s1 1 := by rw [hs1]; exact Eval.set_eq
  have e2 : Eval main (.push S rr) s1 s2 1 := by rw [hs2]; exact Eval.push S rr s1
  have e3 : Eval main (.set rr (Glyph.bit true)) s2 s3 1 := by rw [hs3]; exact Eval.set_eq
  have h1k : s1.stk k = bitsG (List.replicate j true ++ r) ++ T :: bk := by
    rw [hs1, State.updReg_stk]; exact hk'
  have h2k : s2.stk k = bitsG (List.replicate j true ++ r) ++ T :: bk := by
    rw [hs2, State.tPush, State.updStk_apply, ite_eq_right hne]; exact h1k
  have h2S : s2.stk S = TS :: bsk := by
    rw [hs2, State.tPush, State.updStk_same, hs1, State.updReg_apply, ite_eq_left rfl,
      State.updReg_stk, hS]
  have h3k : s3.stk k = bitsG (List.replicate j true ++ r) ++ T :: bk := by
    rw [hs3, State.updReg_stk]; exact h2k
  have h3S : s3.stk S = TS :: bsk := by rw [hs3, State.updReg_stk]; exact h2S
  have h3reg : s3.reg rr = Glyph.bit true := by rw [hs3, State.updReg_apply, ite_eq_left rfl]
  have h3fr : ∀ j' : Stk, j' ≠ k → j' ≠ S → s3.stk j' = s.stk j' := by
    intro j' hj hj'
    rw [hs3, State.updReg_stk, hs2, State.tPush, State.updStk_apply,
      ite_eq_right (fun h : j' = S => hj' h), hs1, State.updReg_stk]
  -- the carry loop
  obtain ⟨s4, n4, hev4, hn4, h4k, h4S, h4reg, h4fr⟩ :=
    incBits_loop_eval main k T S rr rs bk hne hrr hT j r (TS :: bsk) s3 h3k h3S h3reg hr
  rcases hr with hr0 | ⟨r', hr'⟩
  · -- case `r = []`: every bit was `true`, the carry is a fresh `true` on top of `S`
    subst hr0
    have h4kA : s4.stk k = T :: bk := by simpa using h4k
    have h4regA : s4.reg rr ≠ Glyph.bit false := by
      rw [h4reg, ite_eq_left rfl]
      exact fun h => hT false h.symm
    obtain ⟨s5, n5, hev5, hn5, h5k, h5S, h5fr⟩ :=
      incBitsFinal_eval_other main k T S rr rs bk
        (List.replicate j (Glyph.bit false) ++ TS :: bsk) s4 hne h4kA h4S h4regA
    set l0 : List Glyph := Glyph.bit true :: List.replicate j (Glyph.bit false) with hl0def
    have h5S' : s5.stk S = l0 ++ TS :: bsk := by
      rw [h5S, hl0def, List.cons_append]
    have hl0rev : l0.reverse = bitsG (incBitsList l) := by
      rw [hl0def, List.reverse_cons, List.reverse_replicate, hl, List.append_nil,
        incBitsList_replicate_true]
      simp [bitsG, List.map_append, List.map_replicate]
    have hmvT : ∀ g ∈ l0, g ≠ TS := by
      intro g hg
      have hg' : g ∈ l0.reverse := List.mem_reverse.mpr hg
      rw [hl0rev] at hg'
      exact bitsG_ne_of_bit_ne hTS g hg'
    obtain ⟨s6, n6, hev6, hn6, h6S, h6k, h6fr⟩ :=
      eval_mvRev main S TS k T rs l0 bsk bk s5 hmvT h5S' h5k (Ne.symm hne)
    have hlen : l.length = j := by rw [hl, List.append_nil, List.length_replicate]
    have hl0len : l0.length = j + 1 := by rw [hl0def, List.length_cons, List.length_replicate]
    refine ⟨s6, 1 + (1 + (1 + (n4 + (n5 + n6)))), ?_, ?_, ?_, ?_, ?_⟩
    · exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq hev4 (Eval.seq hev5 hev6))))
    · omega
    · rw [h6k, hl0rev]
    · exact h6S
    · intro j' hj1 hj2
      rw [h6fr j' hj2 hj1, h5fr j' hj1 hj2, h4fr j' hj1 hj2, h3fr j' hj1 hj2]
  · -- case `r = false :: r'`: the carry stops at the first `false` bit
    subst hr'
    have h4kB : s4.stk k = Glyph.bit false :: (bitsG r' ++ T :: bk) := by
      rw [h4k]; rfl
    have h4regB : s4.reg rr = Glyph.bit false := by rw [h4reg]; simp
    obtain ⟨s5, n5, hev5, hn5, h5k, h5S, h5fr⟩ :=
      incBitsFinal_eval_false main k T S rr rs r' bk
        (List.replicate j (Glyph.bit false) ++ TS :: bsk) s4 hT hne h4kB h4S h4regB
    set l0 : List Glyph := (bitsG r').reverse ++ Glyph.bit true :: List.replicate j (Glyph.bit false)
      with hl0def
    have h5S' : s5.stk S = l0 ++ TS :: bsk := by
      rw [h5S, hl0def, List.append_assoc, List.cons_append]
    have hl0rev : l0.reverse = bitsG (incBitsList l) := by
      rw [hl0def, List.reverse_append, List.reverse_cons, List.reverse_reverse,
        List.reverse_replicate, hl, incBitsList_replicate_true_false_cons]
      simp [bitsG, List.map_append, List.map_replicate, List.append_assoc]
    have hmvT : ∀ g ∈ l0, g ≠ TS := by
      intro g hg
      have hg' : g ∈ l0.reverse := List.mem_reverse.mpr hg
      rw [hl0rev] at hg'
      exact bitsG_ne_of_bit_ne hTS g hg'
    obtain ⟨s6, n6, hev6, hn6, h6S, h6k, h6fr⟩ :=
      eval_mvRev main S TS k T rs l0 bsk bk s5 hmvT h5S' h5k (Ne.symm hne)
    have hlen : l.length = j + 1 + r'.length := by
      rw [hl, List.length_append, List.length_replicate, List.length_cons]; omega
    have hl0len : l0.length = r'.length + 1 + j := by
      rw [hl0def, List.length_append, List.length_cons, List.length_replicate,
        List.length_reverse]
      simp only [bitsG, List.length_map]
      omega
    refine ⟨s6, 1 + (1 + (1 + (n4 + (n5 + n6)))), ?_, ?_, ?_, ?_, ?_⟩
    · exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq hev4 (Eval.seq hev5 hev6))))
    · omega
    · rw [h6k, hl0rev]
    · exact h6S
    · intro j' hj1 hj2
      rw [h6fr j' hj2 hj1, h5fr j' hj1 hj2, h4fr j' hj1 hj2, h3fr j' hj1 hj2]

end Work.IntLib
