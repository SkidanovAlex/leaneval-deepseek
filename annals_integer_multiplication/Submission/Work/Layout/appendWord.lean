import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.appendDefs
import Submission.Work.Layout.appendPhase1
import Submission.Work.Layout.appendPhase2

namespace Work.Layout

open HvdH

/-! ## Small helpers -/

/-- `pushG k c` pushes the constant glyph `c` on stack `k` and touches nothing else. -/
theorem appendP_pushG_ev {main : Cmd} (k : Stk) (c : Glyph) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main (pushG k c) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧ s'.stk k = c :: X k ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  have h1 : Ev main (.set rB c) ⟨g, X⟩ ⟨Function.update g rB c, X⟩ 1 := ev_set' main rB c g X
  have h2 : Ev main (.push k rB) ⟨Function.update g rB c, X⟩
      ⟨Function.update g rB c, Function.update X k (c :: X k)⟩ 1 := by
    simpa using ev_push' main k rB (Function.update g rB c) X
  have h3 : Ev main (pushG k c) ⟨g, X⟩
      ⟨Function.update g rB c, Function.update X k (c :: X k)⟩ 2 := by
    unfold pushG
    simp only [seqs]
    exact Ev.seq' h1 h2 (le_rfl)
  refine ⟨⟨Function.update g rB c, Function.update X k (c :: X k)⟩, 2, h3, le_rfl, ?_, ?_⟩
  · simp
  · intro j hj
    simp only [stk_mk]
    rw [Function.update_of_ne hj]

/-- `pop k r` drops the top glyph of stack `k`. -/
theorem appendP_pop_ev {main : Cmd} (k : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main (.pop k r) ⟨g, X⟩ s' n ∧ n ≤ 1 ∧ s'.stk k = (X k).tail ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  refine ⟨⟨Function.update g r ((X k).headD Glyph.eos), Function.update X k (X k).tail⟩, 1,
    ev_pop' main k r g X, le_rfl, ?_, ?_⟩
  · simp
  · intro j hj
    simp only [stk_mk]
    rw [Function.update_of_ne hj]

/-- Glue for the final state: `lstEnc` followed by the frame of stack 0. -/
theorem appendP_lstEnc_encs (zs : List Val) (rest : List Val) (R : List Glyph) :
    lstEnc zs ++ (encs rest ++ R) = encs (ofList zs :: rest) ++ R := by
  rw [encs_ofList, List.append_assoc]

/-! ## `LayoutLib.append` -/

/-- **`LayoutLib.append`**: move the elements of `ofList xs` one by one to a scratch stack (they arrive
in reverse order), then cons them (from the top, i.e. last element first) onto `ofList ys`.  Only `xs`
is traversed, hence the cost bound. -/
theorem appendWord : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs ys : List Val), WordR main p
    (fun vs => ∃ rest, vs = ofList xs :: ofList ys :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: ofList ys :: rest ∧ out = ofList (xs ++ ys) :: rest)
    (fun _ => K * (vsz (ofList xs) + 1)) := by
  refine ⟨appendP, 200, ?_⟩
  intro main xs ys vs hpre s R hR
  obtain ⟨rest, rfl⟩ := hpre
  set C0 : List Glyph := encs rest ++ R with hC0
  -- content of stack 0 at the start
  have hX0 : s.stk 0 = (ofList xs).enc ++ ((ofList ys).enc ++ C0) := by
    rw [hR, hC0]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  -- phase 0: move `ofList xs` aside to stack 2
  obtain ⟨s₁, n₁, hmv1, hn1, h10, h12, h13, h14, h1f⟩ :=
    mvVal_ev_all (main := main) (a := 0) (b := 2) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s.reg) (X := s.stk) (v := ofList xs) (A := (ofList ys).enc ++ C0) (B := s.stk 2)
      hX0 rfl
  have hs1 : s₁.stk 1 = s.stk 1 := h1f 1 (by decide) (by decide) (by decide) (by decide)
  -- push the sentinel that delimits the element region on stack 1
  obtain ⟨s₂, n₂, hpush, hn2, hs21, hs2f⟩ := appendP_pushG_ev (main := main) 1 gSent s₁.reg s₁.stk
  have hs20 : s₂.stk 0 = s₁.stk 0 := hs2f 0 (by decide)
  have hs22 : s₂.stk 2 = s₁.stk 2 := hs2f 2 (by decide)
  have hs23 : s₂.stk 3 = s₁.stk 3 := hs2f 3 (by decide)
  have hs24 : s₂.stk 4 = s₁.stk 4 := hs2f 4 (by decide)
  -- phase 1: unpack `ofList xs` from stack 2 onto stack 1
  obtain ⟨s₃, n₃, hp1, hn3, hs31, hs32, hs33, hs34, hs3f⟩ :=
    appendPhase1 (main := main) (zs := xs) (mzs := [])
      (C1 := s.stk 1) (C2 := s.stk 2) (C3 := s.stk 3) (C4 := s.stk 4) s₂.reg s₂.stk
      (by simp only [hs21, hs1, elsEnc_nil]) (by simp only [hs22, h12, ofList_enc])
      (by simp only [hs23, h13]) (by simp only [hs24, h14])
  have hs30 : s₃.stk 0 = s₂.stk 0 := hs3f 0 (by decide) (by decide) (by decide) (by decide)
  -- phase 2: cons the elements back onto `ofList ys`
  obtain ⟨s₄, n₄, hp2, hn4, hs40, hs41, hs43, hs44, hs4f⟩ :=
    appendPhase2 (main := main) (mzs := xs.reverse) (p := []) (ys := ys) (C0 := C0)
      (C1 := s.stk 1) (C3 := s.stk 3) (C4 := s.stk 4) s₃.reg s₃.stk
      (by simp only [hs30, hs20, h10, ofList_enc, List.nil_append])
      (by simp only [hs31, List.append_nil])
      (by simp only [hs33, h13]) (by simp only [hs34, h14])
  -- pop the sentinel again
  obtain ⟨s₅, n₅, hpop, hn5, hs51, hs5f⟩ := appendP_pop_ev (main := main) 1 rA s₄.reg s₄.stk
  -- the whole word
  have hEv : Ev main appendP s s₅ (n₁ + n₂ + n₃ + n₄ + n₅) := by
    have e4 : Ev main (Cmd.seq p2 (Cmd.pop 1 rA)) s₃ s₅ (n₄ + n₅) :=
      Ev.seq' hp2 hpop (le_rfl)
    have e3 : Ev main (Cmd.seq p1 (Cmd.seq p2 (Cmd.pop 1 rA))) s₂ s₅ (n₃ + n₄ + n₅) :=
      Ev.seq' hp1 e4 (by omega)
    have e2 : Ev main (Cmd.seq (pushG 1 gSent) (Cmd.seq p1 (Cmd.seq p2 (Cmd.pop 1 rA)))) s₁ s₅
        (n₂ + n₃ + n₄ + n₅) := Ev.seq' hpush e3 (by omega)
    have e1 : Ev main (Cmd.seq (mvVal 0 2 3 4)
        (Cmd.seq (pushG 1 gSent) (Cmd.seq p1 (Cmd.seq p2 (Cmd.pop 1 rA))))) s s₅
        (n₁ + n₂ + n₃ + n₄ + n₅) := Ev.seq' hmv1 e2 (by omega)
    simpa only [appendP, seqs] using e1
  obtain ⟨n, hEval, hnle⟩ := hEv
  refine ⟨ofList (xs ++ ys) :: rest, s₅, n, ⟨rest, rfl, rfl⟩, hEval, ?_, ?_, ?_⟩
  · have hrev : vsz (ofList xs.reverse) = vsz (ofList xs) := vsz_ofList_reverse_ap xs
    show n ≤ 200 * (vsz (ofList xs) + 1)
    omega
  · simp only [hs5f 0 (by decide), hs40, List.reverse_reverse, List.append_nil, hC0]
    exact appendP_lstEnc_encs (xs ++ ys) rest R
  · intro k hk0
    by_cases hk1 : k = 1
    · subst hk1
      simp only [hs51, hs41, List.tail_cons]
    by_cases hk2 : k = 2
    · subst hk2
      simp only [hs5f 2 (by decide), hs4f 2 (by decide) (by decide) (by decide) (by decide), hs32]
    by_cases hk3 : k = 3
    · subst hk3
      simp only [hs5f 3 (by decide), hs43]
    by_cases hk4 : k = 4
    · subst hk4
      simp only [hs5f 4 (by decide), hs44]
    · have h5 : s₅.stk k = s₄.stk k := hs5f k hk1
      have h4 : s₄.stk k = s₃.stk k := hs4f k hk0 hk1 hk3 hk4
      have h3 : s₃.stk k = s₂.stk k := hs3f k hk1 hk2 hk3 hk4
      have h2 : s₂.stk k = s₁.stk k := hs2f k hk1
      have h1 : s₁.stk k = s.stk k := h1f k hk0 hk2 hk3 hk4
      simp only [h5, h4, h3, h2, h1]

end Work.Layout
