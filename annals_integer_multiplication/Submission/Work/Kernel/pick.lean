import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Kernel.dropValue
import Submission.Work.Kernel.pickDefs

namespace Work.Kernel

open HvdH

/-! ## Helper lemmas for `pick`

`pickProg k` (defined in `Submission/Work/Kernel/pickDefs.lean`)

1. saves the top `k` values on stack 1 (`moveTop k 0 1`), exposing the `k`-th value;
2. duplicates the exposed value (`dup_prog`);
3. moves one copy aside on stack 4 (`mvVal 0 4 2 3`);
4. restores the `k` saved values (`moveTop k 1 0`);
5. puts the copy back on top (`mvVal 4 0 2 3`).
-/

/-- Appending one value to a value list, on encodings. -/
theorem pick_encs_snoc (l : List Val) (y : Val) (Rb : List Glyph) :
    encs l ++ (y.enc ++ Rb) = encs (l ++ [y]) ++ Rb := by
  rw [encs_append, encs_cons, encs_nil]
  simp [List.append_assoc]

/-- Splitting `vs.drop k` at its head, written with `getD` (the form in `Post`). -/
theorem pick_drop_eq (vs : List Val) (k : ℕ) (h : k < vs.length) :
    vs.drop k = vs.getD k Val.nil :: vs.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem vs Val.nil h]

/-- `vs.take (k+1)` is `vs.take k` with the `k`-th value appended. -/
theorem pick_take_eq (vs : List Val) (k : ℕ) (h : k < vs.length) :
    vs.take (k + 1) = vs.take k ++ [vs.getD k Val.nil] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem vs Val.nil h]
  rfl

/-- The numerical cost inequality used for `pick`. -/
theorem pick_cost_bound (E Sv k : ℕ) :
    32 * E + 32 * k + 80 * Sv + 82 ≤ 112 * (k + 1) * (E + Sv + 1) := by
  nlinarith [Nat.zero_le E, Nat.zero_le Sv, Nat.zero_le k]

/-- `Work.Kernel.moveTop j a b` moves the top `j` values of stack `a` to the top of stack `b`
(the first moved ends deepest), one `Work.Layout.mvVal` at a time, buffering on stacks `2` and `3`
(which are restored); the encodings below the moved block are untouched. -/
theorem pick_moveTop_ev {main : Cmd} {a b : Stk}
    (hab : a ≠ b) (ha2 : a ≠ (2 : Stk)) (ha3 : a ≠ (3 : Stk))
    (hb2 : b ≠ (2 : Stk)) (hb3 : b ≠ (3 : Stk)) :
    ∀ (j : ℕ) (ys : List Val) (Ra Rb : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      j ≤ ys.length → X a = encs ys ++ Ra → X b = Rb →
      ∃ s' n, Work.Layout.Ev main (moveTop j a b) ⟨g, X⟩ s' n ∧
        n ≤ 16 * (((ys.take j).map vsz).sum + j) + 1 ∧
        s'.stk a = encs (ys.drop j) ++ Ra ∧
        s'.stk b = encs ((ys.take j).reverse) ++ Rb ∧
        s'.stk 2 = X 2 ∧ s'.stk 3 = X 3 ∧
        (∀ k, k ≠ a → k ≠ b → k ≠ (2 : Stk) → k ≠ (3 : Stk) → s'.stk k = X k) := by
  intro j
  induction j with
  | zero =>
    intro ys Ra Rb g X _ ha hb
    refine ⟨⟨g, X⟩, 1, ⟨1, Eval.skip _, le_rfl⟩, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp
    · simpa using ha
    · show X b = encs ((ys.take 0).reverse) ++ Rb
      rw [hb]; rfl
    · intro k _ _ _ _; rfl
  | succ j ih =>
    intro ys Ra Rb g X hlen ha hb
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      have hlen' : j ≤ ys'.length := by simpa using hlen
      have ha' : X a = y.enc ++ (encs ys' ++ Ra) := by
        rw [encs_cons, List.append_assoc] at ha; exact ha
      obtain ⟨s₁, n₁, hE₁, hn₁, ha₁, hb₁, h2₁, h3₁, hf₁⟩ :=
        Work.Layout.mvVal_ev_full (main := main) (a := a) (b := b) (c := 2) (d := 3)
          hab ha2 ha3 hb2 hb3 (by decide) (g := g) (X := X) (v := y)
          (A := encs ys' ++ Ra) (B := Rb) ha' hb
      obtain ⟨s₂, n₂, hE₂, hn₂, ha₂, hb₂, h2₂, h3₂, hf₂⟩ :=
        ih ys' Ra (y.enc ++ Rb) s₁.reg s₁.stk hlen' ha₁ hb₁
      refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Work.Layout.Ev main (Cmd.seq (Work.Layout.mvVal a b 2 3) (moveTop j a b))
          ⟨g, X⟩ s₂ (n₁ + n₂)
        exact Work.Layout.Ev.seq hE₁ hE₂
      · have hB : n₂ ≤ 16 * (((ys'.take j).map vsz).sum + j) + 1 := hn₂
        rw [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
      · rw [ha₂, List.drop_succ_cons]
      · rw [hb₂, List.take_succ_cons, List.reverse_cons]
        exact pick_encs_snoc (List.take j ys').reverse y Rb
      · rw [h2₂, h2₁]
      · rw [h3₂, h3₁]
      · intro k h1 h2 h3 h4
        rw [hf₂ k h1 h2 h3 h4, hf₁ k h1 h2 h3 h4]

/-- `pick` field of `HvdH.KernelLib` (v2/v3).  Imports: `Submission.Work.Kernel.Raw`, `Submission.Work.Kernel.Pend`, and the already-proved marker movers `Submission.Work.Layout.Move` (`Work.Layout.Ev` = bounded `Eval`; `mvVal_ev` moves one value between two stacks in normal order at cost `≤ 16*(vsz v+1)`) — using them saves hours.  Plan: same as `roll` (move the top `k` values aside, expose the `k`-th), but *duplicate* the exposed value before restoring the `k` saved values, so the result is `vs.getD k .nil :: vs`.  Helpers must be named with the prefix `pick_`. -/
theorem pick : ∃ (prog : ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (k : ℕ), HvdH.WordR main (prog k)
    (fun vs => k < vs.length) (fun vs out => out = vs.getD k HvdH.Val.nil :: vs)
    (fun vs => K * (k + 1) * (((vs.take (k + 1)).map HvdH.vsz).sum + 1)) := by
  refine ⟨pickProg, 112, ?_⟩
  intro main k vs hpre s R hR
  set v := vs.getD k Val.nil with hv
  have hlt : k < vs.length := hpre
  have hdrop : vs.drop k = v :: vs.drop (k + 1) := by
    rw [pick_drop_eq vs k hlt, ← hv]
  have htake : vs.take (k + 1) = vs.take k ++ [v] := by
    rw [pick_take_eq vs k hlt, ← hv]
  have hlen : (vs.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hrev4 : ((vs.take k).reverse).length ≤ k := by rw [List.length_reverse, hlen]
  have htake4 : ((vs.take k).reverse).take k = (vs.take k).reverse :=
    List.take_of_length_le hrev4
  have hsum4 : ((((vs.take k).reverse).take k).map vsz).sum = ((vs.take k).map vsz).sum := by
    rw [htake4, List.map_reverse, List.sum_reverse]
  have hvol : encs vs = encs (vs.take k) ++ encs (v :: vs.drop (k + 1)) := by
    conv_lhs => rw [← List.take_append_drop k vs, hdrop]
    rw [encs_append]
  -- step 1: save the top `k` values on stack 1
  obtain ⟨s₁, C₁, hE₁, hC₁, ha₁, hb₁, h2₁, h3₁, hf₁⟩ :=
    pick_moveTop_ev (main := main) (a := 0) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) k vs R (s.stk 1) s.reg s.stk (by omega) hR rfl
  -- step 2: duplicate the exposed value with `dup_prog`
  have hR₁ : s₁.stk 0 = encs (v :: vs.drop (k+1)) ++ R := by rw [ha₁, hdrop]
  obtain ⟨out₂, s₂, n₂, hp₂, hev₂, hc₂, hstk₂, hfr₂⟩ :=
    (dup_prog_wordR main) (v :: vs.drop (k+1)) (by simp) s₁ R hR₁
  obtain ⟨v', rest', hspec, hout₂⟩ := hp₂
  injection hspec with hv' hrest'
  have hout₂' : out₂ = v :: v :: vs.drop (k+1) := by rw [hout₂, ← hv', ← hrest']
  have hc₂' : n₂ ≤ 48 * (vsz v + 1) := by simpa using hc₂
  have hstk₂' : s₂.stk 0 = encs (v :: v :: vs.drop (k+1)) ++ R := by rw [hstk₂, hout₂']
  -- step 3: move one copy aside on stack 4
  have hR₂ : s₂.stk 0 = v.enc ++ (encs (v :: vs.drop (k+1)) ++ R) := by
    rw [hstk₂', encs_cons, List.append_assoc]
  obtain ⟨s₃, n₃, hE₃, hc₃, ha₃, hb₃, h2₃, h3₃, hf₃⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 4) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₂.reg) (X := s₂.stk) (v := v) (A := encs (v :: vs.drop (k+1)) ++ R)
      (B := s₂.stk 4) hR₂ rfl
  -- step 4: restore the `k` saved values
  have hb₁' : s₃.stk 1 = encs ((vs.take k).reverse) ++ s.stk 1 := by
    rw [hf₃ 1 (by decide) (by decide) (by decide) (by decide), hfr₂ 1 (by decide), hb₁]
  have hlen4 : k ≤ ((vs.take k).reverse).length := by rw [List.length_reverse, hlen]
  obtain ⟨s₄, C₄, hE₄, hC₄, ha₄, hb₄, h2₄, h3₄, hf₄⟩ :=
    pick_moveTop_ev (main := main) (a := 1) (b := 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) k ((vs.take k).reverse) (s.stk 1) (s₃.stk 0) s₃.reg s₃.stk
      hlen4 hb₁' rfl
  have hb₄' : s₄.stk 0 = encs (vs.take k) ++ (encs (v :: vs.drop (k+1)) ++ R) := by
    rw [hb₄, htake4, List.reverse_reverse, ha₃]
  -- step 5: put the copy back on top
  have h4₄ : s₄.stk 4 = v.enc ++ s₂.stk 4 := by
    rw [hf₄ 4 (by decide) (by decide) (by decide) (by decide), hb₃]
  obtain ⟨s₅, n₅, hE₅, hc₅, ha₅, hb₅, h2₅, h3₅, hf₅⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 4) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₄.reg) (X := s₄.stk) (v := v) (A := s₂.stk 4) (B := s₄.stk 0) h4₄ rfl
  -- the final content of stack 0
  have hfinal : s₅.stk 0 = encs (v :: vs) ++ R := by
    rw [hb₅, hb₄']
    conv_rhs => rw [encs_cons, hvol]
    simp only [encs_cons, List.append_assoc]
  -- the cost
  have hS : ((vs.take (k + 1)).map vsz).sum = ((vs.take k).map vsz).sum + vsz v := by
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hC₄' : C₄ ≤ 16 * (((vs.take k).map vsz).sum + k) + 1 := by
    rw [hsum4] at hC₄; exact hC₄
  have hTOTAL : C₁ + (48 * (vsz v + 1) + (n₃ + (C₄ + n₅)))
      ≤ 112 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := by
    rw [hS]
    have hb := pick_cost_bound ((vs.take k).map vsz).sum (vsz v) k
    omega
  -- assemble the `Ev` chain
  have hE₂' : Work.Layout.Ev main dup_prog s₁ s₂ (48 * (vsz v + 1)) := ⟨n₂, hev₂, hc₂'⟩
  have h45 : Work.Layout.Ev main
      (Cmd.seq (moveTop k 1 0) (Work.Layout.mvVal 4 0 2 3)) s₃ s₅ (C₄ + n₅) :=
    Work.Layout.Ev.seq hE₄ hE₅
  have h345 : Work.Layout.Ev main
      (Cmd.seq (Work.Layout.mvVal 0 4 2 3)
        (Cmd.seq (moveTop k 1 0) (Work.Layout.mvVal 4 0 2 3))) s₂ s₅ (n₃ + (C₄ + n₅)) :=
    Work.Layout.Ev.seq hE₃ h45
  have h2345 : Work.Layout.Ev main
      (Cmd.seq dup_prog (Cmd.seq (Work.Layout.mvVal 0 4 2 3)
        (Cmd.seq (moveTop k 1 0) (Work.Layout.mvVal 4 0 2 3)))) s₁ s₅
      (48 * (vsz v + 1) + (n₃ + (C₄ + n₅))) := Work.Layout.Ev.seq hE₂' h345
  have hAll : Work.Layout.Ev main
      (Cmd.seq (moveTop k 0 1) (Cmd.seq dup_prog (Cmd.seq (Work.Layout.mvVal 0 4 2 3)
        (Cmd.seq (moveTop k 1 0) (Work.Layout.mvVal 4 0 2 3))))) ⟨s.reg, s.stk⟩ s₅
      (C₁ + (48 * (vsz v + 1) + (n₃ + (C₄ + n₅)))) := Work.Layout.Ev.seq hE₁ h2345
  obtain ⟨n, hev, hle⟩ := hAll
  refine ⟨v :: vs, s₅, n, rfl, ?_, le_trans hle hTOTAL, hfinal, ?_⟩
  · show Eval main (pickProg k) s s₅ n
    exact hev
  · intro k' hk'0
    by_cases h1 : k' = 1
    · subst k'
      rw [hf₅ 1 (by decide) (by decide) (by decide) (by decide), ha₄,
        List.drop_eq_nil_of_le hrev4, encs_nil, List.nil_append]
    · by_cases h2 : k' = 2
      · subst k'
        rw [h2₅, h2₄, h2₃, hfr₂ 2 (by decide), h2₁]
      · by_cases h3 : k' = 3
        · subst k'
          rw [h3₅, h3₄, h3₃, hfr₂ 3 (by decide), h3₁]
        · by_cases h4 : k' = 4
          · subst k'
            rw [ha₅, hfr₂ 4 (by decide), hf₁ 4 (by decide) (by decide) (by decide) (by decide)]
          · rw [hf₅ k' h4 hk'0 h2 h3, hf₄ k' h1 hk'0 h2 h3, hf₃ k' hk'0 h4 h2 h3,
              hfr₂ k' hk'0, hf₁ k' hk'0 h1 h2 h3]

end Work.Kernel
