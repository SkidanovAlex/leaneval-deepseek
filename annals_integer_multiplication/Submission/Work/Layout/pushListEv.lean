import Mathlib
import Submission.Work.Layout.ReplicateDefs

namespace Work.Layout

/-- Work in `Submission/Work/Layout/pushListEv.lean`.

`Work.Layout.pushList l` pushes the glyph list `l` onto stack 0 (so that stack 0 becomes
`l ++ X 0`), leaving every other stack untouched.  Definition (in
`Submission/Work/Layout/ReplicateDefs.lean`): `pushList [] = Cmd.skip` and
`pushList (c :: cs) = Cmd.seq (pushList cs) (pushConst 0 c)`; `pushConst_ev` (cost 2 per glyph) is in
`Submission/Work/Layout/Move.lean`, and the extra 1 is the final `Cmd.skip`. -/
theorem pushListEv {main : HvdH.Cmd} (l : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.pushList l) ⟨g, X⟩ s' n ∧ n ≤ 2 * l.length + 1 ∧
      s'.stk 0 = l ++ X 0 ∧ (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = X k) := by
  induction l generalizing g X with
  | nil =>
      refine ⟨⟨g, X⟩, 1, ?_, by simp, by simp, ?_⟩
      · simpa [pushList] using ev_skip main (⟨g, X⟩ : HvdH.State)
      · intro k _
        rfl
  | cons c cs ih =>
      obtain ⟨s₁, n₁, h₁, hn₁, h0₁, hk₁⟩ := ih g X
      obtain ⟨s₂, n₂, h₂, hn₂, h0₂, hk₂, -, -⟩ :=
        pushConst_ev (main := main) (k := 0) (cst := c) (g := s₁.reg) (X := s₁.stk)
      refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_⟩
      · show Ev main (HvdH.Cmd.seq (pushList cs) (pushConst 0 c)) ⟨g, X⟩ s₂ (n₁ + n₂)
        exact Ev.seq h₁ h₂
      · simp only [List.length_cons]
        omega
      · rw [h0₂, h0₁, List.cons_append]
      · intro k hk
        rw [hk₂ k hk, hk₁ k hk]

end Work.Layout
