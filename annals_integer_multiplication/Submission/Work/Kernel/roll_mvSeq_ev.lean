import Mathlib
import Submission.Work.Kernel.rollDefs
import Submission.Work.Layout.mvVal_ev_full

namespace Work.Kernel

open HvdH

/-- `encs` of a reversed cons list: moving one value to the front reverses it. -/
theorem encs_reverse_cons (u : Val) (us : List Val) :
    encs (u :: us).reverse = encs us.reverse ++ u.enc := by
  rw [List.reverse_cons, encs_append, encs_cons, encs_nil, List.append_nil]

theorem roll_mvSeq_ev {main : HvdH.Cmd} {a b c d : HvdH.Stk} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (us : List HvdH.Val)
    (A B : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (ha : X a = HvdH.encs us ++ A) (hb : X b = B) :
    ∃ s' n, Work.Layout.Ev main (Work.Kernel.roll_mvSeq a b c d us.length) ⟨g, X⟩ s' n ∧
      n ≤ 16 * ((us.map HvdH.vsz).sum + us.length + 1) ∧
      s'.stk a = A ∧ s'.stk b = HvdH.encs us.reverse ++ B ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k : HvdH.Stk, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  have key : ∀ (us : List HvdH.Val) (A B : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph), X a = HvdH.encs us ++ A → X b = B →
      ∃ s' n, Work.Layout.Ev main (Work.Kernel.roll_mvSeq a b c d us.length) ⟨g, X⟩ s' n ∧
        n ≤ 16 * ((us.map HvdH.vsz).sum + us.length + 1) ∧
        s'.stk a = A ∧ s'.stk b = HvdH.encs us.reverse ++ B ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
        (∀ k : HvdH.Stk, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
    intro us
    induction us with
    | nil =>
      intro A B g X ha hb
      refine ⟨⟨g, X⟩, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [roll_mvSeq_zero] using Work.Layout.ev_skip main (⟨g, X⟩ : HvdH.State)
      · simp only [List.map_nil, List.sum_nil, List.length_nil]; norm_num
      · simpa [encs_nil] using ha
      · simpa [encs_nil] using hb
      · rfl
      · rfl
      · intro k _ _ _ _; rfl
    | cons u us' ih =>
      intro A B g X ha hb
      have ha' : X a = u.enc ++ (encs us' ++ A) := by
        rw [encs_cons, List.append_assoc] at ha; exact ha
      obtain ⟨s₁, n₁, h1, hn1, ha1, hb1, hc1, hd1, hf1⟩ :=
        Work.Layout.mvVal_ev_full (a := a) (b := b) (c := c) (d := d) (g := g) (X := X)
          (v := u) (A := encs us' ++ A) (B := B) hab hac had hbc hbd hcd ha' hb
      obtain ⟨s₂, n₂, h2, hn2, ha2, hb2, hc2, hd2, hf2⟩ :=
        ih A (u.enc ++ B) s₁.reg s₁.stk ha1 hb1
      refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, roll_mvSeq_succ]
        exact Work.Layout.Ev.seq h1 h2
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      · exact ha2
      · rw [hb2, encs_reverse_cons, List.append_assoc]
      · rw [hc2, hc1]
      · rw [hd2, hd1]
      · intro k hka hkb hkc hkd
        rw [hf2 k hka hkb hkc hkd, hf1 k hka hkb hkc hkd]
  exact key us A B g X ha hb

end Work.Kernel
