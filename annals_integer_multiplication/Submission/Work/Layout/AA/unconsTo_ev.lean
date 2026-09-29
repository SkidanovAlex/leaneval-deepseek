import Mathlib
import Submission.Work.Layout.AA.Defs

namespace Work.Layout.AA

/-- `unconsTo` is `pop` followed by `mvVal`; the `Ev`-specification composes the two. -/
theorem unconsTo_ev (main : HvdH.Cmd) (a b c d : HvdH.Stk) (rr : HvdH.Reg)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (v : HvdH.Val)
    (A : List HvdH.Glyph) (ha : X a = HvdH.Glyph.cons :: (v.enc ++ A)) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.unconsTo a b c d rr) ⟨g, X⟩ s' n ∧
      n ≤ 20 * (HvdH.vsz v + 1) ∧ s'.stk a = A ∧ s'.stk b = v.enc ++ X b ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ c → j ≠ d → s'.stk j = X j) := by
  -- pop the leading `cons`
  have h1 : Work.Layout.Ev main (.pop a rr) ⟨g, X⟩
      ⟨Function.update g rr ((X a).headD HvdH.Glyph.eos), Function.update X a (X a).tail⟩ 1 :=
    Work.Layout.ev_pop' main a rr g X
  -- the value follows immediately after the popped `cons`
  have ha' : Function.update X a (X a).tail a = v.enc ++ A := by
    simp only [Work.Layout.stkFn_same, ha, Work.Layout.tail_cons]
  have hb' : Function.update X a (X a).tail b = X b :=
    Work.Layout.stkFn_ne X hab.symm (X a).tail
  obtain ⟨s₂, n₂, h2, hn₂, ha₂, hb₂, hf₂⟩ :=
    Work.Layout.mvVal_ev (main := main) hab hac had hbc hbd hcd
      (g := Function.update g rr ((X a).headD HvdH.Glyph.eos))
      (X := Function.update X a (X a).tail) (v := v) (A := A) (B := X b) ha' hb'
  have hupd : ∀ j, j ≠ a → Function.update X a (X a).tail j = X j :=
    fun j hj => Work.Layout.stkFn_ne X hj (X a).tail
  have hmain : Work.Layout.Ev main (Work.Layout.unconsTo a b c d rr) ⟨g, X⟩ s₂ (n₂ + 1) := by
    unfold Work.Layout.unconsTo
    simp only [Work.Layout.seqs]
    exact Work.Layout.Ev.seq' h1 h2 (by omega)
  refine ⟨s₂, _, hmain, by omega, ha₂, hb₂, ?_⟩
  intro j hja hjb hjc hjd
  rw [hf₂ j hja hjb hjc hjd, hupd j hja]

end Work.Layout.AA
