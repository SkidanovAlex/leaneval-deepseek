import Mathlib
import Submission.Work.Layout.Take.Basic

namespace Work.Layout.Take

/-- One iteration of `walkProg_x`'s loop, taken on the `nil` terminator: the list on stack `0` is
empty, so `walkBody` pops the `nil` glyph, fails the `cons` test and stops the driver (`rG := eos`)
without touching anything else.  Cost `3` (`pop` plus the two steps of the `ite`). -/
theorem walkBody_nil (main : HvdH.Cmd) (A : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (h0 : X 0 = HvdH.Glyph.nil :: A) : ∃ s' n, Work.Layout.Ev main Work.Layout.walkBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧ s'.stk 0 = A ∧ s'.reg Work.Layout.rG = HvdH.Glyph.eos ∧ (∀ j, j ≠ 0 → s'.stk j = X j) := by
  -- popping the `nil` head of stack `0`
  have h1 : Work.Layout.Ev main (HvdH.Cmd.pop 0 Work.Layout.rE_x) ⟨g, X⟩
      ⟨Function.update g Work.Layout.rE_x HvdH.Glyph.nil, Function.update X 0 A⟩ 1 := by
    have h := ev_pop' main 0 Work.Layout.rE_x g X
    have hhead : (X 0).headD HvdH.Glyph.eos = HvdH.Glyph.nil := by rw [h0]; rfl
    have htail : (X 0).tail = A := by rw [h0]; rfl
    rw [hhead, htail] at h
    exact h
  -- the `cons` test fails, so the driver register is set to `eos`
  have h2 : Work.Layout.Ev main
      (HvdH.Cmd.ite Work.Layout.rE_x HvdH.Glyph.cons
        (seqs [mvVal 0 Work.Layout.sS Work.Layout.sX Work.Layout.sY, HvdH.Cmd.set Work.Layout.rE_x Work.Layout.gU,
          HvdH.Cmd.push Work.Layout.sD Work.Layout.rE_x, HvdH.Cmd.set Work.Layout.rG Work.Layout.gCont_x])
        (HvdH.Cmd.set Work.Layout.rG HvdH.Glyph.eos))
      ⟨Function.update g Work.Layout.rE_x HvdH.Glyph.nil, Function.update X 0 A⟩
      ⟨Function.update (Function.update g Work.Layout.rE_x HvdH.Glyph.nil) Work.Layout.rG HvdH.Glyph.eos,
        Function.update X 0 A⟩ 2 :=
    Ev.iteF (by show Function.update g Work.Layout.rE_x HvdH.Glyph.nil Work.Layout.rE_x ≠ HvdH.Glyph.cons
                rw [Function.update_self]; decide)
      (ev_set' main Work.Layout.rG HvdH.Glyph.eos _ _)
  refine ⟨⟨Function.update (Function.update g Work.Layout.rE_x HvdH.Glyph.nil) Work.Layout.rG HvdH.Glyph.eos,
      Function.update X 0 A⟩, 3, ?_, le_rfl, ?_, ?_, ?_⟩
  · unfold Work.Layout.walkBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  · simp
  · simp
  · intro j hj
    exact Function.update_of_ne hj _ _

end Work.Layout.Take
