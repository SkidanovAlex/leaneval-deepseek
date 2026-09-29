import Mathlib
import Submission.Work.Layout.MergeDefs

namespace Work.Layout

open HvdH Work.Layout

/-- **`updSize` when there is no record left to expose** (the `else` branch of `Sk.updSize`).

If the top glyph of `S` is not `cons` — i.e. `S` no longer carries a record whose key size could be
cached — then `Sk.updSize pSize S SA t d` = `peek S rH; ite rH cons (pushSize …) skip` reads
`(X S).headD Glyph.eos` into `rH` and, since this is not `Glyph.cons`, executes `skip`. It therefore
changes no stack at all, in cost `3 ≤ 4`. -/
theorem merge_updSizeSkip {main pSize : Cmd} {S SA t d : Stk} {g : Reg → Glyph} {X : Stk → List Glyph} (hS : (X S).headD Glyph.eos ≠ Glyph.cons) : ∃ s' n, Ev main (Sk.updSize pSize S SA t d) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧ s'.stk S = X S ∧ s'.stk SA = X SA ∧ s'.stk 0 = X 0 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧ (∀ k' : Stk, k' ≠ S → k' ≠ SA → k' ≠ 0 → k' ≠ t → k' ≠ d → s'.stk k' = X k') := by
  -- after the `peek`, register `rH` holds `(X S).headD Glyph.eos ≠ cons`, so `ite` takes `skip`
  let s1 : State := ⟨Function.update g Sk.rH ((X S).headD Glyph.eos), X⟩
  have e1 : Ev main (.peek S Sk.rH) ⟨g, X⟩ s1 1 := ev_peek' main S Sk.rH g X
  let s2 : State := ⟨s1.reg, s1.stk⟩
  have hne : s1.reg Sk.rH ≠ Glyph.cons := by
    rw [show s1.reg Sk.rH = (X S).headD Glyph.eos from rfl]; exact hS
  have e2 : Ev main (.ite Sk.rH Glyph.cons (Sk.pushSize pSize S SA t d) .skip) s1 s2 2 :=
    Ev.iteF hne (ev_skip main s1)
  refine ⟨s2, 3, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the whole program is `peek` followed by the `ite`, cost `1 + 2 = 3 ≤ 4`
    unfold Sk.updSize
    exact Ev.seq' (C := 3) e1 e2 (by omega)
  · simp only [s2, s1]
  · simp only [s2, s1]
  · simp only [s2, s1]
  · simp only [s2, s1]
  · simp only [s2, s1]
  · intro k' _ _ _ _ _
    simp only [s2, s1]

end Work.Layout
