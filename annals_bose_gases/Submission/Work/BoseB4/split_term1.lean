import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.SplitHbogPre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_term1` — the `(0,2)` Bogoliubov row under `split`

The mode-lattice word `a₀† a₀† a_l a_{−l}` (the adjoint of the `(2,0)` half of the
Bogoliubov pair term) corresponds, under `Work.BoseB4.split`, to the anti-normal
monomial `monoOp 0 2` with the excited-mode spectator operator
`annX m l ∘ annX m (-l)`:

    `split (a₀† (a₀† (a_l (a_{−l} v)))) = monoOp 0 2 (annX l ∘ annX (−l)) (split v)`.

The proof is the dictionary (`Split_ann_zero`, `Split_cre_zero`,
`Split_ann_excited`, `Split_cre_excited`, in the pointwise form recorded in
`Submission/Work/BoseB4/SplitHbogPre.lean`) followed by the `lift` composition law
`lift B ∘ lift B' = lift (B ∘ B')`.  Note `annX m l = annC (Excited m) ⟨l, hl⟩`
for `l ≠ 0`, so the two hypotheses `hl`, `hnl` are exactly what is needed to
identify the spectators. -/

namespace Work.BoseB4

theorem split_term1 {m : ℕ} [NeZero m] (l : Fin m) (hl : l ≠ 0) (hnl : -l ≠ 0) (v : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.cre m 0 (Work.BoseB4.cre m 0 (Work.BoseB4.ann m l (Work.BoseB4.ann m (-l) v))))
      = (Work.BoseB4.monoOp 0 2 ((Work.BoseB4.annX m l).comp (Work.BoseB4.annX m (-l)))) (Work.BoseB4.split v) := by
  rw [split_apply_cre_zero, split_apply_cre_zero, split_apply_ann_of_ne l hl,
    split_apply_ann_of_ne (-l) hnl, annX_of_ne l hl, annX_of_ne (-l) hnl]
  simp only [monoOp, a0pow_zero, a0dpow_succ, a0dpow_zero]
  rw [lift_comp_apply]
  rfl

end Work.BoseB4
