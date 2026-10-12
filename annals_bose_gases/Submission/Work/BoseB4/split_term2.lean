import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.SplitHbogPre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- **Split of the `(2,0)` Bogoliubov row.**  The lattice word
`a†_l a†_{-l} a₀ a₀` (all annihilations performed first) corresponds, under
`split`, to the anti-normal monomial `a₀² (a₀†)⁰ (creC l ∘ creC (−l))`, i.e. to
`monoOp 2 0 ((creX m l).comp (creX m (-l))>` evaluated on the split state.

This is the `(2,0)` companion of `split_term1`: the two creation operators
`cre m l`, `cre m (-l)` act on the spectator (excited) modes, hence commute with
the condensate annihilation `a₀` and are absorbed into a single `lift` of the
composition `creX m l ∘ creX m (-l)`, while the two condensate annihilations
`ann m 0` sit to the left of that `lift`, giving precisely `a0pow 2 ∘ lift B`
with `B` the composed spectator creation. -/
theorem split_term2 {m : ℕ} [NeZero m] (l : Fin m) (hl : l ≠ 0) (hnl : -l ≠ 0) (v : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (Work.BoseB4.cre m l (Work.BoseB4.cre m (-l) (Work.BoseB4.ann m 0 (Work.BoseB4.ann m 0 v))))
      = (Work.BoseB4.monoOp 2 0 ((Work.BoseB4.creX m l).comp (Work.BoseB4.creX m (-l)))) (Work.BoseB4.split v) := by
  -- Push `split` through the four mode operators, innermost first.
  rw [split_apply_cre_of_ne l hl, split_apply_cre_of_ne (-l) hnl,
    split_apply_ann_zero, split_apply_ann_zero]
  -- Match the spectator operators with the lattice words `creX`.
  rw [monoOp, creX_of_ne l hl, creX_of_ne (-l) hnl]
  simp only [a0dpow_zero, LinearMap.comp_apply]
  -- Absorb the two `lift`s into one, then move it past the two condensate annihilations.
  rw [lift_comp_apply]
  rw [lift_a0_apply, lift_a0_apply]
  simp [a0pow, LinearMap.comp_apply]

end Work.BoseB4
