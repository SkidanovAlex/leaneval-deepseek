import Mathlib
import Submission.Work.SilvermanReduction.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

/-- **Negation in coordinates.**  For two nonsingular affine points of a Weierstrass curve over a
field whose `x`-coordinates coincide, `(x, y) ≠ -(x', y')` holds exactly when `y` is not the
`y`-coordinate of `-(x', y')` and the `y`-coordinates agree.

This is the statement that two points of a Weierstrass curve over a field with the same
`x`-coordinate are either equal or negatives of each other.  Proof route: `Point.X_eq_iff` gives
`some x y h = some x' y' h' ∨ some x y h = -some x' y' h'`; `Point.neg_some` rewrites the
negation as `some x' (W'.negY x' y')`, and `Point.some.injEq` compares coordinates.  The forward
direction of `y' = y` uses `WeierstrassCurve.Affine.Y_eq_of_X_eq` on the two equations. -/
theorem ils_some_ne_neg_some {k : Type*} [Field k] [DecidableEq k] {W' : WeierstrassCurve.Affine k}
    {x y x' y' : k} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y') (hx : x = x') :
    (WeierstrassCurve.Affine.Point.some x y h ≠
      - WeierstrassCurve.Affine.Point.some x' y' h') ↔ (y ≠ W'.negY x' y' ∧ y' = y) := by
  subst hx
  rw [WeierstrassCurve.Affine.Point.neg_some h']
  simp only [ne_eq, WeierstrassCurve.Affine.Point.some.injEq, true_and]
  have hy : y = y' ∨ y = W'.negY x y' := WeierstrassCurve.Affine.Y_eq_of_X_eq h.1 h'.1 rfl
  constructor
  · intro hne
    refine ⟨hne, ?_⟩
    rcases hy with h1 | h2
    · exact h1.symm
    · exact absurd h2 hne
  · rintro ⟨hne, -⟩
    exact hne

end Work.SilvermanReduction
