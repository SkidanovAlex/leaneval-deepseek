import Mathlib
import Submission.Work.Smooth.JordanSeparation.plCutLoop

/-!
# Distributing endpoint casts over path concatenation (step (B), first cast)

The assembly of the induction step needs to compare two composite paths which differ only by
`Prop`-level endpoint casts on their factors: the cast of `A · B` along the closing equality is the
concatenation of `A` with the cast of `B`.  This file supplies that identity.

* `path_cast_apply` — an endpoint cast does not change the values of a path;
* `cast_trans_eq` — a cast *outside* a concatenation is the same as the cast applied to the last
  factor.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- An endpoint cast does not change the values of a path. -/
theorem path_cast_apply {x y x' y' : X} (γ : Path x y) (hx : x' = x) (hy : y' = y)
    (t : unitInterval) :
    ((Path.cast γ hx hy : Path x' y') : unitInterval → X) t = γ t := by
  rw [Path.cast_coe]

/-- **A cast outside a concatenation acts on the last factor.** -/
theorem cast_trans_eq {x y x' : X} (A : Path x' x) (B : Path x y) (h : x' = y) :
    Path.cast (A.trans B) rfl h = A.trans (Path.cast B rfl h) := by
  ext t
  rw [path_cast_apply, Path.trans_apply, Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [dif_pos ht]
  · simp only [dif_neg ht]
    exact path_cast_apply B rfl h _

end

end Work.Smooth.JordanSeparation
