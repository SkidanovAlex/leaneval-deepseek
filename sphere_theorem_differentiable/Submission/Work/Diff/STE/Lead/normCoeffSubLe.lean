import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- The mean value inequality on the interval `Set.Ico 0 tau`: if `f : ℝ → ℂ` has derivative
`F r` within `Set.Ico 0 tau` at every `r` of that interval and `‖F r‖ ≤ g` there, then `f` is
`g`-Lipschitz on the interval (in the form `‖f s - f t‖ ≤ |s - t| * g`). -/
lemma normCoeffSubLe {tau t : ℝ} {f F : ℝ → ℂ} {g : ℝ} (hder : ∀ r ∈ Set.Ico (0 : ℝ) tau, HasDerivWithinAt f (F r) (Set.Ico (0 : ℝ) tau) r) (hb : ∀ r ∈ Set.Ico (0 : ℝ) tau, ‖F r‖ ≤ g) (ht : t ∈ Set.Ico (0 : ℝ) tau) : ∀ s ∈ Set.Ico (0 : ℝ) tau, ‖f s - f t‖ ≤ |s - t| * g := by
  intro s hs
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Ico (0 : ℝ) tau) (f := f) (f' := F) (C := g)
    hder hb (convex_Ico 0 tau) ht hs
  rw [Real.norm_eq_abs, mul_comm] at h
  exact h

end Work.Diff.STE.Lead
