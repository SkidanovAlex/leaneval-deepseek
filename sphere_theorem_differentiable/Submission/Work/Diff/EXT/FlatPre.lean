import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Heaviside cut of a function on `ℝ × ℝⁿ`

`stepFun T γ` is the function which is `0` on the closed half-space `{t ≤ T}` and agrees with `γ`
on the open half-space `{t > T}`.

This is the shape of the function in `Work.Diff.EXT.contDiffAt_of_flat_indicator`: a smooth
function that is flat along the hyperplane `{t = T}`, cut off by the indicator of `{t > T}`.
-/

namespace Work.Diff.EXT

/-- The Heaviside cut of `γ` at the hyperplane `{t = T}`. -/
noncomputable def stepFun {n : ℕ} (T : ℝ) {F : Type*} [Zero F] (γ : ℝ × (Fin n → ℝ) → F) :
    ℝ × (Fin n → ℝ) → F :=
  fun p => if p.1 ≤ T then 0 else γ p

@[simp]
theorem stepFun_apply {n : ℕ} (T : ℝ) {F : Type*} [Zero F] (γ : ℝ × (Fin n → ℝ) → F)
    (p : ℝ × (Fin n → ℝ)) : stepFun T γ p = if p.1 ≤ T then 0 else γ p := rfl

end Work.Diff.EXT
