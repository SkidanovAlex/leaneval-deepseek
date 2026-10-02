import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

/-- **Signed mean-value bound.** If `φ` is continuous on `[a,b]` and differentiable on `(a,b)` with
`l ≤ φ' ≤ u` there, then `φ b - φ a ∈ [l (b-a), u (b-a)]`. -/
theorem derivBoundIcc {φ : ℝ → ℝ} {a b l u : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hdiff : DifferentiableOn ℝ φ (Set.Ioo a b))
    (hl : ∀ x ∈ Set.Ioo a b, l ≤ deriv φ x) (hu : ∀ x ∈ Set.Ioo a b, deriv φ x ≤ u) :
    φ b - φ a ∈ Set.Icc (l * (b - a)) (u * (b - a)) := by
  have hD : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hdiff' : DifferentiableOn ℝ φ (interior (Set.Icc a b)) := by
    rwa [interior_Icc]
  have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  constructor
  · refine hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff' ?_ a ha b hb hab
    intro x hx
    exact hl x (by rwa [interior_Icc] at hx)
  · refine hD.image_sub_le_mul_sub_of_deriv_le hcont hdiff' ?_ a ha b hb hab
    intro x hx
    exact hu x (by rwa [interior_Icc] at hx)

end Work.PTGeometric.WeakRegion
