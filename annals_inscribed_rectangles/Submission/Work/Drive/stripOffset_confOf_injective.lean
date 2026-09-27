import Mathlib
import Submission.Work.Drive.strip_offset
import Submission.Work.Drive.stripOffset_param
import Submission.Work.Drive.cappedPlaneFamily

/-!
# Injectivity of the offset chart of the strip, in capping coordinates

`Work.Drive.stripOffset_param` shows that the offset chart `(x, s) ↦ μ (x, x * exp (2πs))` of the
configuration strip is injective on `Circle × [0, 1/2]` up to the identification of the two
parametrisations of a diameter.  The capping (`Work.Drive.confOf`) reads a configuration point off the
axis in the coordinates `(‖(m, ℓ)‖, (m, ℓ)/‖(m, ℓ)‖, η)`, and
`Work.Drive.confOf_injective_of_nonneg` shows that these coordinates determine the configuration point
whenever the length is non-negative.  This file records the resulting form of the injectivity, in
capping coordinates: it is the form in which the *disk presentation* of the capped plane uses it (the
offset chart is the annulus half of the disk model of `P_u`).
-/

namespace Work.Drive

noncomputable section

/-- **The offset chart is injective in capping coordinates.**  If two offset points have the same
capping coordinates `confOf` — equivalently, by `confOf_injective_of_nonneg`, if they are the same
configuration point — then they are the same offset point, up to the two presentations of a
diameter. -/
theorem stripOffsetPt_confOf_injective
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ)
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    (hlen : ∀ p : Circle × Circle, 0 ≤ (μ p).2.2) :
    ∀ x x' : Circle, ∀ s s' : ℝ, s ∈ Set.Icc (0 : ℝ) (1 / 2) → s' ∈ Set.Icc (0 : ℝ) (1 / 2) →
      confOf (stripOffsetPt μ x s) = confOf (stripOffsetPt μ x' s') →
      (x = x' ∧ s = s') ∨ (s = 1 / 2 ∧ s' = 1 / 2 ∧ x' = -x) := by
  intro x x' s s' hs hs' h
  have h1 : 0 ≤ (stripOffsetPt μ x s).2.2 := hlen (x, x * Circle.exp (2 * Real.pi * s))
  have h2 : 0 ≤ (stripOffsetPt μ x' s').2.2 := hlen (x', x' * Circle.exp (2 * Real.pi * s'))
  have heq : stripOffsetPt μ x s = stripOffsetPt μ x' s' :=
    confOf_injective_of_nonneg h1 h2 h
  rcases stripOffset_param μ hsym hinj with ⟨_, hinjoff, _⟩
  exact hinjoff x x' s s' hs hs' heq

end

end Work.Drive
