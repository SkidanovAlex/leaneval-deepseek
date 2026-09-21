import Mathlib
import Submission.Commons.Geometry.Ulam.odd_floating_of_family

/-!
# The odd-dimensional family data: statement

The package of data that the odd-dimensional half of Ryabogin's construction produces: a
perturbation `h` of the ball data and a profile `f` (strictly concave, vanishing at the ends,
positive inside, not symmetric) such that the one-parameter family of hyperplanes
`x_d = s x_0 + h s` are the cutting hyperplanes at level `vol K / 2`, and their "under-graph"
centroids lie on the line through the centre of mass in the direction `(-s, 0, ..., 0, 1)`.

This is stated as a named `Prop` so that the intermediate targets of the construction can be
phrased as statements about it.
-/

namespace Submission.Odd

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

/-- The odd-dimensional family data of Ryabogin's construction. -/
def OddFamilyData (d : ℕ) [NeZero d] : Prop :=
∃ R₁ R₂ : ℝ, ∃ f h : ℝ → ℝ,
      -R₁ < R₂ ∧
      Function.support f ⊆ Set.Icc (-R₁) R₂ ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂) ∧
      StrictConcaveOn ℝ (Set.Icc (-R₁) R₂) f ∧
      ContinuousOn f (Set.Icc (-R₁) R₂) ∧
      f (-R₁) = 0 ∧ f R₂ = 0 ∧
      (∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t) ∧
      ContDiff ℝ ∞ h ∧
      h 0 = 0 ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) ∧
      (let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
       ∀ s : ℝ, 0 < s →
        volume.real (K ∩ {x | x ⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}) =
          volume.real K / 2) ∧
      (let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
       ∀ s : ℝ, 0 < s →
        (⨍ x in K, x) - (⨍ x in (K ∩ {x | x ⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}), x) ∈
          ℝ ∙ (EuclideanSpace.single (0 : Fin d) (-s) +
            EuclideanSpace.single (⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ : Fin d) 1)) ∧
      (let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
       ¬ ∃ p : EuclideanSpace ℝ (Fin d), K - {p} = -(K - {p}))

end Submission.Odd
