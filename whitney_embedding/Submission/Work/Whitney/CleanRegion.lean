import Mathlib
import Submission.Work.Whitney.DoublePoint

/-!
# The "clean region" of the Whitney cancellation

Whitney's cancellation of two double points `P = (p₁,p₂)`, `Q = (q₁,q₂)` of an immersion
`f : M → ℝ^{2n}` is performed inside an open set `W` on which

* `f` is injective except at the four preimages (`hclean`), and
* `f '' W` is disjoint from `f '' Wᶜ` (`hsep`).

Both conditions are *automatic* once `W` has been chosen so that it meets the set

`D = {y | ∃ z ≠ y, f z = f y}`

of all points that occur in a double point of `f` exactly in the four points `p₁,p₂,q₁,q₂`, and
provided the two double points are *simple* (their values have no third preimage, i.e. `f` has no
triple point there).  This file proves that implication
(`Work.Whitney.clean_region_conditions`); the existence of such a `W` is then a purely topological
statement: taking `W = M ∖ (D ∖ {p₁,p₂,q₁,q₂})` works as soon as the two arcs joining `p₁` to `q₁`
and `p₂` to `q₂` avoid `D` except at their endpoints (`D` is finite, hence closed, and the four
points are not in `D ∖ {p₁,p₂,q₁,q₂}`).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- Clean-region conditions. -/
theorem clean_region_conditions {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (D : Set M) (hD : ∀ y : M, y ∈ D ↔ ∃ z : M, z ≠ y ∧ f z = f y)
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hp₁ : p₁ ∈ W) (hp₂ : p₂ ∈ W) (hq₁ : q₁ ∈ W) (hq₂ : q₂ ∈ W)
    (hWD : ∀ y ∈ W, y ∈ D → y = p₁ ∨ y = p₂ ∨ y = q₁ ∨ y = q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hpreP : ∀ z : M, f z = f p₁ → z = p₁ ∨ z = p₂)
    (hpreQ : ∀ z : M, f z = f q₁ → z = q₁ ∨ z = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂) :
    (∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁)) ∧
    (∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z) := by
  constructor
  · intro y z hyW hzW hfyz
    by_cases hyz : y = z
    · exact Or.inl hyz
    · have hyD : y ∈ D := (hD y).mpr ⟨z, fun h => hyz h.symm, hfyz.symm⟩
      rcases hWD y hyW hyD with h | h | h | h
      · subst h
        rcases hpreP z hfyz.symm with h2 | h2
        · exact absurd h2.symm hyz
        · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · subst h
        rcases hpreP z (hfyz.symm.trans hfp.symm) with h2 | h2
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
        · exact absurd h2.symm hyz
      · subst h
        rcases hpreQ z hfyz.symm with h2 | h2
        · exact absurd h2.symm hyz
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩)))
      · subst h
        rcases hpreQ z (hfyz.symm.trans hfq.symm) with h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h2⟩)))
        · exact absurd h2.symm hyz
  · intro y z hyW hzW hfyz
    have hyz : y ≠ z := fun h => hzW (h ▸ hyW)
    have hyD : y ∈ D := (hD y).mpr ⟨z, fun h => hyz h.symm, hfyz.symm⟩
    rcases hWD y hyW hyD with h | h | h | h
    · subst h
      rcases hpreP z hfyz.symm with h2 | h2
      · exact hzW (h2 ▸ hp₁)
      · exact hzW (h2 ▸ hp₂)
    · subst h
      rcases hpreP z (hfyz.symm.trans hfp.symm) with h2 | h2
      · exact hzW (h2 ▸ hp₁)
      · exact hzW (h2 ▸ hp₂)
    · subst h
      rcases hpreQ z hfyz.symm with h2 | h2
      · exact hzW (h2 ▸ hq₁)
      · exact hzW (h2 ▸ hq₂)
    · subst h
      rcases hpreQ z (hfyz.symm.trans hfq.symm) with h2 | h2
      · exact hzW (h2 ▸ hq₁)
      · exact hzW (h2 ▸ hq₂)


end Work.Whitney
