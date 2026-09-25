import Mathlib

namespace Work.LT

/-- A self-adjoint operator on the `ℓ²` space of a finite type is linear: symmetry of the quadratic form `(u,v) ↦ ∑ x, T u x * v x` forces additivity and homogeneity. -/
theorem op_linear {X : Type*} [Fintype X] (T : (X → ℝ) → (X → ℝ))
    (hsym : ∀ u v : X → ℝ, (∑ x, T u x * v x) = ∑ x, T v x * u x) :
    (∀ u v : X → ℝ, T (u + v) = T u + T v) ∧
      (∀ (c : ℝ) (u : X → ℝ), T (c • u) = c • T u) := by
  classical
  -- Testing the symmetric form against the point mass `Pi.single x 1` exhibits `T f x`
  -- as an explicit linear functional of `f`: `T f x = ∑ y, T (Pi.single x 1) y * f y`.
  have hsingle : ∀ (f : X → ℝ) (x : X), T f x = ∑ y, T (Pi.single x (1:ℝ)) y * f y := by
    intro f x
    have h1 : (∑ y, T f y * (Pi.single x (1:ℝ) : X → ℝ) y) = T f x := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    have h2 := hsym f (Pi.single x (1:ℝ))
    rw [h1] at h2
    exact h2
  constructor
  · intro f g
    funext x
    show T (f + g) x = T f x + T g x
    rw [hsingle (f + g) x, hsingle f x, hsingle g x, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [Pi.add_apply, mul_add]
  · intro c f
    funext x
    show T (c • f) x = c * T f x
    rw [hsingle (c • f) x, hsingle f x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Pi.smul_apply, smul_eq_mul]
    ring

end Work.LT
