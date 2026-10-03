import Mathlib

/-!
# Differentiability of an iterate at a point (REPEL / pert_orbit_eqOn infrastructure)

If a map `g : ℂ → ℂ` is differentiable at every point of the finite orbit
`x, g x, g^[2] x, …, g^[n-1] x` (and at `x` itself, for `n = 0` nothing is needed), then the
iterate `g^[n]` is differentiable at `x`.  (Mathlib's `DifferentiableAt.iterate` only covers the
case of a fixed point, which is not what is needed here.)
-/

namespace Work.Repel

/-- Iterates are differentiable at a point whose orbit stays in the domain of differentiability. -/
theorem differentiableAt_iterate {g : ℂ → ℂ} {x : ℂ} (n : ℕ)
    (h : ∀ i < n, DifferentiableAt ℂ g (g^[i] x)) : DifferentiableAt ℂ g^[n] x := by
  induction n with
  | zero => exact differentiableAt_id
  | succ n ih =>
      have hn : DifferentiableAt ℂ g^[n] x :=
        ih fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have hg : DifferentiableAt ℂ g (g^[n] x) := h n (Nat.lt_succ_self n)
      have hcomp : DifferentiableAt ℂ (g ∘ g^[n]) x := hg.comp x hn
      rw [← Function.iterate_succ'] at hcomp
      exact hcomp

end Work.Repel
