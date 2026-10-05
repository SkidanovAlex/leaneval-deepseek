import Mathlib

/-!
# Definitions for the ray construction of a retraction from a fixed-point-free map

Let `E = EuclideanSpace ℝ (Fin N)`.  Given two vectors `p, d ∈ E` with `d ≠ 0`, the ray
`t ↦ p + t • d` meets the unit sphere `{z | ‖z‖ = 1}` in exactly one point with `t ≥ 0` when
`‖p‖ ≤ 1`; that parameter is the (closed-form) larger root of the quadratic
`‖p + t • d‖² = 1`, namely

  `rayT p d = (-⟪p, d⟫ + √(⟪p, d⟫² + ‖d‖² * (1 - ‖p‖²))) / ‖d‖²`.

This is the "ray from an interior point through a boundary point, extended to the sphere" of the
classical proof that a fixed-point-free self-map of the closed ball yields a retraction onto the
sphere.
-/

namespace Work.RPB1a.Caratheodory.Brouwer

open scoped Topology

/-- The larger root of the equation `‖p + t • d‖ = 1` in the ray parameter `t`, in closed form.

(For `d = 0` the formula is still meaningful but divides by zero; all uses supply `d ≠ 0`.) -/
noncomputable def rayT {N : ℕ} (p d : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (-(inner ℝ p d) + Real.sqrt ((inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2))) / ‖d‖ ^ 2

end Work.RPB1a.Caratheodory.Brouwer
