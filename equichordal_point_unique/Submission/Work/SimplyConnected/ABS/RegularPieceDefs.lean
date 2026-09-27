import Mathlib

/-!
# The sector (cone) condition on the frontier of a region of a Riemann surface

This module fixes the *local geometric regularity* condition used in
`Work.SimplyConnected.ABS.exists_isRegularPiece_superset`, the "regular" (Dirichlet-regular)
version of the ABS engulfing statement.

`Work.SimplyConnected.ABS.HasSectorBoundary U p` says that, in a chart `c` around the frontier
point `p`, the region `U` avoids the solid sector with apex `p` spanned by two half-planes
`{0 < L₁ w}`, `{0 < L₂ w}` (`w = c x - c p`).

The condition is the classical *cone condition* of potential theory: it is a sufficient condition
for `p` to be a regular boundary point (the classical explicit barrier is a fractional power of the
chart coordinate), it holds at every point of a `C¹` boundary (in suitable coordinates the
complement of a `C¹` region at the origin contains a quadrant, i.e. a sector of angle `π/2`), and it
fails at points which may be irregular (the tip of Lebesgue's spine: the complement there contains
no sector of positive angle).
-/

namespace Work.SimplyConnected.ABS

open Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The sector (cone) condition at a frontier point `p` of `U`.**

There is a chart `c` (a member of the atlas), a neighbourhood `V` of `p`, and two non-zero linear
functionals `L₁ L₂ : ℂ →L[ℝ] ℝ` spanning a non-degenerate sector (non-empty), such that `U` meets
`V` only outside the *open* sector through `p`:

`∀ x ∈ U ∩ V, ¬ (0 < L₁ (c x - c p) ∧ 0 < L₂ (c x - c p))`.

The chart is required to be an atlas member and `V ⊆ c.source`, so that `c` really is a chart
coordinate system on `V`. -/
def HasSectorBoundary (U : Set X) (p : X) : Prop :=
  ∃ (c : OpenPartialHomeomorph X ℂ) (V : Set X) (L₁ L₂ : ℂ →L[ℝ] ℝ),
    c ∈ atlas ℂ X ∧ IsOpen V ∧ p ∈ V ∧ V ⊆ c.source ∧ p ∈ c.source ∧ L₁ ≠ 0 ∧ L₂ ≠ 0 ∧
      (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ x ∈ U ∩ V, ¬ (0 < L₁ (c x - c p) ∧ 0 < L₂ (c x - c p))

end Work.SimplyConnected.ABS
