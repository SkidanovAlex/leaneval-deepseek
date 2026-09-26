/-
# Shared shape predicate for the `K₊^{(24)}` five-term decomposition

This file only records the *predicate* used to state the atom bounds at a point `τ` that the
far-region deviation bound `Work.Asymptotics.Tile.halfDevFar24High` consumes: the four
`τ`-atoms `r0 = τE₁₄(τ)`, `r1 = φ₀(τ)Δ(τ)`, `r2 = φ₂(τ)E₁₀(τ)`, `R0 = φ₀(τ)E₄(τ)³` are bounded
by `D · scale τ` and the `j`-invariant by `Dj · scale τ`.

On the cusp-`±1` tile `τ = n +ᵥ w` (`w ∈ E = KEpsilon`, `n = ±1`) these hold with
`D = O((scale w)^N)` and `Dj = O((scale w)^N e^{2π Im (S • w)})`; whereas on the funnel
`{2 ≤ Im τ}` they hold with `D = O(1)` and `Dj = O(e^{2π Im τ})` (see
`Work.Asymptotics.K24F.tau_atom_bounds_D`).
-/
import Mathlib
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24FBase

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace Tile

/-- The `τ`-atom bounds at the point `τ` used by the `K₊^{(24)}` cusp decomposition.

`D` bounds `r0, r1, r2, R0` and `Dj` bounds `j`, both relative to `scale τ`. -/
def TileAtoms24 (τ : ℍ) (D Dj : ℝ) : Prop :=
  ‖K24F.r0 τ‖ ≤ D * scale τ ∧ ‖K24F.r1 τ‖ ≤ D * scale τ ∧
  ‖K24F.r2 τ‖ ≤ D * scale τ ∧ ‖K24F.R0 τ‖ ≤ D * scale τ ∧
  ‖jInvariantFun τ‖ ≤ Dj * scale τ

/-- Monotonicity of `TileAtoms24` in the two constants. -/
lemma TileAtoms24.mono {τ : ℍ} {D Dj D' Dj' : ℝ} (h : TileAtoms24 τ D Dj)
    (hD : D ≤ D') (hDj : Dj ≤ Dj') : TileAtoms24 τ D' Dj' := by
  obtain ⟨a, b, c, d, e⟩ := h
  have hs : (0 : ℝ) ≤ scale τ := (scale_pos τ).le
  exact ⟨le_trans a (mul_le_mul_of_nonneg_right hD hs),
    le_trans b (mul_le_mul_of_nonneg_right hD hs),
    le_trans c (mul_le_mul_of_nonneg_right hD hs),
    le_trans d (mul_le_mul_of_nonneg_right hD hs),
    le_trans e (mul_le_mul_of_nonneg_right hDj hs)⟩

end Tile

end

end Work.Asymptotics
