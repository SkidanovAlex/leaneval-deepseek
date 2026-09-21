import Submission.Work.OddRadon.Reduction

/-!
# The two-power radial system (`Work.OddRadon`, part 4: definitions)

For odd `d = 2n+1` the paper rewrites the two Radon conditions `𝓡(w_1² ρ^{d+1}) = φ` and
`𝓡(w_1 ρ^d) = ψ` (restricted to rotation-invariant even data) into equations for the two
*r radial functions* `R, r` of the body of revolution: the boundary point at angle `α` is
`(R α cos α, R α sin α)` in the upper half-plane and `(-(r α cos α), r α sin α)` in the lower
half-plane, and the conditions become

  `R(α)^{d+1} + r(α)^{d+1} = Φ(α) / cos²α`,   `R(α)^d - r(α)^d = Ψ(α) / cos α`   (paper (+r)),

where `(Φ, Ψ)` are the rotation-invariant `𝓡^{-1}`-transformed data.

## The non-degenerate reading

Written with divisions, the system is degenerate at `α = π/2` (`cos (π/2) = 0`, so Lean's
`x / 0 = 0` makes the equation read `R^{d+1} + r^{d+1} = 0`, which no positive pair can
satisfy).  The mathematically correct form — the one used in the paper, where both sides tend
to finite values as `α → π/2` — is the cleared form

  `(R^{d+1} + r^{d+1}) cos²α = Φ α`,   `(R^d - r^d) cos α = Ψ α`.

This is `RadialSystem` below; `RadialSystem_iff_div` shows it agrees with the divided form on
the half-open interval `[0, π/2)`.

## Main definitions

* `radialMap n` — the two-power map `(R, r) ↦ (R^{2n+2}+r^{2n+2}, R^{2n+1}-r^{2n+1})`;
* `RadialSystem n Φ Ψ R r` — the system;
* `IsRadialGraph R r f` — `f` is the radial graph of `(R, r)`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **The two-power map** `(R,r) ↦ (R^{2n+2} + r^{2n+2}, R^{2n+1} - r^{2n+1})`, for the odd
dimension `d = 2n+1` (`d+1 = 2n+2`, `d = 2n+1`). -/
def radialMap (n : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 ^ (2 * n + 2) + p.2 ^ (2 * n + 2), p.1 ^ (2 * n + 1) - p.2 ^ (2 * n + 1))

/-- **The two-power radial system** (`d = 2n+1`, `n ≥ 1`), in its non-degenerate cleared form:
`(R^{d+1} + r^{d+1}) cos²α = Φ α` and `(R^d - r^d) cos α = Ψ α` on `[0, π/2]`. -/
def RadialSystem (n : ℕ) (Φ Ψ : ℝ → ℝ) (R r : ℝ → ℝ) : Prop :=
  ∀ α ∈ Set.Icc 0 (Real.pi / 2),
    (R α ^ (2 * n + 2) + r α ^ (2 * n + 2)) * Real.cos α ^ 2 = Φ α ∧
    (R α ^ (2 * n + 1) - r α ^ (2 * n + 1)) * Real.cos α = Ψ α

/-- `f` is traced by the radial functions `R, r`: the upper boundary arc is
`α ↦ (R α cos α, R α sin α)` and the lower one `α ↦ (-(r α cos α), r α sin α)`. -/
def IsRadialGraph (R r f : ℝ → ℝ) : Prop :=
  (∀ α ∈ Set.Icc 0 (Real.pi / 2), f (R α * Real.cos α) = R α * Real.sin α) ∧
  (∀ α ∈ Set.Icc 0 (Real.pi / 2), f (-(r α * Real.cos α)) = r α * Real.sin α)

/-- The ball's data: `Φ α = 2 cos²α`, `Ψ α = 0`. -/
def ballPhi (α : ℝ) : ℝ := 2 * Real.cos α ^ 2

/-- The ball's second datum. -/
def ballPsi (_ : ℝ) : ℝ := 0

/-- The (trivial) radial functions of the ball: `R = r = 1` on the whole interval, so the body
is the Euclidean ball (its profile is the semicircle). -/
def ballR (_ : ℝ) : ℝ := 1

/-- The ball's second radial function. -/
def ballr (_ : ℝ) : ℝ := 1

end Work.OddRadon
