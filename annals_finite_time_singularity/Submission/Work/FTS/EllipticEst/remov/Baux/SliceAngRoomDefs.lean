import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

noncomputable section

set_option autoImplicit false

/-!
# Vocabulary for the angular slice "room" construction (`SLICE-ANG(k)`)

`u` is a θ-slice, `v = u/cos θ` the `cos`-divided profile, `σ = sin(2θ)`, `q = σ^{2k-γ}`,
`W = σ·q`, `P = cos²θ·q`, `B` the "room" coefficient and `D` the flux of the room identity:

* `slice_ang_room_ident` (proved) gives the two pointwise product-rule identities;
* adding them (with the weights `-(k+2)sin²θq` and `(k+1)`) and integrating over `[a,b]` gives the
  **room integral identity**
  `∫ ( sinθcosθ v^{(k+1)}v^{(k+2)} - (k+2)sin²θ (v^{(k+1)})² + (k+1)cos²θ v^{(k)}v^{(k+2)} ) q
      = - ∫ B (v^{(k+1)})² q + ((k+1)/2)∫ (cos²θq)'' (v^{(k)})² + D(b) - D(a)`,
  with `B = ((2k+1-γ)/2)cos2θ + (k+2)sin²θ + (k+1)cos²θ = ((4k+3-γ)/2)cos²θ + ((3+γ)/2)sin²θ`,
  i.e. `B ≥ (3+γ)/2 > 0` on `Iθ`, and the flux
  `D = ¼σq(v^{(k+1)})² + (k+1)cos²θq v^{(k)}v^{(k+1)} - ½(k+1)(cos²θq)'(v^{(k)})²`.
-/

/-- `v = u / cos θ`. -/
def sv (u : ℝ → ℝ) : ℝ → ℝ := fun t => u t / Real.cos t

/-- `q = sin(2θ)^{2k-γ}`. -/
def sq (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)

/-- `W = sin(2θ)·q = 2 sinθ cosθ · q`. -/
def sW (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => Real.sin (2 * θ) * sq k γ θ

/-- `P = cos²θ · q`. -/
def sP (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => Real.cos θ ^ 2 * sq k γ θ

/-- The room coefficient
`B = ((2k+1-γ)/2)·cos2θ + (k+2)·sin²θ + (k+1)·cos²θ`.  On `(0,π/2)` it equals
`((4k+3-γ)/2)cos²θ + ((3+γ)/2)sin²θ`, so

`B - (3+γ)/2 = (2k-γ)·cos²θ`,

and hence `B ≥ (3+γ)/2 > 0` on `(0,π/2)` **provided `γ ≤ 2k`** (which holds in the intended
application `k ≥ 2`, `γ ≤ 5/4`). -/
def sB (k : ℕ) (γ : ℝ) : ℝ → ℝ :=
  fun θ => ((2 * (k : ℝ) + 1 - γ) / 2) * Real.cos (2 * θ)
    + ((k : ℝ) + 2) * Real.sin θ ^ 2 + ((k : ℝ) + 1) * Real.cos θ ^ 2

/-- The flux `D` of the room identity. -/
def sD (k : ℕ) (γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (1 / 4) * sW k γ θ * (iteratedDeriv (k + 1) (sv u) θ) ^ 2
    + ((k : ℝ) + 1) * sP k γ θ * iteratedDeriv k (sv u) θ
        * iteratedDeriv (k + 1) (sv u) θ
    - (1 / 2) * ((k : ℝ) + 1) * deriv (sP k γ) θ * (iteratedDeriv k (sv u) θ) ^ 2

end

end Work.FTS.EllipticEst.remov
