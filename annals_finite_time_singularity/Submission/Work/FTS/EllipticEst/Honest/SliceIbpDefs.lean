/-
Work module: the objects of the `θ`-slice integration by parts behind
`Work.FTS.EllipticEst.Honest.SliceIbpTheta`.

The lemma `SliceIbpTheta` computes

  `∫_θ f · f'' · sin(2θ)^{-η} = -∫_θ (f')² sin(2θ)^{-η} + 2η ∫_θ f² sin(2θ)^{-η}
      + 2η(1+η) ∫_θ f² cos²(2θ) sin(2θ)^{-(2+η)}`

for `f` of class `C²` on `[0, π/2]` vanishing at the endpoints and `η ∈ [0,1)`.  It is the
outcome of two integrations by parts against the singular weight `σ η θ = sin(2θ)^{-η}`.

This file only *names* the four functions that occur (the weight `σ η`, its derivative, and the
auxiliary weight `ρ η = cos(2θ)·sin(2θ)^{-η-1}` together with its derivative); it contains no
`sorry`.

* `sig η θ = sin(2θ)^{-η}`;
* `sigD η θ = -2η cos(2θ) sin(2θ)^{-η-1}` (so `sigD η θ = -2η · rho η θ`);
* `rho η θ = cos(2θ) sin(2θ)^{-η-1}`;
* `rhoD η θ = -2 sin(2θ)^{-η} - 2(η+1) cos²(2θ) sin(2θ)^{-(2+η)}`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

/-- The open angular interval `(0, π/2)`. -/
def Iθo : Set ℝ := Set.Ioo 0 (Real.pi / 2)

/-- `σ η θ = sin(2θ)^{-η}`, the singular angular weight. -/
def sig (η : ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-η)

/-- The derivative of `sigma η` on `(0, π/2)`:
`sigD η θ = -2η cos(2θ) sin(2θ)^{-η-1}`. -/
def sigD (η : ℝ) : ℝ → ℝ :=
  fun θ => -2 * η * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1)

/-- The auxiliary weight `rho η θ = cos(2θ) sin(2θ)^{-η-1}`; the point of it is that
`sigD η θ = -2η · rho η θ` and that `rho η` is exactly the weight whose weighted integration by
parts produces the third term of the identity. -/
def rho (η : ℝ) : ℝ → ℝ := fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η - 1)

/-- The derivative of `rho η` on `(0, π/2)`:
`rhoD η θ = -2 sin(2θ)^{-η} - 2(η+1) cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def rhoD (η : ℝ) : ℝ → ℝ := fun θ =>
  -2 * (Real.sin (2 * θ)) ^ (-η)
    - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))

/-- `sigD η` is `-2η` times `rho η`. -/
theorem sigD_eq_neg_two_mul_rho (η θ : ℝ) : sigD η θ = -2 * η * rho η θ := by
  simp only [sigD, rho]
  ring

theorem sig_apply (η θ : ℝ) : sig η θ = (Real.sin (2 * θ)) ^ (-η) := rfl

theorem rhoD_apply (η θ : ℝ) :
    rhoD η θ = -2 * (Real.sin (2 * θ)) ^ (-η)
      - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := rfl

end Work.FTS.EllipticEst.Honest
