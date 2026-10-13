/-
# Additivity of `H1IP`: the weighted blocks and the honest-pairing predicate

The `ℋ¹` inner product `H1IP α` is a sum of four weighted `L²` pairings

  `wip ρ A B = ∫_{z∈[0,∞)} ∫_{θ∈[0,π/2]} A z θ * B z θ * ρ z θ`

with weights `ρη = w²·sin(2θ)^{-η}` (three times: on `D_z f·D_z g`, on `f·g` and — with
weight `w²` — again on `f·g`) and `ργ = w²·sin(2θ)^{-γ}` (on `D_θ f·D_θ g`).

For *smooth* profiles each of these pairings is an honest absolutely convergent Lebesgue
integral, because every ingredient is an `L²`-function in the `H¹`-integrand: writing

* `Xeta f  = f · w/√(sin 2θ^η)`     (`= U0 f`),
* `XetaDz f = D_z f · w/√(sin 2θ^η)` (`= U1 f`),
* `XgamDth α f = D_θ f · W`         (`= U2 α f`, `W = w·sin(2θ)^{-γ/2}`),
* `Xw f = f · w`

for the four weighted blocks, the pairing integrands are the *products*

* `D_z a · D_z b · ρη = XetaDz a · XetaDz b`,
* `a · b · ρη = Xeta a · Xeta b`,
* `a · b · w² = Xw a · Xw b`,
* `D_θ a · D_θ b · ργ = XgamDth α a · XgamDth α b`

of two blocks whose squares are `L²` by `HkMem α 1`; Cauchy–Schwarz then gives the
absolute convergence, hence the additivity of `wip` in its first argument.  This file
fixes the vocabulary (the weights, the blocks, and the predicate `PairHonest` saying
that the iterated integral of a pairing integrand is honest).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EzDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The weights of the four pairings -/

/-- The weight `w(z)² · sin(2θ)^{-η}` of the three `η`-pairings of `H1IP`. -/
def lamEta (z θ : ℝ) : ℝ := Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)

/-- The weight `w(z)² · sin(2θ)^{-γ}` of the `D_θ`-pairing of `H1IP`. -/
def lamGam (α : ℝ) (z θ : ℝ) : ℝ := Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- The plain weight `w(z)²` of the third pairing of `H1IP`. -/
def lamW (z θ : ℝ) : ℝ := Spaces.w z ^ 2

/-- The open quadrant `(0,∞) × (0,π/2)`, on which all the blocks are continuous. -/
def QdOp : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-! ## The honest-pairing predicate -/

/-- `PairHonest ρ A B` says that the pairing integrand `A·B·ρ` has an honest iterated
integral over the quadrant `[0,∞) × [0,π/2]`: every angular slice is integrable, and the
resulting function of `z` is integrable.  Under this hypothesis `wip ρ A B` is a genuine
Lebesgue integral and `wip` is additive in `A`. -/
def PairHonest (ρ A B : ℝ → ℝ → ℝ) : Prop :=
  I2Mem (fun z θ => A z θ * B z θ * ρ z θ)

/-! ## The four weighted blocks -/

/-- `f · w/√(sin 2θ^η)`, the `D_z⁰`-block of the `ℋ¹` integrand (`= U0 f`). -/
def Xeta (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- `D_z f · w/√(sin 2θ^η)`, the `D_z¹`-block (`= U1 f`). -/
def XetaDz (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.Dz f z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))

/-- `D_θ f · W`, the `D_θ`-block (`= U2 α f`). -/
def XgamDth (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.Dth f z θ * Spaces.Wt α z θ

/-- `f · w`, the block of the plain `w²`-pairing. -/
def Xw (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ * Spaces.w z

end Work.Coercivity
