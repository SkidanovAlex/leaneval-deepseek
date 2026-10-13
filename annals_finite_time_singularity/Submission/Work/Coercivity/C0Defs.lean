/-
# Auxiliary objects for the bound `|C0 f|² ≤ 32 Ef f` (`C0_sq_le`)

`C0 f = L₁₂(Transport f)(0)` is the constant of the projector-derivative term `Z7` of the
`D_z`-decomposition of `𝓛_Γ^T`.  This file fixes the objects appearing in the estimate

  `|C0 f|² ≤ 32 |f w|²_{L²}`

so that the main file and the delegated lemmas share them:

* `C0h` is the angular factor `h(θ) = 3 K(θ) sin(2θ)` of the density of
  `L₁₂(Transport f)`; it vanishes at `θ = 0` and `θ = π/2`, which is what makes the
  angular integration by parts of the estimate boundary-free;
* `C0g = h'` is its derivative, `18 sin θ cos²θ (2cos²θ - 3 sin²θ)`;
* `C0Ih = ∫_{Iθ} h'²` is the square of the `L²_θ`-norm of `h'`;
* `C0D = ∫_0^∞ (z(1+z)w(z))^{-2} dz` is the square of the `L²_z`-norm of the dual weight
  `1/(z(1+z)w(z))` (it equals `1/30`);
* `C0F f s = ∫_{Iθ} f(s,θ)² dθ` is the angular slice of the energy density of `f`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.zAux

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

/-- `h(θ) = 3 K(θ) sin(2θ)`: the angular factor of the density of `L₁₂(Transport f)`.
It vanishes at `θ = 0` and `θ = π/2`. -/
def C0h (θ : ℝ) : ℝ := 3 * Spaces.K θ * Real.sin (2 * θ)

/-- `h'(θ) = 18 sin θ cos²θ (2 cos²θ - 3 sin²θ)`, the derivative of `C0h`. -/
def C0g (θ : ℝ) : ℝ :=
  18 * Real.sin θ * Real.cos θ ^ 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2)

/-- `Ih = ∫_{Iθ} h'(θ)² dθ`. -/
def C0Ih : ℝ := ∫ θ in Spaces.Iθ, (C0g θ) ^ 2

/-- `D = ∫_0^∞ (z(1+z)w(z))^{-2} dz`; it equals `1/30`. -/
def C0D : ℝ := ∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s) * Spaces.w s)) ^ 2

/-- `F f (s) = ∫_{Iθ} f(s,θ)² dθ`. -/
def C0F (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ θ in Spaces.Iθ, (f s θ) ^ 2

end Work.Coercivity
