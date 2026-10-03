import Mathlib

/-!
# Horizontal mass of a holomorphic function on a vertical strip

Helper definitions for `Work.FatouL1.exists_small_horizontal`.

For `g : ℂ → ℂ` and reals `x₁ x₂ y`, `horizMass g x₁ x₂ y` is the total mass of `‖g‖`
along the horizontal segment `t ↦ t + y * I`, `t ∈ (x₁, x₂]`, as an `ENNReal`-valued
(Lebesgue) integral.
-/

namespace Work.FatouL1

open MeasureTheory

set_option autoImplicit false

/-- The `‖g‖`-mass of `g` along the horizontal line at height `y`, over `t ∈ (x₁, x₂]`. -/
noncomputable def horizMass (g : ℂ → ℂ) (x₁ x₂ : ℝ) (y : ℝ) : ENNReal :=
  ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖

end Work.FatouL1
