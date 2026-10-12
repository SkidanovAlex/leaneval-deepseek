import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.DLInfra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.cutoffDefs` — the product-plateau cutoff for the sliding box

Holder of `Work.BoseFixB1B.exists_smoothCutoff`.

The requested cutoff `γ_δ` of the sliding box `B(u) = dlBox ℓ d u` is a product of six
**one-dimensional plateau factors**: three probe the coordinates of `x` and three those of
`x - (ℓd)•u`,

  `cutFun c f g x = f (x 0) * f (x 1) * f (x 2) * g ((x-c) 0) * g ((x-c) 1) * g ((x-c) 2)`,

with `f = plateau (ℓ/2) δ`, `g = plateau (ℓd/2) δ` and

  `plateau A δ t = σ((t+A)/δ) · σ((A-t)/δ)`,  `σ = Real.smoothTransition`.

The reason the product form is the right one: the region `{x | boxMargin ℓ d u x ≥ δ}` is
*exactly* the product of the six slabs `|x i| ≤ ℓ/2 - δ`, `|(x - (ℓd)•u) i| ≤ ℓd/2 - δ`, so a
product of one-dimensional factors can be `1` exactly there, while its support is contained in
the product of the closed slabs, i.e. in `dlBox ℓ d u`; and the derivative bound `C/δ` is then
just the sum of six one-dimensional Lipschitz constants, each `2K/δ`.

The properties of `plateau` (smoothness, `[0,1]`-valuedness, `= 1` for `|t| ≤ A - δ`, `= 0` for
`A ≤ |t|`, Lipschitz constant `2K/δ`) are proved in the sibling modules `plateauBasic`,
`plateauLip`; the properties of `cutFun` in `cutFunLip`, `cutFunSupport`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The one-dimensional plateau factor of half-width `A` and transition width `δ`:

`plateau A δ t = σ((t+A)/δ) · σ((A-t)/δ)` where `σ = Real.smoothTransition` is the standard
smooth step (`σ = 0` on `(-∞,0]`, `σ = 1` on `[1,∞)`).

It is `1` for `|t| ≤ A - δ` (`δ ≤ A`) and `0` for `|t| ≥ A`; the transition region has width
`2δ`, so the Lipschitz constant is `2·(Lip σ)/δ`. -/
noncomputable def plateau (A δ : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((t + A) / δ) * Real.smoothTransition ((A - t) / δ)

/-- The cutoff of the sliding box as a product of six one-dimensional factors: three in the
coordinates of `x` (through `f`), three in the coordinates of `x - c` (through `g`). -/
noncomputable def cutFun (c : ℝ³) (f g : ℝ → ℝ) : ℝ³ → ℝ :=
  fun x => f (x 0) * f (x 1) * f (x 2) * g ((x - c) 0) * g ((x - c) 1) * g ((x - c) 2)

/-- **Coordinate differences are bounded by the norm** (in `EuclideanSpace ℝ (Fin 3)`). -/
lemma abs_coord_sub_le_norm (x y : ℝ³) (i : Fin 3) : |y i - x i| ≤ ‖y - x‖ := by
  have h := Submission.BoseGases.abs_coord_le_norm (y - x) i
  simpa using h

end Work.BoseFixB1B
