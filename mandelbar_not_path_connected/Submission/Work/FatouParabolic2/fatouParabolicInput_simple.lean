/-
Copyright: subproject `Submission/Work/FatouParabolic2/` of `mandelbar_not_path_connected`.

# Fatou's result on parabolic cycles: the simple case

This module proves the headline result of the area,

> `Work.FatouParabolic2.fatouParabolicInput_simple : FatouParabolicInput_simple`,

i.e. the simple case of the classical input `Work.FatouParabolic.FatouParabolicInput`: for a
polynomial map `F` of degree `≥ 2` with a fixed point `z₀` of multiplier `1` whose second
derivative does not vanish, the basin of `z₀` contains a critical point of `F`.

## The route

1. `Work.FatouCoord.Flower.germ_bounds` normalises the germ of `F` at `z₀` to
   `f u = u + u ^ 2 * h u` on a ball of radius `r`, with the affine chart `u ↦ z₀ + lam * u`;
2. `Work.FatouParabolic2.exists_petalData_germ` gives petal data for `f` at `0` on the explicit
   Leau--Fatou petal `Work.FatouCoord.Petal r M`, with the explicit Fatou coordinate;
3. `Work.FatouParabolic2.transport_petalData` transports it along the affine chart to petal data
   for `F` at `z₀`;
4. `Work.FatouParabolic2.exists_criticalPoint_in_immBasin` (the Liouville/covering step) produces
   a critical point of `F` in the immediate basin of `z₀`, hence in the basin.

No antiholomorphic square root of `F` is used anywhere: the delivered Leau--Fatou theory
`Work.FatouCoord.exists_petal_fatouCoord` supplies the petal and the coordinate for every *simple*
parabolic germ, and the Liouville step only consumes the abstract petal interface `PetalData`.
-/
import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.exists_petalData_germ
import Submission.Work.FatouParabolic2.transport_petalData
import Submission.Work.FatouParabolic2.exists_criticalPoint_in_immBasin
import Submission.Work.FatouCoord.Flower.germ_bounds
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- **Petal data at a simple parabolic fixed point.**  Every holomorphic map `F` with
`F z₀ = z₀`, `deriv F z₀ = 1` and `iteratedDeriv 2 F z₀ ≠ 0` carries petal data at `z₀`: an
attracting petal with an injective holomorphic Fatou coordinate whose image exhausts the tails of
all horizontal strips, on which the orbits converge to `z₀` and every orbit converging to `z₀`
enters. -/
theorem exists_petalData_of_simple {F : ℂ → ℂ} {z₀ : ℂ} (hF : Differentiable ℂ F)
    (hfix : F z₀ = z₀) (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ ≠ 0) :
    Nonempty (PetalData F z₀) := by
  obtain ⟨f, h, a, r, A, A', lam, hlam, hb, hfeq⟩ :=
    Work.FatouCoord.Flower.germ_bounds hF hfix h1 h2
  obtain ⟨M, pd, hM, hPa, hφa⟩ := exists_petalData_germ hb
  have hPa_ball : pd.Pa ⊆ Metric.ball 0 r := by
    rw [hPa]
    exact Work.FatouCoord.Petal_subset_ball
  have hconj : ∀ u : ℂ, u ∈ Metric.ball 0 r → f u = (F (z₀ + lam * u) - z₀) / lam :=
    fun u hu => hfeq u hu
  obtain ⟨pd', -, -⟩ := transport_petalData pd hlam hPa_ball hconj
  exact ⟨pd'⟩

/-- **Fatou's result in the simple case, unfolded.**  A polynomial map `F` of degree `≥ 2` with a
simple multiplier-one fixed point has a critical point in the basin of that point. -/
theorem exists_criticalPoint_in_basin_of_simple {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ ≠ 0) :
    ∃ w : ℂ, Work.FatouParabolic.IsCriticalPoint F w ∧ w ∈ Work.FatouParabolic.basin F z₀ := by
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  obtain ⟨pd⟩ := exists_petalData_of_simple hFdiff hfix h1 h2
  obtain ⟨p₀, hp₀⟩ := pd.nonempty
  obtain ⟨w, hwΩ, hw0⟩ := exists_criticalPoint_in_immBasin hF hfix pd hp₀
  exact ⟨w, hw0, Work.FatouParabolic.Core.immBasin_subset_basin hwΩ⟩

/-- **Fatou's classical input on parabolic cycles, simple case.**  For a polynomial map `F` of
degree `≥ 2` and a fixed point `z₀` of multiplier `1` at which the second derivative does not
vanish, the basin of `z₀` contains a critical point of `F`.

This is the statement `Work.FatouParabolic.FatouParabolicInput` with the simplicity hypothesis
`iteratedDeriv 2 F z₀ ≠ 0`; the general input is recovered from it and the degenerate case by
`Work.FatouParabolic2.fatouParabolicInput_split`. -/
theorem fatouParabolicInput_simple : FatouParabolicInput_simple :=
  fun _F _z₀ hF hfix h1 h2 => exists_criticalPoint_in_basin_of_simple hF hfix h1 h2

end

end Work.FatouParabolic2
