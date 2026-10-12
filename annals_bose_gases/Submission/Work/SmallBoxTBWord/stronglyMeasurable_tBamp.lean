import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open MeasureTheory

/-- **Strong measurability of the windowed amplitude in the configuration.**  For a continuous
window `χ` and a measurable state `Φ`, the amplitude `x ↦ tBamp χ p Φ i x` is the parametric
Bochner integral of the jointly strongly measurable integrand
`(x,z) ↦ χ(z)·e^{−i⟪p,z⟫}·Φ(x_{i←z})`, hence strongly measurable in `x`
(`MeasureTheory.StronglyMeasurable.integral_prod_right'`; no integrability hypothesis). -/
theorem stronglyMeasurable_tBamp {N : ℕ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχc : Continuous χ) {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) (i : Fin N)
    (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.StronglyMeasurable (fun x : Submission.BoseGases.X N =>
      Work.SmallBoxTBWord.tBamp χ p Φ i x) := by
  -- The joint integrand `(x, z) ↦ χ z·e^{−i⟪p,z⟫}·Φ(x_{i←z})` is strongly measurable:
  -- `χ z` is strongly measurable as a continuous function of `z`, the exponential is
  -- continuous, and `Φ (x_{i←z})` is the composition of the measurable `Φ : X N → ℝ` with
  -- the jointly measurable slot update `(x, z) ↦ x_{i←z}` (`measurable_update'`).
  have h : StronglyMeasurable
      (fun xz : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
        (χ xz.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p xz.2 : ℂ))) *
          (Φ (Function.update xz.1 i xz.2) : ℂ)) := by
    fun_prop
  simpa only [tBamp] using h.integral_prod_right' (ν := volume)

end Work.SmallBoxTBWord
