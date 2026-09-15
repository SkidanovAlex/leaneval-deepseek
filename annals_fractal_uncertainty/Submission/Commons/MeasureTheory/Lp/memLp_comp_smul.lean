import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory Measure Module

namespace Commons.MeasureTheory.Lp

-- Precomposition with a (nonzero) scalar dilation preserves `MemLp`, with the change of the
-- underlying measure: `∫⁻ x, ‖f (c • x)‖^p = (c^d)⁻¹ * ∫⁻ x, ‖f x‖^p` for `c > 0`
-- (the map `x ↦ c • x` scales the Lebesgue measure by `c^d`).
theorem memLp_comp_smul {d : ℕ} {p : ENNReal} (hp : p ≠ 0)
    {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.MemLp f p (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    {c : ℝ} (hc : c ≠ 0) :
    MeasureTheory.MemLp (fun x => f (c • x)) p (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
  have hmap : Measure.map (fun x : EuclideanSpace ℝ (Fin d) => c • x)
        (volume : Measure (EuclideanSpace ℝ (Fin d)))
      = ENNReal.ofReal (abs (c ^ finrank ℝ (EuclideanSpace ℝ (Fin d)))⁻¹) • volume :=
    map_addHaar_smul volume hc
  have hmem : MemLp f p (Measure.map (fun x : EuclideanSpace ℝ (Fin d) => c • x)
      (volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have hae : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) => c • x) volume :=
    (continuous_const_smul c).aemeasurable
  exact hmem.comp_of_map hae

end Commons.MeasureTheory.Lp