import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option linter.unusedVariables false

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory.Lp

theorem eLpNorm_comp_smul_toReal {d : ℕ} {c : ℝ} (hc : 0 < c)
    {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
    (MeasureTheory.eLpNorm (fun x => f (c • x)) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).toReal
      = ((c ^ d)⁻¹) ^ (1 / 2 : ℝ) * (MeasureTheory.eLpNorm f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).toReal := by
  have hc_ne : c ≠ 0 := hc.ne'
  have hcd_nonneg : (0 : ℝ) ≤ (c ^ d)⁻¹ := by positivity
  have hr : (1 / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hmap : Measure.map (fun x : EuclideanSpace ℝ (Fin d) => c • x) MeasureTheory.volume
      = ENNReal.ofReal ((c ^ d)⁻¹) • MeasureTheory.volume := by
    rw [Measure.map_addHaar_smul MeasureTheory.volume hc_ne, finrank_euclideanSpace,
      Fintype.card_fin, abs_of_nonneg hcd_nonneg]
  have hemb : MeasurableEmbedding (fun x : EuclideanSpace ℝ (Fin d) => c • x) :=
    (Homeomorph.smulOfNeZero c hc_ne).measurableEmbedding
  have hcomp : MeasureTheory.eLpNorm (fun x => f (c • x)) 2 MeasureTheory.volume
      = MeasureTheory.eLpNorm f 2
          (Measure.map (fun x : EuclideanSpace ℝ (Fin d) => c • x) MeasureTheory.volume) :=
    (hemb.eLpNorm_map_measure (μ := MeasureTheory.volume) (g := f) (p := 2)).symm
  have hsmul : MeasureTheory.eLpNorm f 2 (ENNReal.ofReal ((c ^ d)⁻¹) • MeasureTheory.volume)
      = ENNReal.ofReal ((c ^ d)⁻¹) ^ (1 / 2 : ℝ≥0∞).toReal
          • MeasureTheory.eLpNorm f 2 MeasureTheory.volume :=
    eLpNorm_smul_measure_of_ne_top (by norm_num) f (ENNReal.ofReal ((c ^ d)⁻¹))
  rw [hcomp, hmap, hsmul, smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hcd_nonneg, hr]

end Commons.MeasureTheory.Lp