import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

theorem IntegrableOfSqWeight {G : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hInt2 : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ 2 * |G s|) (Set.Ioi (0 : ℝ))) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s * G s) (Set.Ioi r) := by
  have hsub : Set.Ioi r ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hr.le
  rw [MeasureTheory.IntegrableOn] at hInt2 ⊢
  have hμle : MeasureTheory.volume.restrict (Set.Ioi r) ≤
      MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsub
  have hInt2' : MeasureTheory.Integrable (fun s : ℝ => s ^ 2 * |G s|)
      (MeasureTheory.volume.restrict (Set.Ioi r)) := hInt2.mono_measure hμle
  refine MeasureTheory.Integrable.mono' (hInt2'.const_mul (1 / r)) ?_ ?_
  · exact (continuous_id.aestronglyMeasurable).mul (hG.mono_measure hμle)
  · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hr hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx0]
    have hxr : x ≤ x ^ 2 / r := by
      have hxg : r < x := hx
      rw [le_div_iff₀ hr]
      nlinarith [hxg, hx0]
    calc x * |G x| ≤ (x ^ 2 / r) * |G x| := mul_le_mul_of_nonneg_right hxr (abs_nonneg _)
      _ = (1 / r) * (x ^ 2 * |G x|) := by ring

end Work.BoseFixR.LatGreen
