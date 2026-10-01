import Mathlib

namespace Work.ZeroDensity.Ingham

open MeasureTheory

/-- Translation invariance of the Lebesgue integral over a half-line:
`∫_{v > H} f v = ∫_{s > 0} f (s + H)`. -/
theorem setIntegral_Ioi_add_const (f : ℝ → ℝ) (H : ℝ) :
    (∫ v in Set.Ioi H, f v) = ∫ s in Set.Ioi 0, f (s + H) := by
  have hemb : MeasurableEmbedding (fun s : ℝ => s + H) := by
    simpa only [Homeomorph.coe_addRight] using (Homeomorph.addRight H).measurableEmbedding
  have hpre : (fun s : ℝ => s + H) ⁻¹' Set.Ioi H = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hmap : Measure.map (fun s : ℝ => s + H) (volume : Measure ℝ) = volume :=
    MeasureTheory.map_add_right_eq_self volume H
  have hrestr : volume.restrict (Set.Ioi H)
      = Measure.map (fun s : ℝ => s + H) (volume.restrict (Set.Ioi 0)) := by
    calc volume.restrict (Set.Ioi H)
        = (Measure.map (fun s : ℝ => s + H) (volume : Measure ℝ)).restrict (Set.Ioi H) := by
            rw [hmap]
      _ = Measure.map (fun s : ℝ => s + H)
            (volume.restrict ((fun s : ℝ => s + H) ⁻¹' (Set.Ioi H))) :=
            hemb.restrict_map volume (Set.Ioi H)
      _ = Measure.map (fun s : ℝ => s + H) (volume.restrict (Set.Ioi 0)) := by rw [hpre]
  rw [hrestr, hemb.integral_map]

end Work.ZeroDensity.Ingham
