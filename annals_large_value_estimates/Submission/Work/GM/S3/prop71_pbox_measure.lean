import Mathlib
import Submission.Work.GM.S3.prop71_defs

namespace Work.GM.S3

/-- Auxiliary: the volume on `ℝ × ℝ` is the product of the volumes, definitionally. -/
private theorem volume_prod_eq :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod MeasureTheory.volume := rfl

/-- The measure of the region `pbox = [1/2,2] × [1/2,2]` where `w₂` can be nonzero:
`vol(pbox) = (3/2)² = 9/4`. Proof: `MeasureTheory.Measure.prod_prod`,
`Real.volume_Icc` and `ENNReal.toReal_ofReal` (the product `volume` on `ℝ × ℝ` needs a
`change`/`show` first). -/
theorem prop71_pbox_measure :
    ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pbox).toReal = 9 / 4 := by
  rw [pbox, volume_prod_eq, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ENNReal.toReal_mul]
  norm_num

end Work.GM.S3
