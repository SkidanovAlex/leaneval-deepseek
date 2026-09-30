import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory Matrix

/-- The determinant of `Work.BW.transZ z` is the determinant of the matrix with rows `z j`. -/
theorem det_transZ {d : ℕ} (z : Fin d → Fin d → ℝ) :
    LinearMap.det (Work.BW.transZ z) = (Matrix.of (fun i j => z j i)).det := by
  rw [Work.BW.transZ, ← Matrix.toLin'_apply', LinearMap.det_toLin']

/-- The change of variables formula for `Work.BW.transZ z`: the Lebesgue measure of the
preimage of a set is the measure of the set divided by `|det|`. -/
theorem vol_preimage_transZ {d : ℕ} (z : Fin d → Fin d → ℝ)
    (hz : (Matrix.of (fun i j => z j i)).det ≠ 0) (S : Set (Fin d → ℝ)) :
    MeasureTheory.volume.real (Work.BW.transZ z ⁻¹' S)
      = MeasureTheory.volume.real S / |(Matrix.of (fun i j => z j i)).det| := by
  have hdet : LinearMap.det (Work.BW.transZ z) = (Matrix.of (fun i j => z j i)).det :=
    det_transZ z
  have hmain := Measure.addHaar_preimage_linearMap (MeasureTheory.volume : Measure (Fin d → ℝ))
    (f := Work.BW.transZ z) (by rw [hdet]; exact hz) S
  rw [Measure.real_def, Measure.real_def, hmain, hdet, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]

end Work.BW.Minkowski2
