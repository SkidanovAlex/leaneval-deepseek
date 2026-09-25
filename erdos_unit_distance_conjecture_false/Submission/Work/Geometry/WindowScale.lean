import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

set_option linter.unusedSectionVars false
open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

namespace Work
namespace Geometry

variable {K : Type*} [Field K] [NumberField K]

/-- The window is a cone: `B_r = r • B_1` for `0 < r`. -/
theorem Window_smul (r : ℝ) (hr : 0 < r) : Window K r = r • Window K 1 := by
  ext x
  rw [mem_window, Set.mem_smul_set]
  constructor
  · intro h
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · intro w
      rw [mixedEmbedding.normAtPlace_smul, abs_of_pos (inv_pos.mpr hr), inv_mul_lt_one₀ hr]
      exact h w
    · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩ w
    rw [mixedEmbedding.normAtPlace_smul, abs_of_pos hr]
    nlinarith [hy w]

/-- Scaling the window: `vol B_r = r ^ [K : ℚ] · vol B_1`. -/
theorem volume_Window_smul (r : ℝ) (hr : 0 < r) :
    volume (Window K r) =
      ENNReal.ofReal (r ^ Module.finrank ℚ K) * volume (Window K 1) := by
  rw [Window_smul r hr, Measure.addHaar_smul, mixedEmbedding.finrank,
    abs_of_nonneg (pow_nonneg hr.le _)]


/-- The window of radius `R - 1/2` has `(1 - 1/(2R)) ^ [K : ℚ]` times the volume of `B_R`. -/
theorem volume_Window_sub_half (R : ℝ) (hR : 1/2 < R) :
    ENNReal.ofReal ((1 - 1/(2*R)) ^ Module.finrank ℚ K) * volume (Window K R)
      = volume (Window K (R - 1/2)) := by
  have hR0 : 0 < R := by linarith
  have hRh : 0 < R - 1/2 := by linarith
  have hrho : 0 < 1 - 1/(2*R) := by
    have : 1/(2*R) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  rw [volume_Window_smul (K := K) R hR0, volume_Window_smul (K := K) (R - 1/2) hRh]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hrho.le _)]
  congr 2
  rw [← mul_pow]
  congr 1
  field_simp

end Geometry
end Work
