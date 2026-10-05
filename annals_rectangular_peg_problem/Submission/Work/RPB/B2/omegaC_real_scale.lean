import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPB.B2

open Complex

/-- The imaginary part of a real multiple: `Im (r * z) = r * Im z`. -/
private lemma ofReal_mul_im (r : ℝ) (z : ℂ) : ((r : ℂ) * z).im = r * z.im := by
  simp [Complex.mul_im]

theorem omegaC_real_scale (l : ℝ) (w wd : ℂ) (hl : l ≠ 0) :
    Work.RPV.ωC ((l : ℂ) * w) ((l : ℂ) * wd) / ‖(l : ℂ) * w‖ ^ 2
      = Work.RPV.ωC w wd / ‖w‖ ^ 2 := by
  have h1 : Work.RPV.ωC ((l : ℂ) * w) ((l : ℂ) * wd) = l ^ 2 * Work.RPV.ωC w wd := by
    have hc : (starRingEnd ℂ) ((l : ℂ) * w) * ((l : ℂ) * wd)
        = ((l ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) w * wd) := by
      rw [map_mul, Complex.conj_ofReal]; push_cast; ring
    simp only [Work.RPV.ωC, hc, ofReal_mul_im]
  have h2 : ‖(l : ℂ) * w‖ ^ 2 = l ^ 2 * ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    ring
  rw [h1, h2]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hl)

end Work.RPB.B2
