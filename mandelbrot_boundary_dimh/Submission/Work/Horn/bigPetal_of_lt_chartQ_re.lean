import Mathlib
import Submission.Work.Horn.flower_defs

namespace Work.Horn

/-- `Re (c * conj w) = Re (c / w) * ‖w‖²` for `w ≠ 0`: the root disc `DM` condition
`M * ‖w‖² < Re (c * conj w)` is exactly `M < Re (c / w)`. -/
private lemma re_mul_star_eq_re_div_mul_normSq (c w : ℂ) (hw : w ≠ 0) :
    (c * star w).re = (c / w).re * Complex.normSq w := by
  have h1 : c * star w = (c / w) * (w * star w) := by field_simp
  have h2 : w * star w = ((Complex.normSq w : ℝ) : ℂ) := by
    rw [Complex.star_def]; exact Complex.mul_conj w
  rw [h1, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem bigPetal_of_lt_chartQ_re {q : ℕ} {a z : ℂ} {M : ℝ} (hz : z ≠ 0)
    (h : M < (Work.Horn.Flower.chartQ q a z).re) :
    z ∈ Work.Horn.Flower.bigPetal q a M := by
  rw [Flower.bigPetal, Set.mem_ofPred_eq, Flower.DM, Set.mem_ofPred_eq]
  have hw : z ^ q ≠ 0 := pow_ne_zero _ hz
  have hns : 0 < Complex.normSq (z ^ q) := Complex.normSq_pos.mpr hw
  have key : (Flower.cc q a * star (z ^ q)).re
      = (Flower.chartQ q a z).re * Complex.normSq (z ^ q) := by
    rw [Flower.chartQ]
    exact re_mul_star_eq_re_div_mul_normSq (Flower.cc q a) (z ^ q) hw
  rw [key]
  exact mul_lt_mul_of_pos_right h hns

end Work.Horn
