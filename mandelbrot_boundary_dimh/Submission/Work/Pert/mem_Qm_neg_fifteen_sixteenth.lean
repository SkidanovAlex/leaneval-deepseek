import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_slice

namespace Work.Pert

/-- The point `-(15/16)/α` sits in the lower gate `Qm Ξ α` as soon as `16 Ξ` is smaller than
`Re (1/α) + |Im (1/α)|` and `Ξ > 0`.

Indeed, writing `w = 1/α` and `W = w.re + |w.im|`, the two cone inequalities for the point
`z = -(15/16) w` read

* `Ξ - w.re - |w.im|/16 < -(15/16) w.re`, i.e. `16 Ξ < W`, and
* `-(15/16) w.re < (15/16) |w.im| - Ξ`, i.e. `Ξ < (15/16) W`,

the second following from the first because `Ξ > 0` forces `W > 0`. -/
theorem mem_Qm_neg_fifteen_sixteenth {Ξ : ℝ} {α : ℂ} (hΞ : 0 < Ξ)
    (h : 16 * Ξ < (1 / α).re + |(1 / α).im|) :
    ((-15 / 16 : ℝ) : ℂ) / α ∈ Work.Pert.Qm Ξ α := by
  set w : ℂ := 1 / α with hw
  have hz : ((-15 / 16 : ℝ) : ℂ) / α = ((-15 / 16 : ℝ) : ℂ) * w := by
    rw [hw, one_div, div_eq_mul_inv]
  rw [Qm_mem_iff, hz]
  have hre : (((-15 / 16 : ℝ) : ℂ) * w).re = (-15 / 16) * w.re := by simp
  have him : (((-15 / 16 : ℝ) : ℂ) * w).im = (-15 / 16) * w.im := by simp
  rw [hre, him]
  have habs : |((-15 / 16 : ℝ) * w.im) + w.im| = |w.im| / 16 := by
    have h1 : ((-15 / 16 : ℝ) * w.im) + w.im = (1 / 16) * w.im := by ring
    rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
    ring
  have habs2 : |((-15 / 16 : ℝ) * w.im)| = (15 / 16) * |w.im| := by
    rw [abs_mul, abs_of_neg (by norm_num : ((-15 / 16 : ℝ) < 0))]
    ring
  rw [habs, habs2]
  exact ⟨by linarith, by linarith⟩

end Work.Pert
