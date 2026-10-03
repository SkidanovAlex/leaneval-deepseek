import Mathlib

namespace Work.Pert.pert2v2

theorem walk_step_bounds {z w : ℂ} (h : ‖w - (z - 1)‖ ≤ 1 / 32) :
    z.re - 33 / 32 ≤ w.re ∧ w.re ≤ z.re - 31 / 32 ∧ |w.im - z.im| ≤ 1 / 32 := by
  have hre : |(w - (z - 1)).re| ≤ (1 : ℝ) / 32 :=
    le_trans (Complex.abs_re_le_norm _) h
  have him : |(w - (z - 1)).im| ≤ (1 : ℝ) / 32 :=
    le_trans (Complex.abs_im_le_norm _) h
  rw [Complex.sub_re, Complex.sub_re, Complex.one_re] at hre
  have hre' : |w.re - z.re + 1| ≤ (1 : ℝ) / 32 := by
    have : w.re - (z.re - 1) = w.re - z.re + 1 := by ring
    rwa [this] at hre
  have him' : (w - (z - 1)).im = w.im - z.im := by simp
  rw [him'] at him
  obtain ⟨hr1, hr2⟩ := abs_le.mp hre'
  exact ⟨by linarith, by linarith, him⟩

end Work.Pert.pert2v2
