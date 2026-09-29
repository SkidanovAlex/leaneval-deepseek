import Mathlib
import Submission.Work.A14D.setup

namespace Work.A14D

/-- On the slit disc `slitDisk δ = ball (1/9) δ ∩ slitComp` with `δ ≤ 8/9` the leading
coefficient `PZ` never vanishes.  (Modules: `Submission.Work.A14D.setup` for `PZ`, `ninth`,
`slitDisk`, `mem_slitDisk_iff`.)

Reason: `PZ z = -9 * z * (1 - z) * (z - 1/9)`; the three possible zeros are `0`, `1/9` (both on the
slit `{Im = 0, Re ≤ 1/9}`) and `1` (at distance `8/9 ≥ δ` from the centre `1/9`, hence outside
`ball (1/9) δ`). -/
theorem PZ_ne_zero_of_mem_slitDisk {δ : ℝ} (hδ8 : δ ≤ 8 / 9) {z : ℂ}
    (hz : z ∈ slitDisk δ) : PZ z ≠ 0 := by
  rw [mem_slitDisk_iff] at hz
  obtain ⟨hb, hcomp⟩ := hz
  have hb' : dist z ninth < δ := Metric.mem_ball.mp hb
  have him9 : ninth.im = 0 := by simp [ninth]
  have hre9 : ninth.re = 1 / 9 := by simp [ninth]
  intro hPZ
  rw [PZ] at hPZ
  have hfac : z * (1 - z) * (1 - 9 * z) = 0 := hPZ
  rcases mul_eq_zero.mp hfac with h1 | h9
  · rcases mul_eq_zero.mp h1 with h0 | h1'
    · -- `z = 0` lies on the slit
      rcases hcomp with him | hre
      · rw [h0] at him; simp at him
      · rw [h0] at hre; rw [hre9] at hre; norm_num at hre
    · -- `z = 1` is at distance `8/9` from the centre
      have hz1 : z = 1 := by linear_combination -h1'
      rw [hz1] at hb'
      have hd : dist (1 : ℂ) ninth = 8 / 9 := by
        rw [Complex.dist_eq]; norm_num [ninth]
      rw [hd] at hb'
      linarith
  · -- `z = 1/9` lies on the slit
    have hz9 : z = ninth := by
      rw [sub_eq_zero] at h9
      rw [ninth, eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination -h9
    rcases hcomp with him | hre
    · rw [hz9] at him; rw [him9] at him; exact him rfl
    · rw [hz9] at hre; rw [hre9] at hre; norm_num at hre

end Work.A14D
