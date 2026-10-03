import Mathlib
import Submission.Work.Pert.pert2v2.walkY2

namespace Work.Pert.pert2v2

/-- **The deep threshold bound of the right walk.**  On the lower gate `Qm Ξ α`, at heights below
`-walkY2 Ξ x₀ α`, the lower margin dominates `5/4 + (17/16) · 32 (z.re - x₀ - 3)/31`.

The gate gives `margB_g Ξ z = |z.im| - Ξ - z.re > 0`, i.e. `z.re < |z.im| - Ξ`, while
`margA_g Ξ α z ≥ z.re - |Ξ| + |z.im| - 2‖1/α‖` (triangle inequality for the imaginary part and
`-‖w‖ ≤ w.re`).  Substituting `z.re = (z.re - x₀ - 3) + x₀ + 3` turns the claim into the single
linear inequality

`(28/31) Q - (34/31)(A + B) - 2 N + 102/31 - 5/4 ≥ 0`,  `Q = |z.im|`, `A = |x₀|`, `B = |Ξ|`,
`N = ‖1/α‖`,

which is what the threshold `Q ≥ 16 (A + B + N + 4) + 16` of `walkY2` is made for. -/
theorem margA_deep_bound {Ξ x₀ : ℝ} {α : ℂ} {z : ℂ}
    (hz : z ∈ Work.Pert.Qm Ξ α) (hzim : z.im ≤ - Work.Pert.pert2v2.walkY2 Ξ x₀ α)
    (hzre : x₀ + 3 ≤ z.re) :
    5 / 4 + (17 / 16) * (32 * (z.re - x₀ - 3) / 31) ≤ Work.Pert.margA_g Ξ α z := by
  have hN0 : (0 : ℝ) ≤ ‖(1 : ℂ) / α‖ := norm_nonneg _
  have hWpos : 0 < Work.Pert.pert2v2.walkY2 Ξ x₀ α :=
    Work.Pert.pert2v2.walkY2_pos Ξ x₀ α
  have him_neg : z.im < 0 := lt_of_le_of_lt hzim (neg_lt_zero.mpr hWpos)
  have hQabs : |z.im| = -z.im := abs_of_neg him_neg
  have hQwalk : Work.Pert.pert2v2.walkY2 Ξ x₀ α ≤ |z.im| := by rw [hQabs]; linarith
  have hQwalk' : 16 * (|x₀| + |Ξ| + ‖(1 : ℂ) / α‖ + 4) + 16 ≤ |z.im| := by
    simpa only [Work.Pert.pert2v2.walkY2] using hQwalk
  -- the upper margin of the gate is positive, so `z.re < |z.im| - Ξ`
  have hB : 0 < Work.Pert.margB_g Ξ z := ((Work.Pert.mem_Qm_iff_g z).mp hz).2
  have hre_lt : z.re < |z.im| - Ξ := by
    rw [Work.Pert.margB_g] at hB; linarith
  -- the lower triangle bound on `margA_g`
  have him_abs : |z.im| - |((1 : ℂ) / α).im| ≤ |z.im + ((1 : ℂ) / α).im| := by
    have h := abs_add_le (z.im + ((1 : ℂ) / α).im) (-((1 : ℂ) / α).im)
    have he : (z.im + ((1 : ℂ) / α).im) + (-((1 : ℂ) / α).im) = z.im := by ring
    rw [he, abs_neg] at h
    linarith
  have him_le : |((1 : ℂ) / α).im| ≤ ‖(1 : ℂ) / α‖ := Complex.abs_im_le_norm _
  have hre_ge : -‖(1 : ℂ) / α‖ ≤ ((1 : ℂ) / α).re := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) / α)
    linarith [neg_abs_le ((1 : ℂ) / α).re]
  have hA : z.re - |Ξ| + |z.im| - 2 * ‖(1 : ℂ) / α‖ ≤ Work.Pert.margA_g Ξ α z := by
    rw [Work.Pert.margA_g]
    linarith [neg_le_neg (le_abs_self Ξ)]
  -- the five nonnegative pieces of the linear inequality
  have hT1 : 0 ≤ (3 / 31 : ℝ) * (|z.im| - Ξ - z.re) :=
    mul_nonneg (by norm_num) (by linarith)
  have hT2 : 0 ≤ (3 / 31 : ℝ) * (|Ξ| + Ξ) :=
    mul_nonneg (by norm_num) (by linarith [neg_abs_le Ξ])
  have hT3 : 0 ≤ (28 / 31 : ℝ) * (|z.im| - (16 * (|x₀| + |Ξ| + ‖(1 : ℂ) / α‖ + 4) + 16)) :=
    mul_nonneg (by norm_num) (by linarith)
  have hT4 : 0 ≤ (34 / 31 : ℝ) * (|x₀| + x₀) :=
    mul_nonneg (by norm_num) (by linarith [neg_abs_le x₀])
  have hT5 : 0 ≤ (414 / 31 : ℝ) * |x₀| + (414 / 31) * |Ξ| + (386 / 31) * ‖(1 : ℂ) / α‖
      + (2342 / 31 - 5 / 4) := by
    have h1 := abs_nonneg x₀
    have h2 := abs_nonneg Ξ
    linarith
  have hsum : 0 ≤ (3 / 31 : ℝ) * (|z.im| - Ξ - z.re) + (3 / 31) * (|Ξ| + Ξ)
      + (28 / 31) * (|z.im| - (16 * (|x₀| + |Ξ| + ‖(1 : ℂ) / α‖ + 4) + 16))
      + (34 / 31) * (|x₀| + x₀)
      + ((414 / 31) * |x₀| + (414 / 31) * |Ξ| + (386 / 31) * ‖(1 : ℂ) / α‖
          + (2342 / 31 - 5 / 4)) := by
    linarith [hT1, hT2, hT3, hT4, hT5]
  have hid : (3 / 31 : ℝ) * (|z.im| - Ξ - z.re) + (3 / 31) * (|Ξ| + Ξ)
      + (28 / 31) * (|z.im| - (16 * (|x₀| + |Ξ| + ‖(1 : ℂ) / α‖ + 4) + 16))
      + (34 / 31) * (|x₀| + x₀)
      + ((414 / 31) * |x₀| + (414 / 31) * |Ξ| + (386 / 31) * ‖(1 : ℂ) / α‖
          + (2342 / 31 - 5 / 4))
      = (z.re - |Ξ| + |z.im| - 2 * ‖(1 : ℂ) / α‖)
        - (5 / 4 + (34 / 31) * (z.re - x₀ - 3)) := by
    ring
  have hm := hid ▸ hsum
  have hkey : 5 / 4 + (34 / 31) * (z.re - x₀ - 3) ≤ Work.Pert.margA_g Ξ α z :=
    le_trans (by linarith) hA
  have heq : 5 / 4 + (17 / 16) * (32 * (z.re - x₀ - 3) / 31)
      = 5 / 4 + (34 / 31) * (z.re - x₀ - 3) := by ring
  rw [heq]; exact hkey

end Work.Pert.pert2v2
