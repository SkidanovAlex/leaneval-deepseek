import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Band.BadFaceDefs

namespace Work.Drive.Mono.Band

/-- **The slab direction.**  If `e, n` are unit vectors with `16 * |⟪e, n⟫| < 1` then there is a
unit vector `v ⊥ n` within `1/8` of `e`: take `v` the unit vector in the direction of the orthogonal
projection `w = e - ⟪e,n⟫ • n` of `e` onto `n^⊥`.  Then `‖w‖² = 1 - ⟪e,n⟫²`,
`⟪(‖w‖)⁻¹ • w, e⟫ = ‖w‖`, so `‖v - e‖² = 2(1 - ‖w‖) ≤ 2·⟪e,n⟫²` and hence
`‖v - e‖ ≤ √2·|⟪e,n⟫| < √2/16 < 1/8`.

The estimates needed are `abs_mul`, `norm_smul`/`norm_smul_inv_norm`, `inner_sub_left`,
`inner_sub_right`, `real_inner_smul_left`, `real_inner_smul_right`, `real_inner_self_eq_norm_sq`,
`real_inner_comm` (note its argument order: `real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫`),
`norm_sub_sq_real`, and `Real.sqrt_le_sqrt`/`sq_le_sq` for the last step. -/
theorem exists_slab_direction {e n : LeanEval.KnotTheory.PardonDistortion.R3}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (ht : 16 * |inner ℝ e n| < 1) :
    ∃ v : LeanEval.KnotTheory.PardonDistortion.R3,
      ‖v‖ = 1 ∧ inner ℝ v n = 0 ∧ ‖v - e‖ ≤ 1 / 8 := by
  -- the scalar `c = ⟪e,n⟫`, the orthogonal projection `w = e - c • n` of `e` onto `n^⊥`.
  set c : ℝ := inner ℝ e n with hcdef
  have hcabs : |c| < 1 / 16 := by
    rw [hcdef]; nlinarith [ht]
  have hc2 : c ^ 2 < 1 / 256 := by
    have h := abs_lt.mp hcabs
    nlinarith [h.1, h.2]
  set w : LeanEval.KnotTheory.PardonDistortion.R3 := e - c • n with hwdef
  -- `w ⊥ n`
  have hwn : inner ℝ w n = 0 := by
    rw [hwdef, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn, ← hcdef]
    ring
  -- `⟪w, e⟫ = 1 - c²`
  have hwe : inner ℝ w e = 1 - c ^ 2 := by
    rw [hwdef, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he,
      ← real_inner_comm n e, ← hcdef]
    ring
  have hinner_sub : ∀ x : LeanEval.KnotTheory.PardonDistortion.R3,
      inner ℝ x w = inner ℝ x e - c * inner ℝ x n := by
    intro x
    rw [hwdef, inner_sub_right, real_inner_smul_right]
  -- `⟪w, w⟫ = 1 - c²`, hence `‖w‖² = 1 - c²`
  have hww : inner ℝ w w = 1 - c ^ 2 := by
    rw [hinner_sub w, hwe, hwn, mul_zero, sub_zero]
  have hwnorm : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; exact hww
  have hwpos : 0 < ‖w‖ := by
    have h : 0 < ‖w‖ ^ 2 := by rw [hwnorm]; nlinarith [hc2]
    exact lt_of_le_of_ne (norm_nonneg w) (Ne.symm (sq_pos_iff.mp h))
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwpos)
  have hvnorm : ‖(‖w‖)⁻¹ • w‖ = 1 := norm_smul_inv_norm hw0
  -- `⟪(‖w‖)⁻¹ • w, e⟫ = ‖w‖`
  have hvinv : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 = 2 * (1 - ‖w‖) := by
    have hve_inner : inner ℝ ((‖w‖)⁻¹ • w) e = ‖w‖ := by
      rw [real_inner_smul_left, hwe, ← hwnorm]
      field_simp
    rw [norm_sub_sq_real, hve_inner, he, hvnorm]
    ring
  have hle : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 ≤ 2 * c ^ 2 := by
    rw [hvinv]
    have hwle1 : ‖w‖ ≤ 1 := by
      have h : ‖w‖ ^ 2 ≤ 1 := by rw [hwnorm]; nlinarith [sq_nonneg c]
      nlinarith [norm_nonneg w]
    have hb : 1 - ‖w‖ ≤ c ^ 2 := by
      have h2 : ‖w‖ ^ 2 ≤ ‖w‖ := by nlinarith [hwle1, norm_nonneg w]
      nlinarith [hwnorm]
    linarith
  refine ⟨(‖w‖)⁻¹ • w, hvnorm, ?_, ?_⟩
  · rw [real_inner_smul_left, hwn, mul_zero]
  · have hfin : ‖(‖w‖)⁻¹ • w - e‖ ^ 2 ≤ (1 / 8) ^ 2 := by
      nlinarith [hle, hc2]
    have h := sq_le_sq.mp hfin
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h

end Work.Drive.Mono.Band
