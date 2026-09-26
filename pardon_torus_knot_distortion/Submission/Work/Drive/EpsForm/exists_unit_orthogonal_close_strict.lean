import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion

/-- Given a unit vector `e` and a nonzero vector `n` making a small angle with `e`
(`|⟪n,e⟫| ≤ ‖n‖/16`), there is a unit vector `v` orthogonal to `n` and close to `e`
(`‖v - e‖ ≤ 1/8`).  This is the elementary "near-normal to a direction" input used
elsewhere in the ε-form.  It sharpens `exists_unit_orthogonal_close` (constant `2/13`).

Proof: take `w` to be the orthogonal projection of `e` away from the span of `n`,
`w = e - (⟪n,e⟫/‖n‖²) n`, and set `v = ‖w‖⁻¹ • w`.  Then `⟪n,w⟫ = 0`, so `⟪n,v⟫ = 0`,
`‖w‖² = 1 - ⟪n,e⟫²/‖n‖² ≥ 255/256 ≥ (127/128)²`, and `⟪v,e⟫ = ‖w‖`, whence
`‖v-e‖² = 2 - 2‖w‖ ≤ 2 - 2·(127/128) = 1/64`. -/
theorem exists_unit_orthogonal_close_strict {e n : LeanEval.KnotTheory.PardonDistortion.R3} (he : ‖e‖ = 1) (hn : 0 < ‖n‖)
    (hc : |inner ℝ n e| ≤ ‖n‖ / 16) :
    ∃ v : LeanEval.KnotTheory.PardonDistortion.R3, ‖v‖ = 1 ∧ inner ℝ n v = 0 ∧ ‖v - e‖ ≤ 1 / 8 := by
  set w : R3 := e - (inner ℝ n e / ‖n‖ ^ 2) • n with hw
  have hN2 : (0 : ℝ) < ‖n‖ ^ 2 := by positivity
  have hN2ne : ‖n‖ ^ 2 ≠ 0 := ne_of_gt hN2
  -- `⟪n, w⟫ = 0`
  have hwn : inner ℝ n w = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq n,
      div_mul_cancel₀ _ hN2ne, sub_self]
  have hwwn : inner ℝ w n = 0 := by rw [real_inner_comm]; exact hwn
  -- `⟪w, e⟫ = 1 - ⟪n,e⟫²/‖n‖²`
  have hwe : inner ℝ w e = 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by
    rw [hw, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq e, he]
    field_simp
  have hwwe : inner ℝ w w = inner ℝ w e := by
    nth_rewrite 2 [hw]
    rw [inner_sub_right, inner_smul_right, hwwn, mul_zero, sub_zero]
  have hwself : inner ℝ w w = 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by
    rw [hwwe, hwe]
  have hwnorm : ‖w‖ ^ 2 = 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq w]
    exact hwself
  -- the angle bound
  have ha2 : (inner ℝ n e) ^ 2 ≤ (‖n‖ / 16) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖n‖ / 16)]
    exact hc
  have hfrac : (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 ≤ 1 / 256 := by
    rw [div_le_iff₀ hN2]
    nlinarith [ha2]
  have hlow : (255 : ℝ) / 256 ≤ 1 - (inner ℝ n e) ^ 2 / ‖n‖ ^ 2 := by nlinarith
  have hwge : (255 : ℝ) / 256 ≤ ‖w‖ ^ 2 := by rw [hwnorm]; exact hlow
  have hwpos : 0 < ‖w‖ := by
    refine lt_of_le_of_ne (norm_nonneg w) (Ne.symm ?_)
    intro h
    have h2 : (0 : ℝ) < ‖w‖ ^ 2 := by nlinarith
    rw [h] at h2
    norm_num at h2
  have hv1 : ‖(‖w‖)⁻¹ • w‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]
    exact inv_mul_cancel₀ (ne_of_gt hwpos)
  have hv2 : inner ℝ n ((‖w‖)⁻¹ • w) = 0 := by
    rw [inner_smul_right, hwn, mul_zero]
  have hve : inner ℝ ((‖w‖)⁻¹ • w) e = ‖w‖ := by
    rw [real_inner_smul_left, hwe, ← hwnorm, sq, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hwpos), one_mul]
  refine ⟨(‖w‖)⁻¹ • w, hv1, hv2, ?_⟩
  have h127 : (127 : ℝ) / 128 ≤ ‖w‖ := by
    have hsq' : ((127 : ℝ) / 128) ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [hwge]
    have hsq'' := sq_le_sq.mp hsq'
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 127 / 128),
      abs_of_nonneg (norm_nonneg w)] at hsq''
  have hsq : ‖((‖w‖)⁻¹ • w) - e‖ ^ 2 ≤ (1 / 8) ^ 2 := by
    rw [norm_sub_sq_real, hv1, he, hve]
    nlinarith [h127]
  have hfinal := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)] at hfinal

end Work.Drive.EpsForm
