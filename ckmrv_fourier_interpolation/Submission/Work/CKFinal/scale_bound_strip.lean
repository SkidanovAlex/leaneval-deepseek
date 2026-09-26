import Mathlib
import Submission.Work.CKFinal.EngineDefs

/-!
# `scale_bound_strip`

On the strip `{im τ ≥ 3/2}` the paper's scale `S τ = 1 + (Im τ)⁻¹ + |τ|` is comparable to
`1 + |τ|`: the two auxiliary summands `1` and `(Im τ)⁻¹` are bounded there (`1 ≤ 2/3 < 1 + |τ|`),
so

  `S τ ≤ (5/3) * (1 + |τ|)`   and   `1 ≤ S τ`.

Hence for arbitrary real `C`, `N` the expression `C * S τ ^ N` is dominated by `K * (1 + |τ|) ^ A`
for suitable `K, A ≥ 0`:  take `A = max N 0`, and absorb the positive part of `C` into `K`
(if `C ≤ 0` the left-hand side is `≤ 0`).
-/

noncomputable section

namespace Work.CKFinal

/-- On the strip `3/2 ≤ im τ` the scale is at most `(5/3)` times `1 + |τ|`. -/
private lemma scale_le_strip (τ : UpperHalfPlane) (hτ : 3 / 2 ≤ τ.im) :
    Work.Kernels.scale τ ≤ (5 / 3) * (1 + ‖(τ : ℂ)‖) := by
  have hinv : (τ.im)⁻¹ ≤ (3 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hτ
  have h2 : (3 / 2 : ℝ)⁻¹ = 2 / 3 := by norm_num
  rw [h2] at hinv
  have hnorm : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  unfold Work.Kernels.scale
  linarith

theorem scale_bound_strip (C N : ℝ) :
    ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧
      ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
        C * (Work.Kernels.scale τ) ^ N ≤ K * (1 + ‖(τ : ℂ)‖) ^ A := by
  rcases le_or_gt 0 N with hN | hN
  · -- `N ≥ 0`: take `A = N` and `K = max C 0 * (5/3)^N`.
    refine ⟨max C 0 * (5 / 3) ^ N, N, ?_, hN, fun τ hτ => ?_⟩
    · exact mul_nonneg (le_max_right C 0) (Real.rpow_pos_of_pos (by norm_num) N).le
    · have hs := scale_le_strip τ hτ
      have hspos := Work.Kernels.scale_pos τ
      have hxnn : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by positivity
      have h1 : (Work.Kernels.scale τ) ^ N ≤ ((5 / 3) * (1 + ‖(τ : ℂ)‖)) ^ N :=
        Real.rpow_le_rpow hspos.le hs hN
      have h2 : ((5 / 3) * (1 + ‖(τ : ℂ)‖)) ^ N
          = (5 / 3) ^ N * (1 + ‖(τ : ℂ)‖) ^ N := Real.mul_rpow (by norm_num) hxnn
      rw [h2] at h1
      rcases le_or_gt 0 C with hC | hC
      · calc C * (Work.Kernels.scale τ) ^ N
            ≤ max C 0 * (Work.Kernels.scale τ) ^ N :=
              mul_le_mul_of_nonneg_right (le_max_left C 0)
                (Real.rpow_nonneg hspos.le N)
          _ ≤ max C 0 * ((5 / 3) ^ N * (1 + ‖(τ : ℂ)‖) ^ N) :=
              mul_le_mul_of_nonneg_left h1 (le_max_right C 0)
          _ = max C 0 * (5 / 3) ^ N * (1 + ‖(τ : ℂ)‖) ^ N := by ring
      · have h3 : C * (Work.Kernels.scale τ) ^ N ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hspos.le N)
        have h4 : (0 : ℝ) ≤ max C 0 * (5 / 3) ^ N * (1 + ‖(τ : ℂ)‖) ^ N := by
          have hp : (0 : ℝ) < (5 / 3) ^ N := Real.rpow_pos_of_pos (by norm_num) N
          have hx : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ N := Real.rpow_nonneg hxnn N
          have hm : (0 : ℝ) ≤ max C 0 := le_max_right C 0
          positivity
        linarith
  · -- `N < 0`: then `S τ ^ N ≤ 1`, so take `A = 0` and `K = max C 0`.
    refine ⟨max C 0, 0, le_max_right C 0, le_rfl, fun τ _hτ => ?_⟩
    have hspos := Work.Kernels.scale_pos τ
    have hle : (Work.Kernels.scale τ) ^ N ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Work.Kernels.one_le_scale τ) (le_of_lt hN)
    simp only [Real.rpow_zero, mul_one]
    rcases le_or_gt 0 C with hC | hC
    · calc C * (Work.Kernels.scale τ) ^ N ≤ C * 1 := mul_le_mul_of_nonneg_left hle hC
        _ = C := by ring
        _ ≤ max C 0 := le_max_left C 0
    · have h3 : C * (Work.Kernels.scale τ) ^ N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hspos.le N)
      have h4 : (0 : ℝ) ≤ max C 0 := le_max_right C 0
      linarith

end Work.CKFinal
