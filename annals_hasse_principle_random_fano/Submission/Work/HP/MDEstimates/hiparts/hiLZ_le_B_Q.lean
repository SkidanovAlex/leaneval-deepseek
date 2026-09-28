import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs

/-!
# The case-`Q`, `Δ ≥ B` bound for `hiLZ`

`hiLZ B Δ M = B^{9/2} Δ² (B^{3/2} + Δ^{3/2}) (log 2Δ)² min{Δ, M^{53}}` is the convenient
`ℓ^{(1)}` bound at `Z = B`.  Here we evaluate it at the doubled cutoffs `Δ ↦ 2Δ`, `M ↦ 2M`
under the hypothesis that the second cutoff is on the `M`-side, `(2M)^{53} ≤ 2Δ`, and with
`Δ ≥ B` (so that `B^{3/2} ≤ Δ^{3/2}`); the resulting polynomial bound is
`32·2^{53} B^{9/2} Δ^{7/2} M^{53} (log 4Δ)²`.

The proof is elementary: the minimum is at most `2^{53} M^{53}`, `(2Δ)² = 4Δ²`, and
`B^{3/2} + (2Δ)^{3/2} ≤ Δ^{3/2} + 4Δ^{3/2} ≤ 8Δ^{3/2}` using `B ≤ Δ` and `2^{3/2} ≤ 4`.
-/

namespace Work.HP.MDEstimates.hiparts

theorem hiLZ_le_B_Q (B Δ M : ℝ) (hB : 0 < B) (hΔ : 0 < Δ) (hM : 0 ≤ M) (hBΔ : B ≤ Δ)
    (hQ : (2 * M) ^ 53 ≤ 2 * Δ) :
    hiLZ B (2 * Δ) (2 * M) ≤ 32 * 2 ^ 53 * B ^ ((9:ℝ)/2) * Δ ^ ((7:ℝ)/2) * M ^ 53
      * (Real.log (4 * Δ)) ^ 2 := by
  have hB0 : (0:ℝ) ≤ B := hB.le
  have hΔ0 : (0:ℝ) ≤ Δ := hΔ.le
  have hΔ32 : (0:ℝ) ≤ Δ ^ ((3:ℝ)/2) := Real.rpow_nonneg hΔ0 _
  -- `B^{3/2} ≤ Δ^{3/2}`
  have hB32 : B ^ ((3:ℝ)/2) ≤ Δ ^ ((3:ℝ)/2) :=
    Real.rpow_le_rpow hB0 hBΔ (by norm_num)
  -- `2^{3/2} ≤ 4`
  have h2pow : (2:ℝ) ^ ((3:ℝ)/2) ≤ 4 := by
    have h : (2:ℝ) ^ ((3:ℝ)/2) ≤ (2:ℝ) ^ ((2:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_natCast] at h
    norm_num at h
    exact h
  -- `(2Δ)^{3/2} = 2^{3/2} Δ^{3/2}`
  have hmul2 : (2 * Δ) ^ ((3:ℝ)/2) = 2 ^ ((3:ℝ)/2) * Δ ^ ((3:ℝ)/2) :=
    Real.mul_rpow (by norm_num) hΔ0
  -- the bracket is at most `8 Δ^{3/2}`
  have hS : B ^ ((3:ℝ)/2) + (2 * Δ) ^ ((3:ℝ)/2) ≤ 8 * Δ ^ ((3:ℝ)/2) := by
    have h2 : 2 ^ ((3:ℝ)/2) * Δ ^ ((3:ℝ)/2) ≤ 4 * Δ ^ ((3:ℝ)/2) :=
      mul_le_mul_of_nonneg_right h2pow hΔ32
    rw [hmul2]; linarith
  -- `Δ² · Δ^{3/2} = Δ^{7/2}`
  have hΔ7 : Δ ^ 2 * Δ ^ ((3:ℝ)/2) = Δ ^ ((7:ℝ)/2) := by
    rw [← Real.rpow_natCast (Δ), ← Real.rpow_add hΔ]
    congr 1
    norm_num
  have hlog : Real.log (2 * (2 * Δ)) = Real.log (4 * Δ) := by congr 1; ring
  have hmin : min (2 * Δ) ((2 * M) ^ 53) = 2 ^ 53 * M ^ 53 := by
    rw [min_eq_right hQ]; ring
  unfold hiLZ
  rw [hlog, hmin, show (2 * Δ) ^ 2 = 4 * Δ ^ 2 by ring]
  have hA : (0:ℝ) ≤ B ^ ((9:ℝ)/2) * (4 * Δ ^ 2) :=
    mul_nonneg (Real.rpow_nonneg hB0 _) (by positivity)
  have hC : (0:ℝ) ≤ (Real.log (4 * Δ)) ^ 2 := sq_nonneg _
  have hD : (0:ℝ) ≤ 2 ^ 53 * M ^ 53 := mul_nonneg (by norm_num) (pow_nonneg hM 53)
  have h1 : (B ^ ((9:ℝ)/2) * (4 * Δ ^ 2)) * (B ^ ((3:ℝ)/2) + (2 * Δ) ^ ((3:ℝ)/2))
      ≤ (B ^ ((9:ℝ)/2) * (4 * Δ ^ 2)) * (8 * Δ ^ ((3:ℝ)/2)) :=
    mul_le_mul_of_nonneg_left hS hA
  have h2 := mul_le_mul_of_nonneg_right h1 hC
  have h3 := mul_le_mul_of_nonneg_right h2 hD
  refine le_trans h3 (le_of_eq ?_)
  rw [show (B ^ ((9:ℝ)/2) * (4 * Δ ^ 2)) * (8 * Δ ^ ((3:ℝ)/2))
        = B ^ ((9:ℝ)/2) * (32 * (Δ ^ 2 * Δ ^ ((3:ℝ)/2))) by ring, hΔ7]
  ring

end Work.HP.MDEstimates.hiparts
