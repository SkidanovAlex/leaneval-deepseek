import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs

/-!
# The `𝔡₃ ≤ B` (`A`, "P") bound for `hiLZ B (2Δ) (2M)`

Recall (`HiDefs`)
`hiLZ B Δ M = B^{9/2} Δ² (B^{3/2} + Δ^{3/2}) (log 2Δ)² min{Δ, M⁵³}`.

In the regime `Δ ≤ B` (so that `𝔡₃ ≤ A^{1/20} ≤ B`) no `λ₁`-information is used:
the `min{·,·}` factor is simply dropped, and the two `Δ`-powers `(2Δ)²`, `(2Δ)` combine to
`8 Δ³` while the `B`-powers `B^{9/2}·B^{3/2}` combine to `B⁶`.  Using only `Δ ≤ B` to
bound `(2Δ)^{3/2} = 2^{3/2} Δ^{3/2} ≤ 4 B^{3/2}`, one gets

`hiLZ B (2Δ) (2M) ≤ 40 B⁶ Δ³ (log 4Δ)² ≤ 64 B⁶ Δ³ (log 4Δ)²`.

The hypothesis `hP : 2Δ ≤ (2M)⁵³` holds in the `P` regime but is in fact not needed.
-/

set_option autoImplicit false

namespace Work.HP.MDEstimates.hiparts

theorem hiLZ_le_A_P (B Δ M : ℝ) (hB : 0 < B) (hΔ : 0 < Δ) (hΔB : Δ ≤ B)
    (hP : 2 * Δ ≤ (2 * M) ^ 53) :
    hiLZ B (2 * Δ) (2 * M) ≤ 64 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 := by
  have hB0 : (0 : ℝ) ≤ B := hB.le
  have hΔ0 : (0 : ℝ) ≤ Δ := hΔ.le
  have hlog0 : (0 : ℝ) ≤ (Real.log (4 * Δ)) ^ 2 := sq_nonneg _
  -- Monotonicity of the `3/2`-power of the base.
  have hBD : Δ ^ ((3 : ℝ) / 2) ≤ B ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hΔ0 hΔB (by norm_num)
  -- `2^{3/2} ≤ 2^2 = 4`.
  have h2pow : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
    have h : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_natCast]
    linarith
  -- `(2Δ)^{3/2} = 2^{3/2} Δ^{3/2} ≤ 4 B^{3/2}`.
  have h2Δ3 : (2 * Δ) ^ ((3 : ℝ) / 2) ≤ 4 * B ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hΔ0]
    calc (2 : ℝ) ^ ((3 : ℝ) / 2) * Δ ^ ((3 : ℝ) / 2)
        ≤ 4 * Δ ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hΔ0 _)
      _ ≤ 4 * B ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hBD (by norm_num)
  have hsum : B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2) ≤ 5 * B ^ ((3 : ℝ) / 2) := by
    linarith
  -- `B^{9/2} · B^{3/2} = B^6`.
  have hxy : B ^ ((9 : ℝ) / 2) * B ^ ((3 : ℝ) / 2) = B ^ 6 := by
    rw [← Real.rpow_add hB]
    norm_num
  -- Drop the `min` factor: `min (2Δ) ((2M)^53) ≤ 2Δ`.
  have hstep1 : hiLZ B (2 * Δ) (2 * M) ≤
      B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2 * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2))
        * (Real.log (4 * Δ)) ^ 2 * (2 * Δ) := by
    unfold hiLZ
    rw [show (2 : ℝ) * (2 * Δ) = 4 * Δ by ring]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  -- Bound the parenthesised sum and collect the powers.
  have hstep2 : B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2
        * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2))
        * (Real.log (4 * Δ)) ^ 2 * (2 * Δ)
      ≤ 64 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 := by
    have h1 : B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2
          * (B ^ ((3 : ℝ) / 2) + (2 * Δ) ^ ((3 : ℝ) / 2))
          * (Real.log (4 * Δ)) ^ 2 * (2 * Δ)
        ≤ B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2 * (5 * B ^ ((3 : ℝ) / 2))
          * (Real.log (4 * Δ)) ^ 2 * (2 * Δ) := by
      gcongr
    have h2 : B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2 * (5 * B ^ ((3 : ℝ) / 2))
          * (Real.log (4 * Δ)) ^ 2 * (2 * Δ)
        = 40 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 := by
      have h3 : (2 * Δ) ^ 2 * (2 * Δ) = 8 * Δ ^ 3 := by ring
      calc B ^ ((9 : ℝ) / 2) * (2 * Δ) ^ 2 * (5 * B ^ ((3 : ℝ) / 2))
              * (Real.log (4 * Δ)) ^ 2 * (2 * Δ)
          = 5 * (B ^ ((9 : ℝ) / 2) * B ^ ((3 : ℝ) / 2)) * ((2 * Δ) ^ 2 * (2 * Δ))
              * (Real.log (4 * Δ)) ^ 2 := by ring
        _ = 5 * B ^ 6 * (8 * Δ ^ 3) * (Real.log (4 * Δ)) ^ 2 := by rw [hxy, h3]
        _ = 40 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 := by ring
    have h4 : 40 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2
        ≤ 64 * B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 := by
      have hnn : 0 ≤ B ^ 6 * Δ ^ 3 * (Real.log (4 * Δ)) ^ 2 :=
        mul_nonneg (mul_nonneg (pow_nonneg hB0 6) (pow_nonneg hΔ0 3)) hlog0
      linarith
    linarith [h1, h2.le, h4]
  linarith [hstep1, hstep2]

end Work.HP.MDEstimates.hiparts
