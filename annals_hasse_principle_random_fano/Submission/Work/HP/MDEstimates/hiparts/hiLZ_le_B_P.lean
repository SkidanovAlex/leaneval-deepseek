import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs

namespace Work.HP.MDEstimates.hiparts

/-- Elementary exponent identity: `Δ^2 · Δ^{3/2} · Δ = Δ^{9/2}` (for `Δ > 0`). -/
private lemma rpow_2_mul_three_halves (Δ : ℝ) (hΔ : 0 < Δ) :
    Δ ^ 2 * Δ ^ ((3:ℝ)/2) * Δ = Δ ^ ((9:ℝ)/2) := by
  have e : Δ ^ ((9:ℝ)/2) = Δ ^ (2:ℝ) * Δ ^ ((3:ℝ)/2) * Δ ^ (1:ℝ) := by
    rw [show (9:ℝ)/2 = (2:ℝ) + (3:ℝ)/2 + 1 by norm_num]
    rw [Real.rpow_add hΔ, Real.rpow_add hΔ]
  rw [e]
  rw [show Δ ^ (2:ℝ) = Δ^2 by norm_num, show (Δ:ℝ) ^ (1:ℝ) = Δ by norm_num]

/-- The "case `P`" bound: when the minimum `min (2Δ) ((2M)^53)` is realised by the first argument
(`2Δ ≤ (2M)^53`) but in fact the estimate holds unconditionally, since `min ≤ 2Δ` always.
With `B ≤ Δ` one has `B^{3/2} + (2Δ)^{3/2} ≤ 2 (2Δ)^{3/2}`, so that
`hiLZ B (2Δ) (2M) ≤ 2^{11/2} B^{9/2} Δ^{9/2} (log 4Δ)^2 ≤ 64 B^{9/2} Δ^{9/2} (log 4Δ)^2`. -/
theorem hiLZ_le_B_P (B Δ M : ℝ) (hB : 0 < B) (hΔ : 0 < Δ) (hBΔ : B ≤ Δ)
    (hP : 2 * Δ ≤ (2 * M) ^ 53) :
    hiLZ B (2 * Δ) (2 * M) ≤ 64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) * (Real.log (4 * Δ)) ^ 2 := by
  have hB0 : 0 ≤ B := hB.le
  have hΔ0 : 0 ≤ Δ := hΔ.le
  have h2Δ0 : 0 ≤ 2 * Δ := by linarith
  have hB32 : B ^ ((3:ℝ)/2) ≤ (2 * Δ) ^ ((3:ℝ)/2) :=
    Real.rpow_le_rpow hB0 (by linarith) (by norm_num)
  have hS : B ^ ((3:ℝ)/2) + (2 * Δ) ^ ((3:ℝ)/2) ≤ 2 * (2 * Δ) ^ ((3:ℝ)/2) := by
    have := Real.rpow_nonneg h2Δ0 ((3:ℝ)/2)
    linarith
  have hD32 : (2 * Δ) ^ ((3:ℝ)/2) ≤ 4 * Δ ^ ((3:ℝ)/2) := by
    rw [Real.mul_rpow (by norm_num) hΔ0]
    have hle : (2:ℝ) ^ ((3:ℝ)/2) ≤ 4 := by
      have h2 : (2:ℝ) ^ ((3:ℝ)/2) ≤ (2:ℝ) ^ (2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h4 : (2:ℝ) ^ (2:ℝ) = 4 := by norm_num
      linarith
    nlinarith [Real.rpow_nonneg hΔ0 ((3:ℝ)/2)]
  have hmin : min (2 * Δ) ((2 * M) ^ 53) ≤ 2 * Δ := min_le_left _ _
  have hident : Δ ^ 2 * Δ ^ ((3:ℝ)/2) * Δ = Δ ^ ((9:ℝ)/2) :=
    rpow_2_mul_three_halves Δ hΔ
  have hstep : (2 * Δ) ^ 2 * (2 * (2 * Δ) ^ ((3:ℝ)/2)) * (2 * Δ) ≤ 64 * Δ ^ ((9:ℝ)/2) := by
    have h1 : (2 * Δ) ^ 2 = 4 * Δ^2 := by ring
    have hfin : 4 * Δ^2 * (2 * (4 * Δ ^ ((3:ℝ)/2))) * (2 * Δ) = 64 * Δ ^ ((9:ℝ)/2) := by
      rw [← hident]; ring
    calc (2 * Δ) ^ 2 * (2 * (2 * Δ) ^ ((3:ℝ)/2)) * (2 * Δ)
        = 4 * Δ^2 * (2 * (2 * Δ) ^ ((3:ℝ)/2)) * (2 * Δ) := by rw [h1]
      _ ≤ 4 * Δ^2 * (2 * (4 * Δ ^ ((3:ℝ)/2))) * (2 * Δ) := by gcongr
      _ = 64 * Δ ^ ((9:ℝ)/2) := hfin
  unfold hiLZ
  rw [show 2 * (2 * Δ) = 4 * Δ by ring]
  calc B ^ ((9:ℝ)/2) * (2 * Δ) ^ 2 * (B ^ ((3:ℝ)/2) + (2 * Δ) ^ ((3:ℝ)/2))
          * (Real.log (4 * Δ)) ^ 2 * min (2 * Δ) ((2 * M) ^ 53)
      ≤ B ^ ((9:ℝ)/2) * (2 * Δ) ^ 2 * (B ^ ((3:ℝ)/2) + (2 * Δ) ^ ((3:ℝ)/2))
          * (Real.log (4 * Δ)) ^ 2 * (2 * Δ) := by
        apply mul_le_mul_of_nonneg_left hmin
        positivity
    _ ≤ B ^ ((9:ℝ)/2) * (2 * Δ) ^ 2 * (2 * (2 * Δ) ^ ((3:ℝ)/2))
          * (Real.log (4 * Δ)) ^ 2 * (2 * Δ) := by gcongr
    _ = B ^ ((9:ℝ)/2) * ((2 * Δ) ^ 2 * (2 * (2 * Δ) ^ ((3:ℝ)/2)) * (2 * Δ))
          * (Real.log (4 * Δ)) ^ 2 := by ring
    _ ≤ B ^ ((9:ℝ)/2) * (64 * Δ ^ ((9:ℝ)/2)) * (Real.log (4 * Δ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hB0 _)) (sq_nonneg _)
    _ = 64 * B ^ ((9:ℝ)/2) * Δ ^ ((9:ℝ)/2) * (Real.log (4 * Δ)) ^ 2 := by ring

end Work.HP.MDEstimates.hiparts
