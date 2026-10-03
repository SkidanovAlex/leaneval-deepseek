import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea4.absDelta_le_sector
import Submission.Work.FIArea4.S15box

namespace Work.FIArea2

open scoped BigOperators

/-- **(6.2)**: for `z₁, z₂` in the same polar box (5.14) the determinant `Δ = Im(z̄₁z₂)` satisfies
`|Δ| < 4πθN`.  (The paper states `1 ≤ |Δ| < 4πθN`; `1 ≤ |Δ|` is separate, from `Δ ≠ 0`.)

Proof: `Δ = |z₁||z₂| sin(α₂-α₁)` with both principal arguments in an interval of length `2πθ`,
so `|Δ| ≤ |z₁||z₂| |α₂-α₁| < |z₁||z₂| 2πθ ≤ 4πθN`, using `|z_i|² ≤ (1+θ)N ≤ 2N` (`θ ≤ 1`). -/
theorem absDelta_lt_four_pi {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    (Work.FIPlan.absDelta z1 z2 : ℝ) < 4 * Real.pi * Pa.θ * Pa.N := by
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hN1 : 1 ≤ Pa.N := Pa.hN1
  have hN0 : 0 < Pa.N := by linarith
  -- norm bounds `|z_i|² ≤ (1+θ)N ≤ 2N`
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    have hle : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h1.2.2.1
    nlinarith
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    have hle : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h2.2.2.1
    nlinarith
  have hs1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * Pa.N) :=
    Real.sqrt_le_sqrt hg1
  have hs2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt (2 * Pa.N) :=
    Real.sqrt_le_sqrt hg2
  have hsq : Real.sqrt (2 * Pa.N) * Real.sqrt (2 * Pa.N) = 2 * Pa.N :=
    Real.mul_self_sqrt (by positivity)
  -- the difference of the arguments is `< 2πθ` in absolute value
  have hxlt : |(z2 : ℂ).arg - (z1 : ℂ).arg| < 2 * Real.pi * Pa.θ := by
    have hlt1 : φ < (z1 : ℂ).arg := h1.2.2.2.1
    have hle1 : (z1 : ℂ).arg ≤ φ + 2 * Real.pi * Pa.θ := h1.2.2.2.2
    have hlt2 : φ < (z2 : ℂ).arg := h2.2.2.2.1
    have hle2 : (z2 : ℂ).arg ≤ φ + 2 * Real.pi * Pa.θ := h2.2.2.2.2
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  -- `Δ = |z₁||z₂|sin(α₂-α₁)`
  have hkey : (Work.FIPlan.Delta z1 z2 : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg) := by
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
        GaussianInt.toComplex_star]
    exact Work.FIArea4.im_starRingEnd_mul (z1 : ℂ) (z2 : ℂ)
  have habs : (Work.FIPlan.absDelta z1 z2 : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs, hkey]
    simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
  calc (Work.FIPlan.absDelta z1 z2 : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * |Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg)| := habs
    _ ≤ ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * |(z2 : ℂ).arg - (z1 : ℂ).arg| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := (z2 : ℂ).arg - (z1 : ℂ).arg))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ Real.sqrt (2 * Pa.N) * Real.sqrt (2 * Pa.N) * |(z2 : ℂ).arg - (z1 : ℂ).arg| := by
        rw [← Work.FIArea4.sqrt_gnorm z1, ← Work.FIArea4.sqrt_gnorm z2]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (abs_nonneg _)
    _ = 2 * Pa.N * |(z2 : ℂ).arg - (z1 : ℂ).arg| := by rw [hsq]
    _ < 2 * Pa.N * (2 * Real.pi * Pa.θ) := by
        exact mul_lt_mul_of_pos_left hxlt (by linarith)
    _ = 4 * Real.pi * Pa.θ * Pa.N := by ring

end Work.FIArea2
