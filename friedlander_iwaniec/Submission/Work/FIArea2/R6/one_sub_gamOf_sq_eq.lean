import Mathlib
import Submission.Work.FIArea2.Sec6Defs
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea4.GaussMoebiusCore

/-!
# `1 - γ² = |Δ|² / |z₁z₂|²`  (the `sin²` of §7)

With `γ = Re(z̄₁z₂)/|z₁z₂|` (the cosine of `gamOf`) and `Δ = Im(z̄₁z₂)`, the identity
`Re(z̄₁z₂)² + Im(z̄₁z₂)² = |z₁|²|z₂|²` (multiplicativity of the `ℤ[i]`-norm) is exactly
`1 - γ² = |Δ|²/|z₁z₂|²`.
-/

namespace Work.FIArea2.R6

open Work.FIPlan

/-- The elementary algebra: for reals `x,y,D,S,N` with `D = x²+y² = N > 0` and `S² = D`,
`1 - (x/S)² = y²/N`. -/
private lemma key_alg (x y D S N : ℝ) (hD : 0 < D) (hS : S ^ 2 = D)
    (hkey : x ^ 2 + y ^ 2 = D) (hN : N = D) :
    1 - (x / S) ^ 2 = y ^ 2 / N := by
  have hSD : (x / S) ^ 2 = x ^ 2 / D := by rw [div_pow, hS]
  rw [hSD, hN]
  have hDne : D ≠ 0 := ne_of_gt hD
  field_simp
  linarith

theorem one_sub_gamOf_sq_eq (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    1 - (Work.FIArea2.gamOf z1 z2) ^ 2
      = (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2
        / ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
  have hz1 : z1 ≠ 0 := by
    rintro rfl
    exact hΔ (by simp [absDelta, Delta])
  have hz2 : z2 ≠ 0 := by
    rintro rfl
    exact hΔ (by simp [absDelta, Delta])
  have hN1pos : 0 < ((gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea4.gnorm_pos hz1
  have hN2pos : 0 < ((gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea4.gnorm_pos hz2
  have hDpos : 0 < ((gnorm z1 : ℕ) : ℝ) * ((gnorm z2 : ℕ) : ℝ) := mul_pos hN1pos hN2pos
  have hND : ((gnorm (z1 * z2) : ℕ) : ℝ)
      = ((gnorm z1 : ℕ) : ℝ) * ((gnorm z2 : ℕ) : ℝ) := by
    rw [Work.FIArea4.gnorm_mul]; push_cast; ring
  have hkeyZ : ((star z1 * z2).re : ℤ) ^ 2 + ((star z1 * z2).im : ℤ) ^ 2
      = (gnorm (z1 * z2) : ℤ) := by
    have h1 : ((star z1 * z2).re : ℤ) ^ 2 + ((star z1 * z2).im : ℤ) ^ 2
        = (star z1 * z2).norm := by
      rw [Zsqrtd.norm_def]; ring
    have h2 : (star z1 * z2).norm = (z1 * z2).norm := by
      rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, ← Zsqrtd.norm_mul]
    rw [h1, h2]
    simp [gnorm]
  have hkeyR : (((star z1 * z2).re : ℤ) : ℝ) ^ 2 + (((star z1 * z2).im : ℤ) : ℝ) ^ 2
      = ((gnorm (z1 * z2) : ℕ) : ℝ) := by
    have h := congrArg (fun t : ℤ => (t : ℝ)) hkeyZ
    push_cast at h
    simpa using h
  have hAbs2 : ((absDelta z1 z2 : ℕ) : ℝ) ^ 2 = (((star z1 * z2).im : ℤ) : ℝ) ^ 2 := by
    have h : ((absDelta z1 z2 : ℕ) : ℤ) ^ 2 = (((star z1 * z2).im : ℤ)) ^ 2 := by
      rw [absDelta, Delta]
      simpa [sq] using Int.natAbs_mul_self (star z1 * z2).im
    have h2 := congrArg (fun t : ℤ => (t : ℝ)) h
    push_cast at h2
    simpa using h2
  have hkeyD : (((star z1 * z2).re : ℤ) : ℝ) ^ 2 + (((star z1 * z2).im : ℤ) : ℝ) ^ 2
      = ((gnorm z1 : ℕ) : ℝ) * ((gnorm z2 : ℕ) : ℝ) := by
    rw [hkeyR, hND]
  unfold Work.FIArea2.gamOf
  rw [hAbs2]
  exact key_alg (((star z1 * z2).re : ℤ) : ℝ) (((star z1 * z2).im : ℤ) : ℝ)
    (((gnorm z1 : ℕ) : ℝ) * ((gnorm z2 : ℕ) : ℝ))
    (Real.sqrt (((gnorm z1 : ℕ) : ℝ) * ((gnorm z2 : ℕ) : ℝ)))
    ((gnorm (z1 * z2) : ℕ) : ℝ)
    hDpos (Real.sq_sqrt (le_of_lt hDpos)) hkeyD hND

end Work.FIArea2.R6
