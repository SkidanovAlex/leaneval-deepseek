import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilVP.rpow_le_two_pow
import Submission.Work.WilVP.sameSide_of_free_window

namespace Work.WilVP

/-- ULPM data at a breakpoint-free window give a good ball of radius `s/2` at `s`. -/
theorem window_iso {D : Set ℝ} {g : ℝ → ℝ} {N Qb : ℕ} {Qs : Finset ℚ} {B : Set ℝ}
    (hN : 0 < N) (hQb : ∀ q ∈ Qs, |(q : ℝ)| ≤ Qb)
    (hU : ∀ x₁ x₂ : ℝ, 0 < x₁ → 0 < x₂ → Work.WilC4.Route.SameSide N B x₁ x₂ →
      (x₁ ∈ D ↔ x₂ ∈ D) ∧ (x₁ ∈ D → x₂ ∈ D → ∃ q ∈ Qs,
        |g x₂| * x₁ ^ (q : ℝ) ≤ N * (|g x₁| * x₂ ^ (q : ℝ)) ∧
        |g x₁| * x₂ ^ (q : ℝ) ≤ N * (|g x₂| * x₁ ^ (q : ℝ))))
    {s : ℝ} (hs : 0 < s) (hfree : ∀ b ∈ B, ¬ (s / (2 * N) ≤ b ∧ b ≤ 2 * N * s)) (hsD : s ∈ D) :
    ∀ u : ℝ, |u - s| < s / 2 → u ∈ D ∧
      |g u| ≤ N * 2 ^ Qb * |g s| ∧ |g s| ≤ N * 2 ^ Qb * |g u| := by
  intro u hu
  have habs : |u - s| < s / 2 := hu
  rw [abs_lt] at hu
  -- The ball of radius `s/2` is `(s/2, 3s/2)`, so `u > 0` and `u/s ∈ (1/2, 3/2)`.
  have hlow : s / 2 < u := by linarith [hu.1]
  have hhigh : u < 3 * s / 2 := by linarith [hu.2]
  have hu_pos : 0 < u := by linarith
  -- `hfree` puts `u` and `s` strictly on the same side of every breakpoint.
  have hss := sameSide_of_free_window hN hs hfree habs
  obtain ⟨hD, hQ⟩ := hU u s hu_pos hs hss
  have huD : u ∈ D := hD.mpr hsD
  obtain ⟨q, hqmem, hineq1, hineq2⟩ := hQ huD hsD
  have hq_abs : |(q : ℝ)| ≤ (Qb : ℝ) := hQb q hqmem
  -- The two powers `u^q`, `s^q` differ by at most `2^Qb`, since `u/s, s/u ∈ (1/2, 2)`.
  have huq : u ^ (q : ℝ) ≤ (2 : ℝ) ^ Qb * s ^ (q : ℝ) := by
    have hratio : (1 : ℝ) / 2 < u / s ∧ u / s < 2 := by
      constructor
      · rw [lt_div_iff₀ hs]; linarith
      · rw [div_lt_iff₀ hs]; linarith
    have hb := rpow_le_two_pow hratio.1 hratio.2 hq_abs
    rw [show u ^ (q : ℝ) = (u / s) ^ (q : ℝ) * s ^ (q : ℝ) from by
      rw [← Real.mul_rpow (by positivity) (le_of_lt hs), div_mul_cancel₀ u (ne_of_gt hs)]]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (le_of_lt hs) _)
  have hsq : s ^ (q : ℝ) ≤ (2 : ℝ) ^ Qb * u ^ (q : ℝ) := by
    have hratio : (1 : ℝ) / 2 < s / u ∧ s / u < 2 := by
      constructor
      · rw [lt_div_iff₀ hu_pos]; linarith
      · rw [div_lt_iff₀ hu_pos]; linarith
    have hb := rpow_le_two_pow hratio.1 hratio.2 hq_abs
    rw [show s ^ (q : ℝ) = (s / u) ^ (q : ℝ) * u ^ (q : ℝ) from by
      rw [← Real.mul_rpow (by positivity) (le_of_lt hu_pos), div_mul_cancel₀ s (ne_of_gt hu_pos)]]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (le_of_lt hu_pos) _)
  refine ⟨huD, ?_, ?_⟩
  · -- `|g u| ≤ N * 2^Qb * |g s|`, dividing the second ULPM inequality by `s^q > 0`.
    have hmain : |g u| * s ^ (q : ℝ) ≤ ((N : ℝ) * ((2 : ℝ) ^ Qb) * |g s|) * s ^ (q : ℝ) := by
      calc |g u| * s ^ (q : ℝ) ≤ (N : ℝ) * (|g s| * u ^ (q : ℝ)) := hineq2
        _ = (N : ℝ) * |g s| * u ^ (q : ℝ) := by ring
        _ ≤ (N : ℝ) * |g s| * ((2 : ℝ) ^ Qb * s ^ (q : ℝ)) := by
            apply mul_le_mul_of_nonneg_left huq; positivity
        _ = ((N : ℝ) * ((2 : ℝ) ^ Qb) * |g s|) * s ^ (q : ℝ) := by ring
    have hbound : |g u| ≤ (N : ℝ) * (2 : ℝ) ^ Qb * |g s| :=
      le_of_mul_le_mul_right hmain (Real.rpow_pos_of_pos hs _)
    simpa only [Nat.cast_pow, Nat.cast_mul] using hbound
  · -- `|g s| ≤ N * 2^Qb * |g u|`, dividing the first ULPM inequality by `u^q > 0`.
    have hmain : |g s| * u ^ (q : ℝ) ≤ ((N : ℝ) * ((2 : ℝ) ^ Qb) * |g u|) * u ^ (q : ℝ) := by
      calc |g s| * u ^ (q : ℝ) ≤ (N : ℝ) * (|g u| * s ^ (q : ℝ)) := hineq1
        _ = (N : ℝ) * |g u| * s ^ (q : ℝ) := by ring
        _ ≤ (N : ℝ) * |g u| * ((2 : ℝ) ^ Qb * u ^ (q : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hsq; positivity
        _ = ((N : ℝ) * ((2 : ℝ) ^ Qb) * |g u|) * u ^ (q : ℝ) := by ring
    have hbound : |g s| ≤ (N : ℝ) * (2 : ℝ) ^ Qb * |g u| :=
      le_of_mul_le_mul_right hmain (Real.rpow_pos_of_pos hu_pos _)
    simpa only [Nat.cast_pow, Nat.cast_mul] using hbound

end Work.WilVP
