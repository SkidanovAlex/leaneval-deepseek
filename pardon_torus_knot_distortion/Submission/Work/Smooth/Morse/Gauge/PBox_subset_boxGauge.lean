import Mathlib
import Submission.Work.Smooth.Morse.Gauge

namespace Work.Smooth.Morse.Gauge

theorem PBox_subset_boxGauge (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t) : Submission.PBox t c σ ⊆ {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.Morse.boxGauge c σ k y < (3 : ℝ) ^ (1 / (2 * (k : ℝ))) * t} := by
  intro y hy
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have hy0 := hy 0
    rw [Submission.boxSide_zero, mul_zero] at hy0
    exact absurd hy0 (not_lt.mpr (abs_nonneg _))
  have hk2 : 2 * k ≠ 0 := by omega
  have hk2pos : (0 : ℝ) < 2 * (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hterm : ∀ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| < t := by
    intro i
    rw [abs_div, abs_of_pos (Submission.boxSide_pos i), div_lt_iff₀ (Submission.boxSide_pos i)]
    calc |y (σ i) - c (σ i)| < Submission.boxSide i * t := hy i
      _ = t * Submission.boxSide i := mul_comm _ _
  have hpow : ∀ i : Fin 3,
      |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k) < t ^ (2 * k) := by
    intro i
    exact pow_lt_pow_left₀ (hterm i) (abs_nonneg _) hk2
  have hsum_lt : (∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k))
      < 3 * t ^ (2 * k) := by
    rw [Fin.sum_univ_three]
    have h0 := hpow 0; have h1 := hpow 1; have h2 := hpow 2
    linarith [sq_nonneg (t ^ (2 * k))]
  have hS_nonneg : 0 ≤ ∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k) :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)
  unfold Work.Smooth.Morse.boxGauge
  have hexp_pos : 0 < 1 / (2 * (k : ℝ)) := div_pos zero_lt_one hk2pos
  have hmain := Real.rpow_lt_rpow hS_nonneg hsum_lt hexp_pos
  refine lt_of_lt_of_eq hmain ?_
  rw [Real.mul_rpow (by norm_num) (pow_nonneg ht _)]
  congr 1
  have hcast : (((2 * k : ℕ) : ℝ)) = 2 * (k : ℝ) := by push_cast; ring
  rw [← Real.rpow_natCast t (2 * k), ← Real.rpow_mul ht ((2 * k : ℕ) : ℝ) (1 / (2 * (k : ℝ))),
    hcast]
  have hone : 2 * (k : ℝ) * (1 / (2 * (k : ℝ))) = 1 := by field_simp
  rw [hone, Real.rpow_one]

end Work.Smooth.Morse.Gauge
