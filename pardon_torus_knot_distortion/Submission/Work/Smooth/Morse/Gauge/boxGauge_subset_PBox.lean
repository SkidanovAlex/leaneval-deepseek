import Mathlib
import Submission.Work.Smooth.Morse.Gauge

namespace Work.Smooth.Morse.Gauge

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The sublevel sets of the `ℓ^{2k}`-gauge lie in Pardon's box.**  Since `k ≥ 1`, every
summand of the defining sum is non-negative, so each single coordinate term is bounded by the
whole gauge; taking `(2k)`-th roots gives `|y (σ i) - c (σ i)| / boxSide i < t` for every `i`,
which is exactly membership in `Submission.PBox t c σ`. -/
theorem boxGauge_subset_PBox (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) : {y : LeanEval.KnotTheory.PardonDistortion.R3 | Work.Smooth.Morse.boxGauge c σ k y < t} ⊆ Submission.PBox t c σ := by
  intro y hy
  rw [Submission.mem_PBox]
  intro j
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hepos : 0 < 1 / (2 * (k : ℝ)) := by positivity
  have hhy : (∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k)) ^
      (1 / (2 * (k : ℝ))) < t := by
    simpa [Work.Smooth.Morse.boxGauge] using hy
  have hterm : |(y (σ j) - c (σ j)) / Submission.boxSide j| ^ (2 * k) ≤
      ∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k) :=
    Finset.single_le_sum (f := fun i => |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k))
      (fun i _ => by positivity) (Finset.mem_univ j)
  have hroot : (|(y (σ j) - c (σ j)) / Submission.boxSide j| ^ (2 * k)) ^ (1 / (2 * (k : ℝ)))
      = |(y (σ j) - c (σ j)) / Submission.boxSide j| := by
    rw [← Real.rpow_natCast (|(y (σ j) - c (σ j)) / Submission.boxSide j|) (2 * k)]
    rw [← Real.rpow_mul (abs_nonneg _) (((2 * k : ℕ) : ℝ)) (1 / (2 * (k : ℝ)))]
    have h1 : (((2 * k : ℕ) : ℝ)) * (1 / (2 * (k : ℝ))) = 1 := by
      push_cast
      rw [mul_one_div, div_self (by positivity : (2 * (k : ℝ)) ≠ 0)]
    rw [h1, Real.rpow_one]
  have hle : |(y (σ j) - c (σ j)) / Submission.boxSide j| ≤
      (∑ i : Fin 3, |(y (σ i) - c (σ i)) / Submission.boxSide i| ^ (2 * k)) ^
        (1 / (2 * (k : ℝ))) := by
    rw [← hroot]
    exact Real.rpow_le_rpow (by positivity) hterm (le_of_lt hepos)
  have hlt : |(y (σ j) - c (σ j)) / Submission.boxSide j| < t := lt_of_le_of_lt hle hhy
  have hbs := Submission.boxSide_pos j
  rw [abs_div, abs_of_pos hbs] at hlt
  have hmul := mul_lt_mul_of_pos_right hlt hbs
  rw [div_mul_cancel₀ _ (ne_of_gt hbs)] at hmul
  simpa [mul_comm] using hmul

end Work.Smooth.Morse.Gauge
