import Mathlib
import Submission.Work.Pure.b5_rel

namespace Work.B5pull

open Submission.CDTPlan

/-- The coefficient identity over `ℚ` underlying `b5_coeff_rec_c`: it is the `n`-th
coefficient of the differential identity `b5_rel`. -/
theorem b5_coeff_rec_q (n : ℕ) :
    8 * ((n : ℚ) * PowerSeries.coeff n B5)
      - 2 * (((n - 1 : ℕ) : ℚ) * PowerSeries.coeff (n - 1) B5)
    = 4 * PowerSeries.coeff n B5
      - (if n = 0 then 0 else PowerSeries.coeff (n - 1) B5)
      - 2 * PowerSeries.coeff n B2
      + (if n = 1 then 4 else 0) := by
  have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff n f) Work.Pure.b5_rel
  rw [Work.Pure.b5_coeff_lhs B5 n, Work.Pure.b5_coeff_rhs n] at h
  by_cases h0 : n = 0
  · subst h0
    simp [Work.Pure.b5_coeff_B5_zero, Work.Pure.b5_coeff_B2_zero]
  rw [if_neg h0]
  by_cases h1 : n = 1
  · subst h1
    norm_num [Work.Pure.b5_coeff_B5_one, Work.Pure.b5_coeff_B5_zero,
      Work.Pure.b5_coeff_B2_one]
  rw [if_neg h1] at h ⊢
  linear_combination h

theorem b5_coeff_rec_c (n : ℕ) :
    8 * ((n : ℂ) * ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ))
      - 2 * (((n - 1 : ℕ) : ℂ) * ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B5 : ℚ) : ℂ))
    = 4 * ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ)
      - (if n = 0 then 0 else ((PowerSeries.coeff (n - 1) Submission.CDTPlan.B5 : ℚ) : ℂ))
      - 2 * ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)
      + (if n = 1 then 4 else 0) := by
  have h := congrArg (fun x : ℚ => (x : ℂ)) (b5_coeff_rec_q n)
  push_cast at h
  by_cases h0 : n = 0
  · subst h0
    simpa using h
  rw [if_neg h0] at h ⊢
  by_cases h1 : n = 1
  · subst h1
    simpa using h
  rw [if_neg h1] at h ⊢
  simpa using h

end Work.B5pull
