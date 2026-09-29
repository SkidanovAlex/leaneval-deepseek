import Mathlib
import Submission.Work.Pure.b4_rel

/-!
# The coefficient recurrence of `B₄` (CDT, `(diffformulas)`)

The differential relation `y(4−y)B₄' = (2−y)B₄ + (4−y)B₂ − 2y(4−y)`
(`Work.Pure.b4_rel`) is converted into a recurrence for the coefficients, in exactly
the form needed by the Theorem-C template.
-/

namespace Work.CPull

open Submission.CDTPlan PowerSeries

/-- Coefficient of `(C c − X) * h` at `n`. -/
lemma b4rec_coeff_C_sub_X_mul (c : ℚ) (n : ℕ) (h : PowerSeries ℚ) :
    PowerSeries.coeff n ((PowerSeries.C c - X) * h)
      = c * PowerSeries.coeff n h - (if n = 0 then 0 else PowerSeries.coeff (n - 1) h) := by
  rw [show (PowerSeries.C c - X) * h = PowerSeries.C c * h - X * h by ring]
  rw [map_sub, PowerSeries.coeff_C_mul, Work.Pure.rcoeff_X_mul]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_pos (by omega : 1 ≤ n), if_neg hn]

lemma b4rec_coeff_two_sub_X_mul (n : ℕ) (h : PowerSeries ℚ) :
    PowerSeries.coeff n (((2 : PowerSeries ℚ) - X) * h)
      = 2 * PowerSeries.coeff n h - (if n = 0 then 0 else PowerSeries.coeff (n - 1) h) :=
  b4rec_coeff_C_sub_X_mul 2 n h

lemma b4rec_coeff_four_sub_X_mul (n : ℕ) (h : PowerSeries ℚ) :
    PowerSeries.coeff n (((4 : PowerSeries ℚ) - X) * h)
      = 4 * PowerSeries.coeff n h - (if n = 0 then 0 else PowerSeries.coeff (n - 1) h) :=
  b4rec_coeff_C_sub_X_mul 4 n h

/-- Coefficient of the inhomogeneous term `2X(4−X)`. -/
lemma b4rec_coeff_two_X_four_sub_X (n : ℕ) :
    PowerSeries.coeff n (2 * X * ((4 : PowerSeries ℚ) - X))
      = (if n = 1 then 8 else 0) - (if n = 2 then 2 else 0) := by
  have h : 2 * X * ((4 : PowerSeries ℚ) - X)
      = ((8 : PowerSeries ℚ) * X) - (2 : PowerSeries ℚ) * X ^ 2 := by ring
  rw [h, map_sub, show (8 : PowerSeries ℚ) = PowerSeries.C 8 from rfl, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs <;> ring

theorem B4_coeff_rec (n : ℕ) :
    4 * ((n : ℚ) * PowerSeries.coeff n Submission.CDTPlan.B4)
      - (((n - 1 : ℕ) : ℚ) * PowerSeries.coeff (n - 1) Submission.CDTPlan.B4)
    = 2 * PowerSeries.coeff n Submission.CDTPlan.B4
      - (if n = 0 then 0 else PowerSeries.coeff (n - 1) Submission.CDTPlan.B4)
      + (4 * PowerSeries.coeff n Submission.CDTPlan.B2
         - (if n = 0 then 0 else PowerSeries.coeff (n - 1) Submission.CDTPlan.B2))
      - (if n = 1 then 8 else 0) + (if n = 2 then 2 else 0) := by
  have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff n f) Work.Pure.b4_rel
  rw [Work.Pure.rcoeff_ode_lhs n Submission.CDTPlan.B4] at h
  rw [map_sub, map_add] at h
  rw [b4rec_coeff_two_sub_X_mul n Submission.CDTPlan.B4,
    b4rec_coeff_four_sub_X_mul n Submission.CDTPlan.B2, b4rec_coeff_two_X_four_sub_X n] at h
  rw [h]
  ring

end Work.CPull
