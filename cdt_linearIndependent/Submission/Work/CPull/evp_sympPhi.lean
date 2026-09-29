import Mathlib
import Submission.Work.CPull.defs

/-!
# Evaluation of the symmetrization involution series `φ` and the coordinate `y`

`Submission.CDT.sympPhi = X/(X−1)` is the power series of the involution
`x ↦ x/(x−1)` (`coeff 0 = 0`, `coeff n = −1` for `n ≥ 1`) and
`Submission.CDT.sympY = X·φ = x²/(x−1)` (`coeff 0 = coeff 1 = 0`,
`coeff n = −1` for `n ≥ 2`).

The two coefficient facts below (`Work.CPull.coeff_sympPhi_eq`,
`Work.CPull.coeff_sympY_eq`) are the bridge between the formal series of
`Submission.CDT.SympDescent` and the analytic functions `z ↦ z/(z−1)`,
`z ↦ z²/(z−1)` on the open unit disc.

The evaluation identity `evp φ z = z/(z−1)` is then the standard summation of a
geometric series: the coefficients are `−1` with the appropriate shift, so the
sum equals `−(1−z)⁻¹` plus a finitely-supported correction, which is computed
from single-variable indicator sums.
-/

namespace Work.CPull

open PowerSeries

/-- coefficients of `φ = X/(X−1)`: `0` at `0`, `−1` elsewhere. -/
lemma coeff_sympPhi_eq (n : ℕ) :
    PowerSeries.coeff n Submission.CDT.sympPhi = if n = 0 then 0 else -1 := by
  rcases n with _ | k
  · rw [if_pos rfl]; exact Submission.CDT.coeff_sympPhi_zero
  · rw [if_neg (Nat.succ_ne_zero k)]
    show PowerSeries.coeff (k + 1) (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹) = -1
    rw [PowerSeries.coeff_succ_X_mul]
    exact Submission.CDT.coeff_inv_X_sub_one k

/-- coefficients of `y = X·φ = x²/(x−1)`: `0` at `0` and `1`, `−1` from `2` on. -/
lemma coeff_sympY_eq (n : ℕ) :
    PowerSeries.coeff n Submission.CDT.sympY
      = if n = 0 then 0 else if n = 1 then 0 else -1 := by
  rcases n with _ | k
  · rw [if_pos rfl]; exact Submission.CDT.coeff_sympY_zero
  · rcases k with _ | j
    · rw [if_neg (by norm_num : (1 : ℕ) ≠ 0), if_pos rfl]
      exact Submission.CDT.coeff_sympY_one
    · rw [if_neg (by omega : ¬ ((j + 2 : ℕ) = 0)),
        if_neg (by omega : ¬ ((j + 2 : ℕ) = 1))]
      show PowerSeries.coeff (j + 2) (PowerSeries.X * Submission.CDT.sympPhi) = -1
      rw [PowerSeries.coeff_succ_X_mul, coeff_sympPhi_eq (j + 1), if_neg (Nat.succ_ne_zero j)]

theorem evp_sympPhi (z : ℂ) (hz : ‖z‖ < 1) :
    (evp Submission.CDT.sympPhi z = z / (z - 1)) ∧
      (evp Submission.CDT.sympY z = z ^ 2 / (z - 1)) := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have h1mz : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hzm1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hsum : Summable (fun n : ℕ => z ^ n) := summable_geometric_of_norm_lt_one hz
  have hgeom : ∑' n : ℕ, z ^ n = (1 - z)⁻¹ := tsum_geometric_of_norm_lt_one hz
  have hind0 : Summable (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun b hb => by simp at hb; simp [hb])
  have hind1 : Summable (fun n : ℕ => if n = 1 then z else 0) :=
    summable_of_ne_finset_zero (s := {1}) (fun b hb => by simp at hb; simp [hb])
  have hind0val : (∑' n : ℕ, (if n = 0 then (1 : ℂ) else 0)) = 1 := by
    rw [tsum_eq_single 0 (fun b hb => by simp [hb])]; simp
  have hind1val : (∑' n : ℕ, (if n = 1 then z else 0)) = z := by
    rw [tsum_eq_single 1 (fun b hb => by simp [hb])]; simp
  have hs1 : Summable (fun n : ℕ => -z ^ n + (if n = 0 then (1 : ℂ) else 0)) :=
    hsum.neg.add hind0
  constructor
  · have hfun : (fun n : ℕ => ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ) * z ^ n)
        = fun n : ℕ => -(z ^ n) + (if n = 0 then (1 : ℂ) else 0) := by
      funext n
      rw [coeff_sympPhi_eq n]
      rcases eq_or_ne n 0 with h | h
      · subst h; simp
      · simp [h]
    rw [evp, hfun, Summable.tsum_add hsum.neg hind0, tsum_neg, hgeom, hind0val]
    field_simp
    ring
  · have hfun : (fun n : ℕ => ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n)
        = fun n : ℕ => -(z ^ n) + (if n = 0 then (1 : ℂ) else 0) + (if n = 1 then z else 0) := by
      funext n
      rw [coeff_sympY_eq n]
      rcases eq_or_ne n 0 with h | h
      · subst h; simp
      · rcases eq_or_ne n 1 with h1 | h1
        · subst h1; simp
        · simp [h, h1]
    rw [evp, hfun, Summable.tsum_add hs1 hind1, Summable.tsum_add hsum.neg hind0,
      tsum_neg, hgeom, hind0val, hind1val]
    field_simp
    ring

end Work.CPull
