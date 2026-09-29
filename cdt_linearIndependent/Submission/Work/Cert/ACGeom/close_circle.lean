import Mathlib
import Submission.Work.Cert.ACGeom.GeomAux

/-!
# Certificate points are close to the circle of radius `Rk k / S`

`geomOK L` checks the *integer* condition
`iabs (Ax² + Ay² − Rk k²) ≤ 2 · Rk k · CTOL`.  This file converts it into the geometric statement
needed downstream: the scaled point `cx x y = ((x + i y)/S)` lies within `2·CTOL/S` of the circle of
radius `Rk k / S` centred at the origin.

The analytic content is the elementary estimate.  Writing `r = √(x² + y²)` and `R = (Rk k : ℝ)`,
the hypothesis says `|r² − R²| ≤ 2RC` with `C = (CTOL : ℝ) > 0`; since
`r² − R² = (r − R)(r + R)` and `r + R ≥ R > 0` one gets `|r − R| ≤ |r² − R²| / R ≤ 2C`.
Dividing by `S > 0` gives the claim (using `‖cx x y‖ = r / S`).
-/
namespace Work.Cert.ACGeom

open Work.Cert

theorem close_circle (x y : ℤ) (k : ℕ)
    (h : iabs (x * x + y * y - Rk k * Rk k) ≤ 2 * Rk k * CTOL) :
    |‖cx x y‖ - (Rk k : ℝ) / (S : ℝ)| ≤ 2 * (CTOL : ℝ) / (S : ℝ) := by
  -- pass to the real inequality `|x² + y² − Rk k²| ≤ 2·Rk k·CTOL`
  have hreal : |((x * x + y * y - Rk k * Rk k : ℤ) : ℝ)| ≤ ((2 * Rk k * CTOL : ℤ) : ℝ) := by
    have h' : ((iabs (x * x + y * y - Rk k * Rk k) : ℤ) : ℝ) ≤ ((2 * Rk k * CTOL : ℤ) : ℝ) := by
      exact_mod_cast h
    rwa [iabs_cast] at h'
  have hNR : |(x:ℝ)^2 + (y:ℝ)^2 - (Rk k:ℝ)^2| ≤ 2 * (Rk k:ℝ) * (CTOL:ℝ) := by
    have h1 := hreal
    have e1 : ((x * x + y * y - Rk k * Rk k : ℤ) : ℝ) = (x:ℝ)^2 + (y:ℝ)^2 - (Rk k:ℝ)^2 := by
      push_cast; ring
    have e2 : ((2 * Rk k * CTOL : ℤ) : ℝ) = 2 * (Rk k:ℝ) * (CTOL:ℝ) := by push_cast; ring
    rwa [e1, e2] at h1
  set N : ℝ := (x:ℝ)^2 + (y:ℝ)^2 with hN
  set R : ℝ := (Rk k : ℝ) with hRdef
  set C : ℝ := (CTOL : ℝ) with hCdef
  have hRpos : 0 < R := Rk_pos_real k
  have hCpos : 0 < C := CTOL_pos
  have hNR' : |N - R^2| ≤ 2 * R * C := hNR
  have hNnn : 0 ≤ N := by positivity
  set r : ℝ := Real.sqrt N with hrdef
  have hr2 : r^2 = N := Real.sq_sqrt hNnn
  have hrnn : 0 ≤ r := Real.sqrt_nonneg N
  have hsum : 0 < r + R := by linarith
  -- the exact identity `|r − R|·(r + R) = |r² − R²|`
  have hkey : |r - R| * (r + R) = |N - R^2| := by
    have h2 : |r - R| * (r + R) = |(r - R) * (r + R)| := by
      rw [abs_mul, abs_of_pos hsum]
    rw [h2, show (r - R) * (r + R) = r^2 - R^2 by ring, hr2]
  have hbound : |r - R| ≤ 2 * C := by
    have h3 : |r - R| * R ≤ 2 * R * C := by
      have h4 : |r - R| * R ≤ |r - R| * (r + R) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        linarith
      linarith [hkey, hNR']
    have h5 : |r - R| * R ≤ (2 * C) * R := by nlinarith [h3]
    exact (mul_le_mul_iff_of_pos_right hRpos).mp h5
  -- identify `‖cx x y‖` with `r / S`
  have hnorm : ‖cx x y‖ = r / (S : ℝ) := by
    have hsq : (r / (S:ℝ))^2 = ‖cx x y‖^2 := by
      rw [div_pow, hr2, hN, norm_sq_cx]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
    · exact hh.symm
    · have h1 : (0:ℝ) ≤ r/(S:ℝ) := div_nonneg hrnn (le_of_lt S_pos)
      have h2 : (0:ℝ) ≤ ‖cx x y‖ := norm_nonneg _
      linarith
  rw [hnorm, ← sub_div, abs_div, abs_of_pos S_pos]
  exact div_le_div_of_nonneg_right hbound (le_of_lt S_pos)

end Work.Cert.ACGeom
