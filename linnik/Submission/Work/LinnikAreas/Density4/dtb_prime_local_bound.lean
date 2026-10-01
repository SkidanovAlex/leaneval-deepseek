import Mathlib

namespace Work.LinnikAreas.Density4

/-- Auxiliary real inequality: if `S, D, c > 0`, `S² = D + 1` and `c ≤ S + 1`, then
`1 + S/D ≤ (1 + 1/S) * (1 + 1/(D*c))`.
Clearing the (positive) denominator `S*D*c` reduces it to `S + 1 - c ≥ 0`. -/
private lemma dtb_prime_local_bound_aux (S D c : ℝ) (hS : 0 < S) (hD : 0 < D) (hc : 0 < c)
    (hSq : S ^ 2 = D + 1) (hle : c ≤ S + 1) :
    1 + S / D ≤ (1 + 1 / S) * (1 + 1 / (D * c)) := by
  have hSDc : 0 < S * D * c := by positivity
  rw [← sub_nonneg]
  have hkey : (1 + 1 / S) * (1 + 1 / (D * c)) - (1 + S / D)
      = (S + 1 - c) / (S * D * c) := by
    field_simp
    nlinarith [hSq]
  rw [hkey]
  exact div_nonneg (by linarith) (le_of_lt hSDc)

theorem dtb_prime_local_bound (p : ℕ) (hp : p.Prime) :
    (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1))
      ≤ (1 + 1 / Real.sqrt (p : ℝ)) * (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hPpos : (0 : ℝ) < (p : ℝ) := by linarith
  set S : ℝ := Real.sqrt (p : ℝ) with hSdef
  set D : ℝ := (p : ℝ) - 1 with hDdef
  set c : ℝ := Real.sqrt D with hcdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.sqrt_pos.mpr hPpos
  have hSsq : S ^ 2 = (p : ℝ) := by rw [hSdef]; exact Real.sq_sqrt (le_of_lt hPpos)
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hD_eq : D = S ^ 2 - 1 := by rw [hDdef]; rw [← hSsq]
  have hcpos : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.mpr hDpos
  have hSsq_eq : S ^ 2 = D + 1 := by rw [hD_eq]; ring
  have hle : c ≤ S + 1 := by
    have h1 : Real.sqrt D ≤ Real.sqrt (S ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hD_eq])
    rw [← hcdef, Real.sqrt_sq (le_of_lt hSpos)] at h1
    linarith
  have hrpow : D ^ (3 / 2 : ℝ) = D * c := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hDpos, Real.rpow_one]
    rw [← Real.sqrt_eq_rpow, hcdef]
  rw [hrpow]
  exact dtb_prime_local_bound_aux S D c hSpos hDpos hcpos hSsq_eq hle

end Work.LinnikAreas.Density4
