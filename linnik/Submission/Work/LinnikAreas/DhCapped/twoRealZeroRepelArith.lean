import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas.DhCapped

/-- **Arithmetic of the two-real-zeros repulsion.**  With `r = √λ₀/L`, `a = λ₀/L`, `s = λ₂/L`:
`1/(r+a) + 1/(r+s) ≤ 1/r + K` implies `1/(r+s) ≤ a/(r(r+a)) + K = L/(1+√λ₀) + K ≤ L + K ≤ 23L/11`
(using `λ₀ ≤ 1/100`, `log N ≤ L`, `11(C+1) ≤ L`), hence `s ≥ 11/(23L) - √λ₀/L ≥ 87/(230L)`, i.e.
`λ₂ ≥ 87/230 > 1/4`. -/
theorem twoRealZeroRepelArith {lam0 lam2 L N C : ℝ} (hC : 0 ≤ C) (hlam0 : 0 < lam0)
    (hlam0le : lam0 ≤ 1 / 100) (hlam2 : 0 < lam2) (hL : 0 < L) (hN1 : 1 ≤ N)
    (hN : Real.log N ≤ L) (hLbig : 11 * (C + 1) ≤ L)
    (h : 1 / (Real.sqrt lam0 / L + lam0 / L) + 1 / (Real.sqrt lam0 / L + lam2 / L)
        ≤ (Real.sqrt lam0 / L)⁻¹ + C + Real.log N + Real.log 2 / 2 + 1 / 2) :
    1 / 4 ≤ lam2 := by
  -- Abbreviate `r = √λ₀/L` and `s = λ₂/L`.
  set r : ℝ := Real.sqrt lam0 / L with hr
  set s : ℝ := lam2 / L with hs
  have hrpos : 0 < r := by rw [hr]; positivity
  have hspos : 0 < s := by rw [hs]; positivity
  -- **Step 1.**  `1/(r+a) + 1/(r+s) ≤ 1/r + K` gives `1/(r+s) ≤ a/(r(r+a)) + K`
  -- because `1/r - 1/(r+a) = a/(r(r+a))`.
  have hK : 1 / (r + s) ≤ (lam0 / L) / (r * (r + lam0 / L))
      + (C + Real.log N + Real.log 2 / 2 + 1 / 2) := by
    have hident : 1 / r - 1 / (r + lam0 / L) = (lam0 / L) / (r * (r + lam0 / L)) := by
      have h1 : r ≠ 0 := ne_of_gt hrpos
      have h2 : r + lam0 / L ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    have hrinv : r⁻¹ = 1 / r := by rw [one_div]
    rw [hrinv] at h
    linarith [h, hident]
  -- **Step 2.**  `a/(r(r+a)) = L/(1+√λ₀) ≤ L`.
  have hbnd1 : (lam0 / L) / (r * (r + lam0 / L)) ≤ L := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < r * (r + lam0 / L))]
    rw [hr]
    have hexp : L * (Real.sqrt lam0 / L * (Real.sqrt lam0 / L + lam0 / L))
        = lam0 / L + Real.sqrt lam0 * (lam0 / L) := by
      field_simp
      nlinarith [Real.sq_sqrt (le_of_lt hlam0)]
    rw [hexp]
    have hnn : 0 ≤ Real.sqrt lam0 * (lam0 / L) := by positivity
    linarith
  -- **Step 3.**  `K = C + log N + log 2/2 + 1/2 ≤ 12L/11`.
  have hbnd2 : C + Real.log N + Real.log 2 / 2 + 1 / 2 ≤ 12 * L / 11 := by
    have hlog2 : Real.log 2 / 2 ≤ 1 / 2 := by
      have h1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        linarith
      linarith
    have hC' : C ≤ L / 11 - 1 := by
      have h1 : C + 1 ≤ L / 11 := by nlinarith [hLbig]
      linarith
    linarith
  -- **Step 4.**  `1/(r+s) ≤ L + 12L/11 = 23L/11`.
  have hfinal : 1 / (r + s) ≤ 23 * L / 11 := by
    linarith [hK, hbnd1, hbnd2]
  have hrs_pos : 0 < r + s := by linarith
  -- **Step 5.**  Hence `r + s ≥ 11/(23L)`.
  have hstep : 11 / (23 * L) ≤ r + s := by
    have hL23 : 0 < 23 * L := by linarith
    rw [div_le_iff₀ hL23]
    have h2 : 1 ≤ (23 * L / 11) * (r + s) := (div_le_iff₀ hrs_pos).mp hfinal
    nlinarith [h2]
  -- **Step 6.**  `λ₀ ≤ 1/100` gives `r ≤ 1/(10L)`, so
  -- `s ≥ 11/(23L) - 1/(10L) = 87/(230L)`.
  have hsl : Real.sqrt lam0 ≤ 1 / 10 := by
    have h1 : Real.sqrt lam0 ≤ Real.sqrt (1 / 100) := Real.sqrt_le_sqrt hlam0le
    have h2 : Real.sqrt (1 / 100 : ℝ) = 1 / 10 := by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hrle : r ≤ 1 / (10 * L) := by
    rw [hr]
    have h3 := div_le_div_of_nonneg_right hsl hL.le
    have e : (1 / 10 : ℝ) / L = 1 / (10 * L) := by field_simp
    linarith
  have hs87 : 87 / (230 * L) ≤ s := by
    have h1 : 11 / (23 * L) - r ≤ s := by linarith [hstep]
    have h2 : 11 / (23 * L) - 1 / (10 * L) ≤ 11 / (23 * L) - r := by linarith [hrle]
    have hcalc : (11 : ℝ) / (23 * L) - 1 / (10 * L) = 87 / (230 * L) := by
      field_simp
      ring
    linarith [h1, h2, hcalc]
  -- **Step 7.**  `λ₂ = sL ≥ 87/230 > 1/4`.
  have h87 : 87 / 230 ≤ lam2 := by
    have h' : 87 / (230 * L) ≤ lam2 / L := by rw [← hs]; exact hs87
    have hmul := mul_le_mul_of_nonneg_right h' hL.le
    have e1 : 87 / (230 * L) * L = 87 / 230 := by field_simp
    have e2 : lam2 / L * L = lam2 := by field_simp
    linarith [hmul, e1, e2]
  have hquarter : (1:ℝ) / 4 ≤ 87 / 230 := by norm_num
  linarith

end Work.LinnikAreas.DhCapped
