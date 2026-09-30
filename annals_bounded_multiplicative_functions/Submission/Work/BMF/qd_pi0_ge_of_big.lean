import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `a ≥ P₀ ≥ (2 Cπ/(10 c₀³) + 2)²` we have `π₀(a) = a / log a ≥ Cπ/(20 c₀³) + 1`.
The bound is obtained from `log a ≤ 2 √a`, so `a / log a ≥ √a / 2`, and
`√a ≥ Cπ/(5 c₀³) + 2`, hence `√a / 2 ≥ Cπ/(10 c₀³) + 1 ≥ Cπ/(20 c₀³) + 1`. -/
theorem qd_pi0_ge_of_big {c₀ Cπ a P₀ : ℝ} (hc₀ : 0 < c₀) (hCπ : 0 < Cπ)
    (ha1 : 1 < a) (hP₀a : P₀ ≤ a) (hP₀big : (2 * Cπ / (10 * c₀ ^ 3) + 2) ^ 2 ≤ P₀) :
    pi0 a ≥ Cπ / (20 * c₀ ^ 3) + 1 := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha1
  have hc0cube : 0 < c₀ ^ 3 := by positivity
  have hlogpos : 0 < Real.log a := Real.log_pos ha1
  -- `log a ≤ 2 √a`, hence `a / log a ≥ a / (2 √a) = √a / 2`.
  have hlogle : Real.log a ≤ 2 * Real.sqrt a := by
    have h := Real.log_le_rpow_div (x := a) (ε := 1 / 2) (le_of_lt ha0) (by norm_num)
    rw [← Real.sqrt_eq_rpow a] at h
    have h2 : Real.sqrt a / (1 / 2 : ℝ) = 2 * Real.sqrt a := by ring
    rwa [h2] at h
  -- `√a ≥ Cπ/(5 c₀³) + 2`.
  have hTnn : 0 ≤ Cπ / (5 * c₀ ^ 3) + 2 := by positivity
  have hbig : Cπ / (5 * c₀ ^ 3) + 2 ≤ Real.sqrt a := by
    have hsq : (Cπ / (5 * c₀ ^ 3) + 2) ^ 2 ≤ a := by
      have h := hP₀big
      have heq : 2 * Cπ / (10 * c₀ ^ 3) + 2 = Cπ / (5 * c₀ ^ 3) + 2 := by
        have hne : c₀ ^ 3 ≠ 0 := ne_of_gt (pow_pos hc₀ 3)
        field_simp
        ring
      rw [heq] at h
      linarith
    calc Cπ / (5 * c₀ ^ 3) + 2 = Real.sqrt ((Cπ / (5 * c₀ ^ 3) + 2) ^ 2) :=
          (Real.sqrt_sq hTnn).symm
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt hsq
  have hkey1 : a / (2 * Real.sqrt a) ≤ a / Real.log a :=
    div_le_div_of_nonneg_left (le_of_lt ha0) hlogpos hlogle
  have hkey2 : a / (2 * Real.sqrt a) = Real.sqrt a / 2 := by
    rw [show a / (2 * Real.sqrt a) = (a / Real.sqrt a) / 2 by ring]
    rw [Real.div_sqrt]
  -- `Cπ/(20 c₀³) ≤ Cπ/(10 c₀³)`.
  have hstep : Cπ / (20 * c₀ ^ 3) + 1 ≤ Cπ / (10 * c₀ ^ 3) + 1 := by
    have h : Cπ / (20 * c₀ ^ 3) ≤ Cπ / (10 * c₀ ^ 3) :=
      div_le_div_of_nonneg_left (le_of_lt hCπ) (by positivity)
        (by nlinarith [hc0cube])
    linarith
  have hT2 : Cπ / (10 * c₀ ^ 3) + 1 = (Cπ / (5 * c₀ ^ 3) + 2) / 2 := by
    have hne : c₀ ^ 3 ≠ 0 := ne_of_gt (pow_pos hc₀ 3)
    field_simp
    ring
  rw [pi0]
  linarith [hstep, hT2, hbig, hkey1, hkey2, hTnn]

end Work.BMF
