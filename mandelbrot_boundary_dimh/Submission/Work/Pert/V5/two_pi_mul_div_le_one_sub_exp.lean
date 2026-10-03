import Mathlib

namespace Work.Pert.V5

theorem two_pi_mul_div_le_one_sub_exp {u D : ℝ} (hu : 1 / 4 ≤ u) (hD : 0 < D) (hDu : D ≤ u + 1 / 2) :
    2 * Real.pi * D / (2 * Real.pi * D + 9) ≤ 1 - Real.exp (-(2 * Real.pi * u)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA9 : 0 < 2 * Real.pi * D + 9 := by positivity
  have hS9 : 0 < 2 * Real.pi * u + Real.pi + 9 := by positivity
  -- `D ≤ u + 1/2`  ⇒  `2πD ≤ 2πu + π`
  have hAle : 2 * Real.pi * D ≤ 2 * Real.pi * u + Real.pi := by nlinarith [hpi, hDu]
  -- `1/4 ≤ u`  ⇒  `π/8 ≤ 2πu`
  have hSge : Real.pi / 8 ≤ 2 * Real.pi * u := by nlinarith [hpi, hu]
  -- `t ↦ t/(t+9)` is increasing, so the left side only grows when `D` is replaced by `u + 1/2`
  have step1 : 2 * Real.pi * D / (2 * Real.pi * D + 9)
      ≤ (2 * Real.pi * u + Real.pi) / (2 * Real.pi * u + Real.pi + 9) := by
    rw [div_le_div_iff₀ hA9 hS9]
    nlinarith
  -- `9 e^s ≥ s + π + 9` for `s = 2πu ≥ π/8`, from `e^s ≥ 1 + s`
  have hexp : 2 * Real.pi * u + Real.pi + 9 ≤ 9 * Real.exp (2 * Real.pi * u) := by
    have h := Real.add_one_le_exp (2 * Real.pi * u)
    nlinarith [hSge]
  -- `(s+π)/(s+π+9) = 1 - 9/(s+π+9) ≤ 1 - e^{-s}`
  have step2 : (2 * Real.pi * u + Real.pi) / (2 * Real.pi * u + Real.pi + 9)
      ≤ 1 - Real.exp (-(2 * Real.pi * u)) := by
    have key : 1 / Real.exp (2 * Real.pi * u)
        ≤ 1 / ((2 * Real.pi * u + Real.pi + 9)/9) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have key3 : Real.exp (-(2 * Real.pi * u)) ≤ 9 / (2 * Real.pi * u + Real.pi + 9) := by
      calc Real.exp (-(2 * Real.pi * u)) = 1 / Real.exp (2 * Real.pi * u) := by
              rw [Real.exp_neg, one_div]
        _ ≤ 1 / ((2 * Real.pi * u + Real.pi + 9)/9) := key
        _ = 9 / (2 * Real.pi * u + Real.pi + 9) := by rw [one_div_div]
    have hsub : (2 * Real.pi * u + Real.pi) / (2 * Real.pi * u + Real.pi + 9)
        = 1 - 9 / (2 * Real.pi * u + Real.pi + 9) := by
      field_simp
      ring
    rw [hsub]
    linarith
  linarith [step1, step2]

end Work.Pert.V5
