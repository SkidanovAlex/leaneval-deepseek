import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.tfp

/-- Fejér-kernel lower bound: `4/π² ≤ (sinc (πu))²` for `|u| ≤ 1/2`.  Jordan's inequality
`Real.mul_le_sin : 0 ≤ x → x ≤ π/2 → 2/π * x ≤ sin x` gives `sinc t ≥ 2/π` for
`t = π|u| ∈ [0, π/2]` (via `Real.sinc_of_ne_zero`, `Real.sinc_neg`, `Real.sinc_zero`), then
square the two nonnegative quantities; the `u = 0` case uses `π² ≥ 4`. -/
lemma sinc_sq_ge (u : ℝ) (hu : |u| ≤ 1/2) : 4 / Real.pi^2 ≤ (Real.sinc (Real.pi * u))^2 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  -- sinc is even, so reduce to the nonnegative argument `|u|`
  have hsinc : Real.sinc (Real.pi * u) = Real.sinc (Real.pi * |u|) := by
    rcases lt_or_ge u 0 with h | h
    · rw [abs_of_neg h]
      have hneg : Real.pi * u = -(Real.pi * -u) := by ring
      rw [hneg, Real.sinc_neg]
    · rw [abs_of_nonneg h]
  rw [hsinc]
  set v : ℝ := |u| with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact abs_nonneg u
  have hvle : v ≤ 1/2 := by rw [hv]; exact hu
  rcases eq_or_lt_of_le hv0 with hvz | hvpos
  · -- `v = 0`: `sinc 0 = 1` and `π² ≥ 4`
    have h4 : (4:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have h1 : (4:ℝ)/Real.pi^2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h4
    rw [← hvz, mul_zero, Real.sinc_zero]
    simpa using h1
  · -- `v > 0`: Jordan's inequality `2v ≤ sin (π v)`, then `sinc (π v) ≥ 2/π`
    have hπv_pos : 0 < Real.pi * v := mul_pos hpi hvpos
    have hπv_le : Real.pi * v ≤ Real.pi / 2 := by
      have hm := mul_le_mul_of_nonneg_left hvle (le_of_lt hpi)
      have he : Real.pi * (1/2) = Real.pi / 2 := by ring
      linarith [hm]
    have hsin := Real.mul_le_sin (le_of_lt hπv_pos) hπv_le
    have h2v : (2/Real.pi) * (Real.pi * v) = 2 * v := by field_simp
    have hle_sin : 2 * v ≤ Real.sin (Real.pi * v) := by
      rw [← h2v]; exact hsin
    have hvne : v ≠ 0 := ne_of_gt hvpos
    have hπvne : Real.pi * v ≠ 0 := mul_ne_zero Real.pi_ne_zero hvne
    have hdiv : (2 * v) / (Real.pi * v) ≤ Real.sin (Real.pi * v) / (Real.pi * v) :=
      div_le_div_of_nonneg_right hle_sin (le_of_lt hπv_pos)
    have hsimp : (2 * v) / (Real.pi * v) = 2 / Real.pi := by field_simp
    have hge : 2 / Real.pi ≤ Real.sinc (Real.pi * v) := by
      rw [Real.sinc_of_ne_zero hπvne, ← hsimp]
      exact hdiv
    have hpos : (0:ℝ) < 2 / Real.pi := by positivity
    have hsq := pow_le_pow_left₀ (le_of_lt hpos) hge 2
    have heq : (2/Real.pi)^2 = 4/Real.pi^2 := by ring
    rwa [heq] at hsq

end Work.BMF.tfp
