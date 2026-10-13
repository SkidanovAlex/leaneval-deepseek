import Mathlib

namespace Work.WilE3.Realify

theorem exists_chart_offset (β : ℝ) :
    ∃ (cc e : ℝ), (∃ n : ℤ, cc = n * Real.pi) ∧ e = Real.cos cc ∧ |β - cc| ≤ Real.pi / 2 ∧
      (∀ w : ℝ, |w - β| < Real.pi / 2 → Real.cos ((w - cc) / 2) ≠ 0) ∧
      ((e : ℂ) = Complex.exp ((cc : ℂ) * Complex.I)) := by
  -- Take `cc` to be the nearest multiple of `π` to `β`.
  let n : ℤ := ⌊β / Real.pi + 1 / 2⌋
  have hfloor : (n : ℝ) ≤ β / Real.pi + 1 / 2 := Int.floor_le _
  have hlt : β / Real.pi + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have habs : |(n : ℝ) - β / Real.pi| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hbnd : |β - (n : ℝ) * Real.pi| ≤ Real.pi / 2 := by
    have h : β - (n : ℝ) * Real.pi = Real.pi * (β / Real.pi - (n : ℝ)) := by
      rw [mul_sub, mul_div_cancel₀ β (ne_of_gt Real.pi_pos)]
      ring
    rw [h, abs_mul, abs_of_pos Real.pi_pos, abs_sub_comm]
    nlinarith [habs, Real.pi_pos]
  refine ⟨(n : ℝ) * Real.pi, Real.cos ((n : ℝ) * Real.pi), ⟨n, rfl⟩, rfl, hbnd, ?_, ?_⟩
  · -- For `w` near `β`, the argument `(w - cc)/2` stays strictly inside `(-π/2, π/2)`.
    intro w hw
    have hwb : |w - (n : ℝ) * Real.pi| < Real.pi := by
      have h : w - (n : ℝ) * Real.pi = (w - β) + (β - (n : ℝ) * Real.pi) := by ring
      rw [h]
      calc |(w - β) + (β - (n : ℝ) * Real.pi)| ≤ |w - β| + |β - (n : ℝ) * Real.pi| := abs_add_le _ _
        _ < Real.pi / 2 + Real.pi / 2 := by linarith
        _ = Real.pi := by ring
    have hmem : (w - (n : ℝ) * Real.pi) / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.mem_Ioo, ← abs_lt]
      rw [abs_div, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
      rw [div_lt_iff₀ (show (0:ℝ) < 2 by norm_num)]
      linarith [hwb]
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
  · -- Since `cc` is a multiple of `π`, `exp(cc * I) = cos cc` is real.
    have hsin : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi n
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin]
    simp

end Work.WilE3.Realify
