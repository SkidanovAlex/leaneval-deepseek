import Mathlib

namespace Work.Drive

/-- For a complex number `z`, the class of `arg z / π` in `ℝ ⧸ ℤ = UnitAddCircle` vanishes
exactly when `z` lies on the real axis.  Indeed `arg z ∈ (-π, π]`, so `arg z / π` lies in
`(-1, 1]`, and its image in `ℝ ⧸ ℤ` is `0` precisely when it equals `0` or `1`, i.e. when
`arg z = 0` (points on the non-negative real axis, including `0`) or `arg z = π` (points on
the negative real axis). -/
theorem arg_div_pi_coe_eq_zero_iff (z : ℂ) :
    ((Complex.arg z / Real.pi : ℝ) : UnitAddCircle) = 0 ↔ z.im = 0 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hne : Real.pi ≠ 0 := hpi.ne'
  -- `arg z / π` lies in `(-1, 1]`.
  have hmem : Complex.arg z / Real.pi ∈ Set.Ioc (-1) 1 := by
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hpi, neg_one_mul]
      exact Complex.neg_pi_lt_arg z
    · rw [div_le_iff₀ hpi, one_mul]
      exact Complex.arg_le_pi z
  constructor
  · -- If the class vanishes, then `arg z / π` is an integer, hence (being in `(-1, 1]`)
    -- it is `0` or `1`.
    intro h
    rw [AddCircle.coe_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    rw [zsmul_one] at hn
    have hn_lt : (-1:ℤ) < n := by
      have h' : (-1:ℝ) < (n:ℝ) := by rw [hn]; exact hmem.1
      exact_mod_cast h'
    have hn_le : n ≤ (1:ℤ) := by
      have h' : (n:ℝ) ≤ 1 := by rw [hn]; exact hmem.2
      exact_mod_cast h'
    have harg : Complex.arg z = (n:ℝ) * Real.pi := by
      rw [hn]
      exact (div_mul_cancel₀ (Complex.arg z) hne).symm
    rcases (show n = 0 ∨ n = 1 by omega) with h0 | h1
    · rw [h0] at harg
      simp at harg
      exact (Complex.arg_eq_zero_iff.mp harg).2
    · rw [h1] at harg
      simp at harg
      exact (Complex.arg_eq_pi_iff.mp harg).2
  · -- Conversely a real `z` has `arg z = 0` (if `z.re ≥ 0`) or `arg z = π` (if `z.re < 0`).
    intro h
    by_cases hre : 0 ≤ z.re
    · have harg : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hre, h⟩
      rw [harg, zero_div]
      simp
    · have hre' : z.re < 0 := lt_of_not_ge hre
      have harg : Complex.arg z = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre', h⟩
      rw [harg, div_self hne]
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨1, by simp⟩

end Work.Drive
