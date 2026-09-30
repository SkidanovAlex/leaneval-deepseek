import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- If `u` and `x'` both lie within `3H/(2a)` of `x₀`, then `|u - x'| ≤ 3H/a`; and if moreover
`t ≤ u + H/p` with `a ≤ p`, `a > 0`, `H > 0`, then `|t - x'| ≤ 4H/a`. -/
lemma cell_ball {H a p x₀ u x' t : ℝ} (ha : 0 < a) (hH : 0 < H) (hap : a ≤ p) (hu : |u - x₀| ≤ 3 * H / (2 * a)) (hx' : |x' - x₀| ≤ 3 * H / (2 * a)) (ht : t ∈ Set.Icc u (u + H / p)) : |u - x'| ≤ 3 * H / a ∧ |t - x'| ≤ 4 * (H / a) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hkey : 3 * H / (2 * a) + 3 * H / (2 * a) = 3 * H / a := by
    field_simp
    ring
  have hp : 0 < p := lt_of_lt_of_le ha hap
  have hmain : |u - x'| ≤ 3 * H / a := by
    calc |u - x'| = |(u - x₀) + (x₀ - x')| := by congr 1; ring
      _ ≤ |u - x₀| + |x₀ - x'| := abs_add_le _ _
      _ = |u - x₀| + |x' - x₀| := by rw [abs_sub_comm x₀ x']
      _ ≤ 3 * H / (2 * a) + 3 * H / (2 * a) := add_le_add hu hx'
      _ = 3 * H / a := hkey
  refine ⟨hmain, ?_⟩
  have hle : H / p ≤ H / a := div_le_div_of_nonneg_left (le_of_lt hH) ha hap
  have ht1 : u ≤ t := ht.1
  have ht2 : t ≤ u + H / p := ht.2
  have htu_abs : |t - u| ≤ H / p := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htu : |t - u| ≤ H / a := le_trans htu_abs hle
  calc |t - x'| = |(t - u) + (u - x')| := by congr 1; ring
    _ ≤ |t - u| + |u - x'| := abs_add_le _ _
    _ ≤ H / a + 3 * H / a := add_le_add htu hmain
    _ = 4 * (H / a) := by ring

end Work.BMF.SD
