import Mathlib

namespace Work.FITop6.Sector.TrigAux

open Real

/-- Auxiliary trigonometric bound. For `r ∈ [0, π/2)` and any integer `n`, the value
`|cos (n * π/2 + r)|` is at least `sin (min r (π/2 - r))`, where `min r (π/2 - r)` is the
distance from `φ = n * π/2 + r` to the nearest multiple of `π/2`. -/
private lemma sin_min_le_abs_cos (n : ℤ) (r : ℝ) (hr0 : 0 ≤ r) (hr2 : r < Real.pi / 2) :
    Real.sin (min r (Real.pi / 2 - r)) ≤ |Real.cos ((n:ℝ) * (Real.pi / 2) + r)| := by
  have hmin_r : min r (Real.pi / 2 - r) ≤ r := min_le_left _ _
  have hmin_2 : min r (Real.pi / 2 - r) ≤ Real.pi / 2 - r := min_le_right _ _
  have hmin0 : 0 ≤ min r (Real.pi / 2 - r) := le_min hr0 (by linarith)
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · subst hk
    have harg : (((2 * k : ℤ)) : ℝ) * (Real.pi / 2) + r = r + (k:ℝ) * Real.pi := by
      push_cast; ring
    rw [harg, Real.cos_add_int_mul_pi]
    have hcr : 0 ≤ Real.cos r :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (le_of_lt hr2)
    rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, abs_of_nonneg hcr, one_mul]
    rw [← Real.sin_pi_div_two_sub r]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hmin_2
  · subst hk
    have harg : (((2 * k + 1 : ℤ)) : ℝ) * (Real.pi / 2) + r = (Real.pi / 2 + r) + (k:ℝ) * Real.pi := by
      push_cast; ring
    rw [harg, Real.cos_add_int_mul_pi]
    have hsr : 0 ≤ Real.sin r :=
      Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [hr2, Real.pi_pos])
    rw [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    rw [add_comm (Real.pi / 2) r, Real.cos_add_pi_div_two, abs_neg, abs_of_nonneg hsr]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) hmin_r

theorem abs_cos_gt_of_arg_dist {ϑ φ : ℝ}
    (h : ∀ m : ℤ, Real.pi * ϑ / 2 < |φ - (m : ℝ) * (Real.pi / 2)|) :
    ϑ < |Real.cos φ| := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  -- write φ as `n * π/2 + r` with `r ∈ [0, π/2)`
  set n : ℤ := ⌊2 * φ / Real.pi⌋ with hn
  set r : ℝ := φ - (n:ℝ) * (Real.pi / 2) with hr
  have hr_eq : φ = (n:ℝ) * (Real.pi / 2) + r := by rw [hr]; ring
  have hle : (n:ℝ) ≤ 2 * φ / Real.pi := Int.floor_le _
  have hlt : 2 * φ / Real.pi < (n:ℝ) + 1 := Int.lt_floor_add_one _
  have hkey : 2 * φ / Real.pi * (Real.pi / 2) = φ := by field_simp
  have hr0 : 0 ≤ r := by
    have h1 : (n:ℝ) * (Real.pi / 2) ≤ φ := by
      have := mul_le_mul_of_nonneg_right hle hpi2.le
      rwa [hkey] at this
    rw [hr]; linarith
  have hr2 : r < Real.pi / 2 := by
    have h1 : φ < ((n:ℝ) + 1) * (Real.pi / 2) := by
      have := mul_lt_mul_of_pos_right hlt hpi2
      rwa [hkey] at this
    rw [hr]; linarith
  -- the hypothesis says the distance of `φ` to the two neighbouring multiples of `π/2` exceeds `πϑ/2`
  have hcr : Real.pi * ϑ / 2 < r := by
    have h1 := h n
    rw [← hr, abs_of_nonneg hr0] at h1
    exact h1
  have hc2 : Real.pi * ϑ / 2 < Real.pi / 2 - r := by
    have h1 := h (n + 1)
    have hcast : (((n + 1 : ℤ)) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    rw [hcast] at h1
    have h2 : |φ - ((n:ℝ) + 1) * (Real.pi / 2)| = Real.pi / 2 - r := by
      rw [show φ - ((n:ℝ) + 1) * (Real.pi / 2) = -(Real.pi / 2 - r) by rw [hr]; ring]
      rw [abs_neg, abs_of_nonneg (by linarith)]
    rw [h2] at h1
    exact h1
  -- `d` is the distance of `φ` to the nearest multiple of `π/2`
  set d : ℝ := min r (Real.pi / 2 - r) with hd
  have hd_gt : Real.pi * ϑ / 2 < d := by rw [hd]; exact lt_min hcr hc2
  have hd0 : 0 ≤ d := by rw [hd]; exact le_min hr0 (by linarith)
  have hd_le : d ≤ Real.pi / 2 := by rw [hd]; linarith [min_le_right r (Real.pi / 2 - r)]
  -- Jordan's inequality and the geometric bound `sin d ≤ |cos φ|`
  have hsin : (2 / Real.pi) * d ≤ Real.sin d := Real.mul_le_sin hd0 hd_le
  have hcos : Real.sin d ≤ |Real.cos φ| := by
    have h3 := sin_min_le_abs_cos n r hr0 hr2
    rwa [← hd, ← hr_eq] at h3
  calc ϑ = 2 / Real.pi * (Real.pi * ϑ / 2) := by field_simp
    _ < 2 / Real.pi * d := by
        apply mul_lt_mul_of_pos_left hd_gt; positivity
    _ ≤ Real.sin d := hsin
    _ ≤ |Real.cos φ| := hcos

end Work.FITop6.Sector.TrigAux
