import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `1 ≤ y` and `4c² ≤ y`, the `c y^{1/10}` term is at most `y/2`.  Indeed
`y^{1/10} ≤ y^{1/2} = √y` and `c √y ≤ √(c² y) ≤ √((y/2)²) = y/2`, the middle
inequality coming from `c² y ≤ (y/2)² ⟺ 4c² ≤ y`. -/
private lemma c_mul_rpow_ten_le_half (c y : ℝ) (hc : 0 < c) (h1 : 1 ≤ y) (h4 : 4 * c^2 ≤ y) :
    c * y ^ (1/10 : ℝ) ≤ y / 2 := by
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one h1
  have hstep1 : y ^ (1/10 : ℝ) ≤ y ^ (1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  calc c * y ^ (1/10:ℝ) ≤ c * y ^ (1/2:ℝ) :=
        mul_le_mul_of_nonneg_left hstep1 hc.le
    _ = c * Real.sqrt y := by rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt (c^2 * y) := by
        rw [Real.sqrt_mul (sq_nonneg c) y, Real.sqrt_sq hc.le]
    _ ≤ Real.sqrt ((y/2)^2) := by
        apply Real.sqrt_le_sqrt; nlinarith [h4, hy_pos]
    _ = y/2 := Real.sqrt_sq (by linarith)

/-- The "large `y`" range: for `y ≥ max 1 (48A) (4c²)` the left-hand side
`A y log y` is dominated by `exp (y - c y^{1/10})`. -/
private lemma region_one (A c y : ℝ) (hA : 0 < A) (hc : 0 < c) (h1 : 1 ≤ y)
    (h48 : 48 * A ≤ y) (h4 : 4 * c^2 ≤ y) :
    A * y * Real.log y ≤ Real.exp (y - c * y ^ (1/10:ℝ)) := by
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one h1
  have hlog : Real.log y ≤ y := le_trans (Real.log_le_sub_one_of_pos hy_pos) (by linarith)
  have hAy : 0 ≤ A * y := by positivity
  have hstep : A * y * Real.log y ≤ A * y^2 := by
    have h := mul_le_mul_of_nonneg_left hlog hAy
    nlinarith [h]
  have hc_half : c * y ^ (1/10 : ℝ) ≤ y / 2 :=
    c_mul_rpow_ten_le_half c y hc h1 h4
  have hexp : A * y^2 ≤ Real.exp (y/2) := by
    have h3 := Real.pow_div_factorial_le_exp (y/2) (by linarith) 3
    have hfac : ((3:ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfac] at h3
    have hpoly : A * y^2 ≤ (y/2)^3 / 6 := by nlinarith [h48, hy_pos, sq_nonneg (y/2)]
    linarith [h3, hpoly]
  have harg : y/2 ≤ y - c * y^(1/10:ℝ) := by linarith [hc_half]
  calc A * y * Real.log y ≤ A * y^2 := hstep
    _ ≤ Real.exp (y/2) := hexp
    _ ≤ Real.exp (y - c * y^(1/10:ℝ)) := Real.exp_le_exp.mpr harg

/-- The "compact `y`" range `1 ≤ y ≤ Y`: since `exp (y - c y^{1/10})` is bounded
below by the positive constant `exp (1 - c Y^{1/10})` and `A y log y ≤ A Y log Y`,
the inequality holds with the constant `C = A Y log Y / exp (1 - c Y^{1/10})`. -/
private lemma region_two (A c y Y C : ℝ) (hA : 0 < A) (hc : 0 < c) (hY1 : 1 ≤ Y) (hy1 : 1 ≤ y)
    (hyY : y ≤ Y) (hCpos : 0 < C)
    (hC : A * Y * Real.log Y / Real.exp (1 - c * Y^(1/10:ℝ)) ≤ C) :
    A * y * Real.log y ≤ C * Real.exp (y - c * y^(1/10:ℝ)) := by
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hY_pos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hlogyY : Real.log y ≤ Real.log Y := Real.log_le_log hy_pos hyY
  have hlogy_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hAyY : A * y * Real.log y ≤ A * Y * Real.log Y := by
    have h1 : A * y ≤ A * Y := mul_le_mul_of_nonneg_left hyY hA.le
    have h2 : 0 ≤ A * Y := by positivity
    exact mul_le_mul h1 hlogyY hlogy_nonneg h2
  have hm_pos : 0 < Real.exp (1 - c * Y^(1/10:ℝ)) := Real.exp_pos _
  have hYpow : c * y^(1/10:ℝ) ≤ c * Y^(1/10:ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy_pos.le hyY (by norm_num)) hc.le
  have harg : 1 - c * Y^(1/10:ℝ) ≤ y - c * y^(1/10:ℝ) := by linarith
  have hm_le : Real.exp (1 - c * Y^(1/10:ℝ)) ≤ Real.exp (y - c * y^(1/10:ℝ)) :=
    Real.exp_le_exp.mpr harg
  have hstep1 : (A * Y * Real.log Y / Real.exp (1 - c * Y^(1/10:ℝ)))
      * Real.exp (1 - c * Y^(1/10:ℝ)) ≤ C * Real.exp (1 - c * Y^(1/10:ℝ)) :=
    mul_le_mul_of_nonneg_right hC hm_pos.le
  rw [div_mul_cancel₀ _ (ne_of_gt hm_pos)] at hstep1
  have hstep2 : C * Real.exp (1 - c * Y^(1/10:ℝ)) ≤ C * Real.exp (y - c * y^(1/10:ℝ)) :=
    mul_le_mul_of_nonneg_left hm_le hCpos.le
  linarith

/-- **Exponential domination of `y log y`.** For every `A > 0` and `c > 0` there is `C > 0` with
`A · y · log y ≤ C · exp(y − c y^{1/10})` for all `y ≥ 1`.  (`y log y` is beaten by
`exp(y − c y^{1/10})` at infinity; on the compact range `y ∈ [1, y₀]` both sides are finite, and
`y − c y^{1/10}` is bounded below by `−9(c/10)^{10/9}`.)  Used in `N10` (`vk_prime_sums`) to
absorb the `ω(q) log x` — with `q ≤ (log x)^A` — correction into the main error term
`x exp(−c (log x)^{1/10})`. -/
theorem log_mul_loglog_le_exp (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      A * y * Real.log y ≤ C * Real.exp (y - c * y ^ (1 / 10 : ℝ)) := by
  set Y : ℝ := max 1 (max (4 * c^2) (48 * A)) with hY
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hY4 : 4 * c^2 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY48 : 48 * A ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max 1 (A * Y * Real.log Y / Real.exp (1 - c * Y ^ (1/10:ℝ))), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro y hy1
    have hCpos : 0 < max 1 (A * Y * Real.log Y / Real.exp (1 - c * Y ^ (1/10:ℝ))) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    by_cases hYy : Y ≤ y
    · have hexp : Real.exp (y - c * y ^ (1/10:ℝ))
          ≤ max 1 (A * Y * Real.log Y / Real.exp (1 - c * Y ^ (1/10:ℝ)))
            * Real.exp (y - c * y ^ (1/10:ℝ)) :=
        le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
      exact le_trans (region_one A c y hA hc hy1 (le_trans hY48 hYy) (le_trans hY4 hYy)) hexp
    · exact region_two A c y Y _ hA hc hY1 hy1 (le_of_lt (not_le.mp hYy)) hCpos
        (le_max_right _ _)

end Work.BMF
