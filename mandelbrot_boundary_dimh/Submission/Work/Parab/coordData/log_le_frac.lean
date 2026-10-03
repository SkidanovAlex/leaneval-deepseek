import Mathlib

namespace Work.Parab.coordData

theorem log_le_frac (c : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, M ≤ t → c * (1 + Real.log (2 + t)) ≤ t / 4 := by
  by_cases hc : c ≤ 0
  · -- for `c ≤ 0` the left-hand side is nonpositive as soon as `t ≥ 0`
    refine ⟨1, le_refl 1, fun t ht => ?_⟩
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
    have hlog : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
    have h1 : c * (1 + Real.log (2 + t)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    have h2 : (0 : ℝ) ≤ t / 4 := by linarith
    linarith
  · have hcpos : 0 < c := not_le.mp hc
    -- for `c > 0` use that `log` is little-o of the identity at `+∞`
    set ε : ℝ := 1 / (16 * c) with hεdef
    have hε : 0 < ε := by rw [hεdef]; positivity
    have hce : 2 * c * ε = 1 / 8 := by
      rw [hεdef]; field_simp; norm_num
    have hev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ ε * x := by
      filter_upwards [Real.isLittleO_log_id_atTop.bound hε,
        Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
      simp only [id_eq, Real.norm_eq_abs] at hx
      rw [abs_of_nonneg (Real.log_nonneg hx1),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
      exact hx
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨max 1 (max (8 * c) (max (N + 2) 2)), ?_, fun t ht => ?_⟩
    · exact le_max_left 1 (max (8 * c) (max (N + 2) 2))
    · have hmax1 : (1 : ℝ) ≤ max 1 (max (8 * c) (max (N + 2) 2)) :=
        le_max_left 1 (max (8 * c) (max (N + 2) 2))
      have hmax8 : 8 * c ≤ max 1 (max (8 * c) (max (N + 2) 2)) :=
        le_trans (le_max_left (8 * c) (max (N + 2) 2))
          (le_max_right 1 (max (8 * c) (max (N + 2) 2)))
      have hmaxN : N + 2 ≤ max 1 (max (8 * c) (max (N + 2) 2)) :=
        le_trans (le_trans (le_max_left (N + 2) 2)
            (le_max_right (8 * c) (max (N + 2) 2)))
          (le_max_right 1 (max (8 * c) (max (N + 2) 2)))
      have hmax2 : (2 : ℝ) ≤ max 1 (max (8 * c) (max (N + 2) 2)) :=
        le_trans (le_max_right (N + 2) 2)
          (le_trans (le_max_right (8 * c) (max (N + 2) 2))
            (le_max_right 1 (max (8 * c) (max (N + 2) 2))))
      have ht1 : (1 : ℝ) ≤ t := le_trans hmax1 ht
      have ht8c : 8 * c ≤ t := le_trans hmax8 ht
      have ht2 : (2 : ℝ) ≤ t := le_trans hmax2 ht
      have htN : N ≤ 2 + t := by
        have := le_trans hmaxN ht; linarith
      have hlogbound : Real.log (2 + t) ≤ ε * (2 + t) := hN (2 + t) htN
      have hlog2 : Real.log (2 + t) ≤ 2 * ε * t := by
        have h1 : ε * (2 + t) ≤ ε * (2 * t) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
          linarith
        nlinarith [hlogbound, h1, hε]
      have h2 : c * (1 + Real.log (2 + t)) ≤ c * (1 + 2 * ε * t) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hcpos)
      have h3 : c * (1 + 2 * ε * t) = c + 2 * c * ε * t := by ring
      have h4 : 2 * c * ε * t = (1 / 8) * t := by nlinarith [hce]
      have h5 : c ≤ t / 8 := by linarith
      linarith

end Work.Parab.coordData
