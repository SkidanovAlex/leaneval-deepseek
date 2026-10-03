import Mathlib

namespace Work.FIArea2.SevenSix

/-- The purely algebraic core of the pointwise bound: for `R > 0`, `r > 0`, `q > 0` and
`r ^ 2 * q ≤ R`, the factor `R ^ (3/8) * r ^ (-3/4) * q ^ (-3/8)` is at least `1`. -/
private lemma key_rpow {R r q : ℝ} (hR : 0 < R) (hr : 0 < r) (hq : 0 < q)
    (hrq : r ^ 2 * q ≤ R) :
    1 ≤ R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) * q ^ (-(3 : ℝ) / 8) := by
  have hRq : (1 : ℝ) ≤ R / (r ^ 2 * q) := by
    rw [one_le_div (by positivity)]
    exact hrq
  have h2 : (1 : ℝ) ≤ (R / (r ^ 2 * q)) ^ ((3 : ℝ) / 8) := by
    have h3 := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) hRq
      (show (0 : ℝ) ≤ (3 : ℝ) / 8 by norm_num)
    rwa [Real.one_rpow] at h3
  calc (1 : ℝ) ≤ (R / (r ^ 2 * q)) ^ ((3 : ℝ) / 8) := h2
    _ = R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) * q ^ (-(3 : ℝ) / 8) := by
        rw [Real.div_rpow hR.le (by positivity),
            Real.mul_rpow (z := ((3 : ℝ) / 8)) (sq_nonneg r) hq.le,
            show (r ^ 2 : ℝ) = r ^ ((2 : ℝ)) by
              rw [show (r ^ 2 : ℝ) = r ^ (((2 : ℕ) : ℝ)) from (Real.rpow_natCast r 2).symm]
              congr 1,
            ← Real.rpow_mul hr.le (2 : ℝ) ((3 : ℝ) / 8),
            show (2 : ℝ) * ((3 : ℝ) / 8) = (3 : ℝ) / 4 by norm_num,
            show r ^ (-(3 : ℝ) / 4) = (r ^ ((3 : ℝ) / 4))⁻¹ by
              rw [neg_div]; exact Real.rpow_neg hr.le ((3 : ℝ) / 4),
            show q ^ (-(3 : ℝ) / 8) = (q ^ ((3 : ℝ) / 8))⁻¹ by
              rw [neg_div]; exact Real.rpow_neg hq.le ((3 : ℝ) / 8),
            div_eq_mul_inv, mul_inv]
        ring

theorem quad_pointwise_le (f : ℝ → ℝ) (γ M R : ℝ) (hf0 : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (hR1 : 1 ≤ R) (hR : ∀ x, R ≤ x → f x = 0) (hγ : γ ^ 2 < 1) :
    ∀ r : ℝ, 0 < r → ∀ w : ℝ, 0 < w →
      ‖f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w‖ ≤
        Set.indicator (Set.Iio (Real.sqrt (R / (1 - γ ^ 2))))
          (fun r => M * R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4)) r *
        ((w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2)) := by
  intro r hr w hw
  set q : ℝ := w ^ 2 - 2 * γ * w + 1 with hqdef
  have hc : 0 < 1 - γ ^ 2 := sub_pos.mpr hγ
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hq_ge : 1 - γ ^ 2 ≤ q := by rw [hqdef]; nlinarith [sq_nonneg (w - γ)]
  have hqpos : 0 < q := lt_of_lt_of_le hc hq_ge
  have hr2nn : 0 ≤ r ^ 2 := sq_nonneg r
  have hM0 : 0 ≤ M := le_trans (hf0 0) (hM 0)
  have hsqw : 0 < Real.sqrt w := Real.sqrt_pos_of_pos hw
  rcases lt_or_ge (r ^ 2 * q) R with hlt | hge
  · -- Case 1: `r ^ 2 * q < R`; the indicator is active.
    have hkey : 1 ≤ R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) * q ^ (-(3 : ℝ) / 8) :=
      key_rpow hRpos hr hqpos hlt.le
    have hmin : r ∈ Set.Iio (Real.sqrt (R / (1 - γ ^ 2))) := by
      rw [Set.mem_Iio, Real.lt_sqrt hr.le, lt_div_iff₀ hc]
      nlinarith [mul_le_mul_of_nonneg_left hq_ge hr2nn, hlt]
    rw [Set.indicator_of_mem hmin]
    have hL : ‖f (r ^ 2 * q) / Real.sqrt w‖ = f (r ^ 2 * q) / Real.sqrt w :=
      Real.norm_of_nonneg (div_nonneg (hf0 _) hsqw.le)
    rw [hL]
    have hMw : M / Real.sqrt w = M * w ^ (-(1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, neg_div, ← Real.rpow_neg hw.le ((1 : ℝ) / 2)]
    have hfinal : M * w ^ (-(1 : ℝ) / 2) ≤
        (M * R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4)) *
          (q ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2)) := by
      have h1 : M * (1 : ℝ) ≤ M * (R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) * q ^ (-(3 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left hkey hM0
      have h2 : (M * (1 : ℝ)) * w ^ (-(1 : ℝ) / 2) ≤
          (M * (R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) * q ^ (-(3 : ℝ) / 8))) *
            w ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hw.le _)
      calc M * w ^ (-(1 : ℝ) / 2) = (M * 1) * w ^ (-(1 : ℝ) / 2) := by ring
        _ ≤ (M * (R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) *
              q ^ (-(3 : ℝ) / 8))) * w ^ (-(1 : ℝ) / 2) := h2
        _ = (M * R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4)) *
              (q ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2)) := by ring
    calc f (r ^ 2 * q) / Real.sqrt w ≤ M / Real.sqrt w :=
          (div_le_div_iff_of_pos_right hsqw).mpr (hM _)
      _ = M * w ^ (-(1 : ℝ) / 2) := hMw
      _ ≤ (M * R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4)) *
            (q ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2)) := hfinal
  · -- Case 2: `R ≤ r ^ 2 * q`; here `f` vanishes at the argument.
    have hz : f (r ^ 2 * q) = 0 := hR (r ^ 2 * q) hge
    rw [hz, zero_div, norm_zero]
    apply mul_nonneg
    · by_cases hm : r < Real.sqrt (R / (1 - γ ^ 2))
      · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hm)]
        exact mul_nonneg (mul_nonneg hM0 (Real.rpow_nonneg hRpos.le _))
          (Real.rpow_nonneg hr.le _)
      · rw [Set.indicator_of_notMem (by simpa [Set.mem_Iio] using hm)]
    · exact mul_nonneg (Real.rpow_nonneg hqpos.le _) (Real.rpow_nonneg hw.le _)

end Work.FIArea2.SevenSix
