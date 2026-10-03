import Mathlib

namespace Work.FIArea2.SevenSix

open MeasureTheory Set

/-- `Q(w) = w² - 2γw + 1` is positive when `γ² < 1`, since
`Q(w) = (w - γ)² + (1 - γ²)`. -/
private lemma quad_pos {γ : ℝ} (hγ : γ ^ 2 < 1) (w : ℝ) :
    0 < w ^ 2 - 2 * γ * w + 1 := by
  have hpos : 0 < 1 - γ ^ 2 := by nlinarith
  have : 1 - γ ^ 2 ≤ w ^ 2 - 2 * γ * w + 1 := by nlinarith [sq_nonneg (w - γ)]
  linarith

/-- Near `0` the factor `Q(w)^{-3/8}` is bounded by the constant `(1-γ²)^{-3/8}`. -/
private lemma quad_lower_near_zero {γ w : ℝ} :
    1 - γ ^ 2 ≤ w ^ 2 - 2 * γ * w + 1 := by
  nlinarith [sq_nonneg (w - γ)]

/-- On the whole line, `Q(w) ≥ w²(1-γ²)`: this gives the decay `Q(w)^{-3/8} ≲ w^{-3/4}`
at infinity. -/
private lemma quad_lower_far {γ w : ℝ} :
    w ^ 2 * (1 - γ ^ 2) ≤ w ^ 2 - 2 * γ * w + 1 := by
  nlinarith [sq_nonneg (1 - γ * w)]

theorem quad_B_integrable (γ : ℝ) (hγ : γ ^ 2 < 1) :
    MeasureTheory.IntegrableOn
      (fun w : ℝ => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2))
      (Set.Ioi 0) := by
  have hpos : 0 < 1 - γ ^ 2 := by nlinarith
  -- Continuity of the integrand on `(0,∞)`.
  have hcont : ContinuousOn
      (fun w : ℝ => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2))
      (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun w : ℝ => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8))
        (Set.Ioi 0) := by
      refine ContinuousOn.rpow_const (f := fun w : ℝ => w ^ 2 - 2 * γ * w + 1)
        (p := -(3 : ℝ) / 8) ?_ ?_
      · fun_prop
      · intro x _
        left
        exact (quad_pos hγ x).ne'
    have h2 : ContinuousOn (fun w : ℝ => w ^ (-(1 : ℝ) / 2)) (Set.Ioi 0) := by
      refine ContinuousOn.rpow_const (f := fun w : ℝ => w) (p := -(1 : ℝ) / 2) ?_ ?_
      · exact continuousOn_id
      · intro x hx
        left
        exact ne_of_gt hx
    exact h1.mul h2
  -- Part 1: integrability on `(0,1]`, where the first factor is bounded.
  have hA : IntegrableOn
      (fun w : ℝ => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2))
      (Set.Ioc 0 1) := by
    have hg : IntegrableOn (fun w : ℝ => (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2))
        (Set.Ioc 0 1) := by
      have h0 : IntegrableOn (fun w : ℝ => w ^ (-(1 : ℝ) / 2)) (Set.Ioc 0 1) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact (intervalIntegral.integrableOn_Ioo_rpow_iff (t := 1) one_pos).mpr (by norm_num)
      exact h0.const_mul _
    refine Integrable.mono' hg ?_ ?_
    · exact (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      have hwpos : 0 < w := hw.1
      have hQ : 1 - γ ^ 2 ≤ w ^ 2 - 2 * γ * w + 1 := quad_lower_near_zero
      have hb1 : (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) ≤ (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) :=
        Real.rpow_le_rpow_of_nonpos hpos hQ (by norm_num)
      have hb2 : 0 ≤ w ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hwpos.le _
      have hposf : 0 ≤ (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2) :=
        mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (quad_pos hγ w) _)) hb2
      rw [Real.norm_eq_abs, abs_of_nonneg hposf]
      exact mul_le_mul_of_nonneg_right hb1 hb2
  -- Part 2: integrability on `(1,∞)`, where the first factor decays like `w^{-3/4}`.
  have hB : IntegrableOn
      (fun w : ℝ => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2))
      (Set.Ioi 1) := by
    have hg : IntegrableOn (fun w : ℝ => (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * w ^ (-(5 : ℝ) / 4))
        (Set.Ioi 1) := by
      have h0 : IntegrableOn (fun w : ℝ => w ^ (-(5 : ℝ) / 4)) (Set.Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
      exact h0.const_mul _
    refine Integrable.mono' hg ?_ ?_
    · exact (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hwpos : 0 < w := lt_trans zero_lt_one hw
      have hQ : w ^ 2 * (1 - γ ^ 2) ≤ w ^ 2 - 2 * γ * w + 1 := quad_lower_far
      have hQ0 : 0 < w ^ 2 * (1 - γ ^ 2) := mul_pos (pow_pos hwpos 2) hpos
      have heq1 : (w ^ 2) ^ (-(3 : ℝ) / 8) = w ^ (-(3 : ℝ) / 4) := by
        rw [← Real.rpow_natCast w 2, ← Real.rpow_mul hwpos.le]
        norm_num
      have heq : (w ^ 2 * (1 - γ ^ 2)) ^ (-(3 : ℝ) / 8)
          = (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * w ^ (-(3 : ℝ) / 4) := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ w ^ 2) hpos.le, heq1, mul_comm]
      have hb1 : (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8)
          ≤ (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * w ^ (-(3 : ℝ) / 4) := by
        rw [← heq]
        exact Real.rpow_le_rpow_of_nonpos hQ0 hQ (by norm_num)
      have hb2 : 0 ≤ w ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hwpos.le _
      have hcomb : w ^ (-(3 : ℝ) / 4) * w ^ (-(1 : ℝ) / 2) = w ^ (-(5 : ℝ) / 4) := by
        rw [← Real.rpow_add hwpos]
        norm_num
      have hposf : 0 ≤ (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2) :=
        mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (quad_pos hγ w) _)) hb2
      rw [Real.norm_eq_abs, abs_of_nonneg hposf]
      calc (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2)
          ≤ ((1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * w ^ (-(3 : ℝ) / 4)) * w ^ (-(1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hb1 hb2
        _ = (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * (w ^ (-(3 : ℝ) / 4) * w ^ (-(1 : ℝ) / 2)) := by
              ring
        _ = (1 - γ ^ 2) ^ (-(3 : ℝ) / 8) * w ^ (-(5 : ℝ) / 4) := by rw [hcomb]
  -- Glue: `(0,1] ∪ (1,∞) = (0,∞)`.
  have hAB : IntegrableOn
      (fun w : ℝ => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2))
      (Set.Ioc 0 1 ∪ Set.Ioi 1) := hA.union hB
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext w
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · linarith
    · intro h
      by_cases hw : w ≤ 1
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr (lt_of_not_ge hw)
  rw [hunion] at hAB
  exact hAB

end Work.FIArea2.SevenSix
