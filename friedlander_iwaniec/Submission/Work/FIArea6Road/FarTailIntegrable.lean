import Mathlib

namespace Work.FIArea6Road

open MeasureTheory

/-- `(a + b)^6 ≤ 64 * (a^6 + b^6)` for nonnegative `a`, `b`. -/
private lemma add_pow_six_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 6 ≤ 64 * (a ^ 6 + b ^ 6) := by
  have hmax : a + b ≤ 2 * max a b := by
    have h1 := le_max_left a b
    have h2 := le_max_right a b
    linarith
  have h64 : (2 * max a b) ^ 6 = 64 * (max a b) ^ 6 := by ring
  have hm : (max a b) ^ 6 ≤ a ^ 6 + b ^ 6 := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      nlinarith [pow_nonneg ha 6, pow_nonneg hb 6]
    · rw [max_eq_left h]
      nlinarith [pow_nonneg ha 6, pow_nonneg hb 6]
  calc (a + b) ^ 6 ≤ (2 * max a b) ^ 6 := pow_le_pow_left₀ (by linarith) hmax 6
    _ = 64 * (max a b) ^ 6 := h64
    _ ≤ 64 * (a ^ 6 + b ^ 6) := by linarith

/-- For `t ≥ 1`, `log (1 + t) ≤ 12 * 2^(1/12) * t^(1/12)`: the elementary bound
`log x ≤ x^ε / ε` with `ε = 1/12`. -/
private lemma log_one_add_le (t : ℝ) (ht : 1 ≤ t) :
    Real.log (1 + t) ≤ 12 * (2:ℝ) ^ (1/12:ℝ) * t ^ (1/12:ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h1 : Real.log (1 + t) ≤ (1 + t) ^ (1/12:ℝ) / (1/12:ℝ) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h2 : (1 + t) ^ (1/12:ℝ) / (1/12:ℝ) = 12 * (1 + t) ^ (1/12:ℝ) := by
    rw [div_eq_mul_inv, show ((1:ℝ)/12)⁻¹ = 12 by norm_num, mul_comm]
  have h3 : (1 + t) ^ (1/12:ℝ) ≤ (2 * t) ^ (1/12:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h4 : (2 * t) ^ (1/12:ℝ) = (2:ℝ) ^ (1/12:ℝ) * t ^ (1/12:ℝ) :=
    Real.mul_rpow (by norm_num) (le_of_lt ht0)
  calc Real.log (1 + t) ≤ (1 + t) ^ (1/12:ℝ) / (1/12:ℝ) := h1
    _ = 12 * (1 + t) ^ (1/12:ℝ) := h2
    _ ≤ 12 * (2 * t) ^ (1/12:ℝ) := by linarith
    _ = 12 * ((2:ℝ) ^ (1/12:ℝ) * t ^ (1/12:ℝ)) := by rw [h4]
    _ = 12 * (2:ℝ) ^ (1/12:ℝ) * t ^ (1/12:ℝ) := by ring

/-- For `t ≥ 1`, `(M + log (1 + t))^6 ≤ 64 * (M^6 + (12 * 2^(1/12))^6) * t^(1/2)`. -/
private lemma log_pow_six_le (M t : ℝ) (hM : 0 ≤ M) (ht : 1 ≤ t) :
    (M + Real.log (1 + t)) ^ 6 ≤
      64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) * t ^ (1/2:ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hlog0 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hlog := log_one_add_le t ht
  have hEq : (t ^ (1/12:ℝ)) ^ (6:ℕ) = t ^ (1/2:ℝ) := by
    rw [← Real.rpow_natCast (t ^ (1/12:ℝ)) 6, ← Real.rpow_mul (le_of_lt ht0),
        show (1/12:ℝ) * ((6:ℕ):ℝ) = 1/2 by norm_num]
  have hA : (Real.log (1 + t)) ^ 6 ≤ (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6 * t ^ (1/2:ℝ) := by
    have h1 : (Real.log (1 + t)) ^ 6 ≤ (12 * (2:ℝ) ^ (1/12:ℝ) * t ^ (1/12:ℝ)) ^ 6 :=
      pow_le_pow_left₀ hlog0 hlog 6
    have h2 : (12 * (2:ℝ) ^ (1/12:ℝ) * t ^ (1/12:ℝ)) ^ 6
        = (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6 * t ^ (1/2:ℝ) := by
      rw [mul_pow, hEq]
    linarith [h1, h2.le, h2.ge]
  have hM6 : M ^ 6 ≤ M ^ 6 * t ^ (1/2:ℝ) := by
    have h1 : (1:ℝ) ≤ t ^ (1/2:ℝ) := Real.one_le_rpow ht (by norm_num)
    nlinarith [pow_nonneg hM 6]
  have hB := add_pow_six_le M (Real.log (1 + t)) hM hlog0
  calc (M + Real.log (1 + t)) ^ 6
      ≤ 64 * (M ^ 6 + (Real.log (1 + t)) ^ 6) := hB
    _ ≤ 64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6 * t ^ (1/2:ℝ)) := by linarith [hA]
    _ ≤ 64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) * t ^ (1/2:ℝ) := by nlinarith [hM6]

/-- Pointwise domination on the tail `t ≥ 1` by the integrable model function
`(64 * (M^6 + (12 * 2^(1/12))^6) / θ) * t^(-3/2)`. -/
private lemma pointwise_bound (θ M t : ℝ) (hθ : 0 < θ) (hM : 0 ≤ M) (ht : 1 ≤ t) :
    θ * (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + t)) ^ 6
      ≤ (64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) / θ) * t ^ (-(3/2) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hinv : (1 + (θ * t) ^ 2)⁻¹ ≤ (θ ^ 2 * t ^ 2)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (θ * t)]
  have hpow := log_pow_six_le M t hM ht
  have hB0 : 0 ≤ (M + Real.log (1 + t)) ^ 6 := by
    apply pow_nonneg
    have := Real.log_nonneg (show (1:ℝ) ≤ 1 + t by linarith)
    linarith
  have hA0 : 0 ≤ θ * (θ ^ 2 * t ^ 2)⁻¹ := by positivity
  have hEq : θ * (θ ^ 2 * t ^ 2)⁻¹ * (64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) * t ^ (1/2:ℝ))
      = (64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) / θ) * t ^ (-(3/2) : ℝ) := by
    have hkey : t ^ (-(3/2) : ℝ) = t ^ (1/2:ℝ) / t ^ 2 := by
      rw [show (-(3/2):ℝ) = 1/2 - 2 by norm_num, Real.rpow_sub ht0, Real.rpow_two]
    rw [hkey]
    field_simp
  calc θ * (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + t)) ^ 6
      ≤ θ * (θ ^ 2 * t ^ 2)⁻¹ * (M + Real.log (1 + t)) ^ 6 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hθ.le) hB0
    _ ≤ θ * (θ ^ 2 * t ^ 2)⁻¹ * (64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) * t ^ (1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hA0
    _ = (64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) / θ) * t ^ (-(3/2) : ℝ) := hEq

theorem FarTailIntegrable (θ T M : ℝ) (hθ : 0 < θ) (hT : 1 ≤ T) (hM : 0 ≤ M) :
    MeasureTheory.IntegrableOn (fun t : ℝ => θ * (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + |t|)) ^ 6)
      (Set.Ioi T ∪ Set.Iio (-T) : Set ℝ) := by
  set F : ℝ → ℝ := fun t => θ * (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + |t|)) ^ 6 with hF
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => (64 * (M ^ 6 + (12 * (2:ℝ) ^ (1/12:ℝ)) ^ 6) / θ) * t ^ (-(3/2) : ℝ))
      (Set.Ioi T) :=
    MeasureTheory.Integrable.const_mul
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ)) < -1) hTpos) _
  have hmeasF : MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict (Set.Ioi T)) := by
    rw [hF]
    exact (by measurability : Measurable
      (fun t : ℝ => θ * (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + |t|)) ^ 6)).aestronglyMeasurable
  have h1 : MeasureTheory.IntegrableOn F (Set.Ioi T) := by
    refine MeasureTheory.Integrable.mono' hmaj hmeasF ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [hF]
    have htT : T ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    have ht1 : 1 ≤ t := le_trans hT htT
    have habs : |t| = t := abs_of_pos (lt_of_lt_of_le one_pos ht1)
    rw [habs, Real.norm_eq_abs]
    have hnonneg : 0 ≤ θ * (1 + (θ * t) ^ 2)⁻¹ * (M + Real.log (1 + t)) ^ 6 := by
      have h2 : 0 ≤ (M + Real.log (1 + t)) ^ 6 := by
        apply pow_nonneg
        have := Real.log_nonneg (show (1:ℝ) ≤ 1 + t by linarith)
        linarith
      have h1 : 0 ≤ (1 + (θ * t) ^ 2)⁻¹ := by positivity
      exact mul_nonneg (mul_nonneg hθ.le h1) h2
    rw [abs_of_nonneg hnonneg]
    exact pointwise_bound θ M t hθ hM ht1
  have h2 : MeasureTheory.IntegrableOn F (Set.Iio (-T)) := by
    have hh : MeasureTheory.IntegrableOn F (Set.Ioi (-(-T))) := by simpa using h1
    have hcomp : MeasureTheory.IntegrableOn (fun x : ℝ => F (-x)) (Set.Iio (-T)) :=
      hh.comp_neg_Iio (c := -T)
    convert hcomp using 1
    funext x
    rw [hF]
    simp only [abs_neg]
    rw [show (θ * (-x)) ^ 2 = (θ * x) ^ 2 by ring]
  exact (integrableOn_union).mpr ⟨h1, h2⟩

end Work.FIArea6Road
