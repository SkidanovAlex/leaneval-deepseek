import Mathlib
import Submission.Work.FIArea6Road.integral_Ioi_inv_sq_log_le

namespace Work.FIArea6Road

open MeasureTheory Filter
open scoped Pointwise

/-- Pointwise bound for the substituted integrand on `s > 1`, with the extra additive
shift `L ≥ 0` in the logarithm. This is the `L`-generalisation of
`Work.FIArea6Road.pointwise_bound`. -/
lemma pointwise_bound_shift (θ T L c s : ℝ) (hθ : 0 < θ) (hT1 : 1 ≤ T) (hc1 : 1 ≤ c)
    (hcT : c ≤ T) (hL : 0 ≤ L) (hs : 1 ≤ s) :
    (1 + (θ * (T*s)) ^ 2)⁻¹ * (L + Real.log (T*s + c)) ^ (6:ℕ)
      ≤ 64 * ((L + Real.log (2*T))^6 + (Real.log s)^6) / (θ^2 * T^2 * s^2) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hTs1 : 1 ≤ T*s := one_le_mul_of_one_le_of_one_le hT1 hs
  have h1 : (1 + (θ * (T*s))^2)⁻¹ ≤ (θ^2 * T^2 * s^2)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (θ*(T*s))]
  have h2 : (L + Real.log (T*s+c))^6 ≤ 64 * ((L + Real.log (2*T))^6 + (Real.log s)^6) := by
    have hle1 : T*s + c ≤ 2*T*s := by nlinarith [hcT, hTs1]
    have hlog_le : Real.log (T*s+c) ≤ Real.log (2*T) + Real.log s := by
      have hA : Real.log (T*s+c) ≤ Real.log (2*T*s) := Real.log_le_log (by linarith) hle1
      have hB : Real.log (2*T*s) = Real.log (2*T) + Real.log s := by
        rw [show (2:ℝ)*T*s = (2*T)*s by ring, Real.log_mul (by positivity) (by positivity)]
      linarith [hA, hB]
    have harg0 : 0 ≤ L + Real.log (T*s + c) := by
      have : 0 ≤ Real.log (T*s + c) := Real.log_nonneg (by linarith)
      linarith
    have harg : L + Real.log (T*s+c) ≤ (L + Real.log (2*T)) + Real.log s := by linarith
    have hpow : (L + Real.log (T*s+c))^6 ≤ ((L + Real.log (2*T)) + Real.log s)^6 :=
      pow_le_pow_left₀ harg0 harg 6
    have ha0 : 0 ≤ L + Real.log (2*T) := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2*T); linarith
    have hb := add_pow_six_le (L + Real.log (2*T)) (Real.log s) ha0 (Real.log_nonneg hs)
    linarith [hpow, hb]
  calc (1 + (θ * (T*s)) ^ 2)⁻¹ * (L + Real.log (T*s + c)) ^ (6:ℕ)
      ≤ (θ^2 * T^2 * s^2)⁻¹ * (64 * ((L + Real.log (2*T))^6 + (Real.log s)^6)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 64 * ((L + Real.log (2*T))^6 + (Real.log s)^6) / (θ^2 * T^2 * s^2) := by
        rw [div_eq_inv_mul]

theorem HeartFarIntegral :
    ∃ K : ℝ, 0 < K ∧
      ∀ (θ T L c : ℝ), 0 < θ → 1 ≤ c → c ≤ T → 1 ≤ T → 0 ≤ L →
        (∫ t in Set.Ioi T, (1 + (θ * t) ^ 2)⁻¹ * (L + Real.log (t + c)) ^ (6 : ℕ))
          ≤ K / (θ ^ 2 * T) * (L + Real.log (2 * T) + 1) ^ (6 : ℕ) := by
  refine ⟨46144, by norm_num, ?_⟩
  intro θ T L c hθ hc1 hcT hT1 hL
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hθT : 0 < θ^2 * T := by positivity
  -- values of the two model integrals (delegated lemmas)
  have hval_sq : ∫ s in Set.Ioi (1:ℝ), ((s:ℝ)^2)⁻¹ = 1 := integral_Ioi_one_div_sq
  have hval_log : ∫ s in Set.Ioi (1:ℝ), (Real.log s)^6/s^2 = 720 := integral_Ioi_log_pow_six_div_sq
  -- integrability, obtained from the non-vanishing of the integrals
  have hint_sq : IntegrableOn (fun s : ℝ => (s^2)⁻¹) (Set.Ioi 1) := by
    by_contra h
    have hh := MeasureTheory.integral_undef h
    rw [hh] at hval_sq; norm_num at hval_sq
  have hint_log : IntegrableOn (fun s : ℝ => (Real.log s)^6/s^2) (Set.Ioi 1) := by
    by_contra h
    have hh := MeasureTheory.integral_undef h
    rw [hh] at hval_log; norm_num at hval_log
  set A := 64 * (L + Real.log (2*T))^6 / (θ^2*T^2) with hA
  set B := 64 / (θ^2*T^2) with hB
  -- change of variables y = T * s
  have hcv : ∫ y in Set.Ioi T, (1 + (θ * y) ^ 2)⁻¹ * (L + Real.log (y + c)) ^ (6:ℕ)
      = T * ∫ s in Set.Ioi 1, (1 + (θ * (T*s)) ^ 2)⁻¹ * (L + Real.log (T*s + c)) ^ (6:ℕ) := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi'
      (fun y : ℝ => (1 + (θ * y) ^ 2)⁻¹ * (L + Real.log (y + c)) ^ (6:ℕ)) 1 hTpos
    simp only [mul_one, smul_eq_mul] at h
    rw [h]
  -- pointwise bound
  have hpt : ∀ s ∈ Set.Ioi (1:ℝ),
      (1 + (θ * (T*s)) ^ 2)⁻¹ * (L + Real.log (T*s + c)) ^ (6:ℕ)
        ≤ A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2) := by
    intro s hs
    rw [Set.mem_Ioi] at hs
    have hb := pointwise_bound_shift θ T L c s hθ hT1 hc1 hcT hL (le_of_lt hs)
    have heq : 64 * ((L + Real.log (2*T))^6 + (Real.log s)^6) / (θ^2 * T^2 * s^2)
        = A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2) := by
      rw [hA, hB]
      field_simp
    linarith [hb, heq.le]
  -- monotonicity of the integral
  have hIntbnd : IntegrableOn (fun s : ℝ => A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2))
      (Set.Ioi 1) := (hint_sq.const_mul A).add (hint_log.const_mul B)
  have hmono : ∫ s in Set.Ioi 1, (1 + (θ * (T*s)) ^ 2)⁻¹ * (L + Real.log (T*s + c)) ^ (6:ℕ)
      ≤ ∫ s in Set.Ioi 1, (A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun s => by positivity)
    · exact hIntbnd
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact hpt s hs
  -- value of the bound integral
  have hbndval : ∫ s in Set.Ioi 1, (A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2))
      = A * 1 + B * 720 := by
    rw [integral_add]
    · rw [integral_const_mul, integral_const_mul, hval_sq, hval_log]
    · exact hint_sq.const_mul A
    · exact hint_log.const_mul B
  -- final arithmetic
  have hfinal : T * (A * 1 + B * 720) ≤ 46144 / (θ^2 * T) * (L + Real.log (2*T) + 1)^6 := by
    rw [hA, hB]
    have ha0 : 0 ≤ L + Real.log (2*T) := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2*T); linarith
    have hkey : 64 * (L + Real.log (2*T))^6 + 46080
        ≤ 46144 * (L + Real.log (2*T) + 1)^6 := by
      have h1 : (L + Real.log (2*T))^6 ≤ (L + Real.log (2*T) + 1)^6 :=
        pow_le_pow_left₀ ha0 (by linarith) 6
      have h2 : (1:ℝ) ≤ (L + Real.log (2*T) + 1)^6 := by
        calc (1:ℝ) = 1^6 := by norm_num
          _ ≤ (L + Real.log (2*T) + 1)^6 :=
              pow_le_pow_left₀ (by norm_num) (by linarith) 6
      nlinarith [h1, h2]
    have h1 : (64 * (L + Real.log (2*T))^6 / (θ^2*T^2) * 1 + 64/(θ^2*T^2)*720)
        = (64 * (L + Real.log (2*T))^6 + 46080)/(θ^2*T^2) := by
      field_simp; ring
    have h2 : T * ((64 * (L + Real.log (2*T))^6 + 46080)/(θ^2*T^2))
        = (64 * (L + Real.log (2*T))^6 + 46080)/(θ^2*T) := by
      field_simp
    rw [h1, h2, div_mul_eq_mul_div]
    rw [div_le_div_iff_of_pos_right hθT]
    linarith [hkey]
  calc ∫ y in Set.Ioi T, (1 + (θ * y) ^ 2)⁻¹ * (L + Real.log (y + c)) ^ (6:ℕ)
      = T * ∫ s in Set.Ioi 1, (1 + (θ * (T*s)) ^ 2)⁻¹ * (L + Real.log (T*s + c)) ^ (6:ℕ) := hcv
    _ ≤ T * ∫ s in Set.Ioi 1, (A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2)) :=
        mul_le_mul_of_nonneg_left hmono hTpos.le
    _ = T * (A * 1 + B * 720) := by rw [hbndval]
    _ ≤ 46144 / (θ^2 * T) * (L + Real.log (2*T) + 1)^6 := hfinal

end Work.FIArea6Road
