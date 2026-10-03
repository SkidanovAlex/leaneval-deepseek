import Mathlib
import Submission.Work.FIArea6Road.integral_Ioi_one_div_sq
import Submission.Work.FIArea6Road.integral_Ioi_log_pow_six_div_sq

namespace Work.FIArea6Road

open MeasureTheory Filter
open scoped Pointwise

/-- Elementary bound: `(a+b)^6 ≤ 64 (a^6+b^6)` for nonnegative `a,b`. -/
lemma add_pow_six_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b)^6 ≤ 64 * (a^6 + b^6) := by
  have hmax : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  calc (a + b)^6 ≤ (2 * max a b)^6 := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ a + b) hmax 6
    _ = 64 * (max a b)^6 := by ring
    _ ≤ 64 * (a^6 + b^6) := by
        have hm : (max a b)^6 ≤ a^6 + b^6 := by
          rcases le_total a b with h | h
          · rw [max_eq_right h]; nlinarith [pow_nonneg ha 6]
          · rw [max_eq_left h]; nlinarith [pow_nonneg hb 6]
        linarith

/-- Pointwise bound for the substituted integrand on `s > 1`. -/
lemma pointwise_bound (θ T c s : ℝ) (hθ : 0 < θ) (hT1 : 1 ≤ T) (hc1 : 1 ≤ c) (hcT : c ≤ T)
    (hs : 1 ≤ s) :
    (1 + (θ * (T*s)) ^ 2)⁻¹ * (Real.log (T*s + c)) ^ (6:ℕ)
      ≤ 64 * ((Real.log (2*T))^6 + (Real.log s)^6) / (θ^2 * T^2 * s^2) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hTs1 : 1 ≤ T*s := one_le_mul_of_one_le_of_one_le hT1 hs
  have h1 : (1 + (θ * (T*s))^2)⁻¹ ≤ (θ^2 * T^2 * s^2)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (θ*(T*s))]
  have h2 : (Real.log (T*s+c))^6 ≤ 64 * ((Real.log (2*T))^6 + (Real.log s)^6) := by
    have hle1 : T*s + c ≤ 2*T*s := by nlinarith [hcT, hTs1]
    have hlog_le : Real.log (T*s+c) ≤ Real.log (2*T) + Real.log s := by
      have h1 : Real.log (T*s+c) ≤ Real.log (2*T*s) := Real.log_le_log (by linarith) hle1
      have h2 : Real.log (2*T*s) = Real.log (2*T) + Real.log s := by
        rw [show (2:ℝ)*T*s = (2*T)*s by ring, Real.log_mul (by positivity) (by positivity)]
      linarith [h1, h2]
    have hlog0 : 0 ≤ Real.log (T*s + c) := Real.log_nonneg (by linarith)
    have hpow : (Real.log (T*s+c))^6 ≤ (Real.log (2*T) + Real.log s)^6 :=
      pow_le_pow_left₀ hlog0 hlog_le 6
    have hb := add_pow_six_le (Real.log (2*T)) (Real.log s) (Real.log_nonneg (by linarith))
      (Real.log_nonneg hs)
    linarith [hpow, hb]
  calc (1 + (θ * (T*s)) ^ 2)⁻¹ * (Real.log (T*s + c)) ^ (6:ℕ)
      ≤ (θ^2 * T^2 * s^2)⁻¹ * (64 * ((Real.log (2*T))^6 + (Real.log s)^6)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 64 * ((Real.log (2*T))^6 + (Real.log s)^6) / (θ^2 * T^2 * s^2) := by
        rw [div_eq_inv_mul]

theorem integral_Ioi_inv_sq_log_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (θ T c : ℝ), 0 < θ → 1 ≤ c → c ≤ T → 1 ≤ T →
        ∫ y in Set.Ioi T, (1 + (θ * y) ^ 2)⁻¹ * (Real.log (y + c)) ^ (6 : ℕ)
          ≤ K / (θ ^ 2 * T) * (1 + (Real.log (2 * T)) ^ (6 : ℕ)) := by
  refine ⟨46144, by norm_num, ?_⟩
  intro θ T c hθ hc1 hcT hT1
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
  set A := 64 * (Real.log (2*T))^6 / (θ^2*T^2) with hA
  set B := 64 / (θ^2*T^2) with hB
  -- change of variables y = T * s
  have hcv : ∫ y in Set.Ioi T, (1 + (θ * y) ^ 2)⁻¹ * (Real.log (y + c)) ^ (6:ℕ)
      = T * ∫ s in Set.Ioi 1, (1 + (θ * (T*s)) ^ 2)⁻¹ * (Real.log (T*s + c)) ^ (6:ℕ) := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi'
      (fun y : ℝ => (1 + (θ * y) ^ 2)⁻¹ * (Real.log (y + c)) ^ (6:ℕ)) 1 hTpos
    simp only [mul_one, smul_eq_mul] at h
    rw [h]
  -- pointwise bound
  have hpt : ∀ s ∈ Set.Ioi (1:ℝ),
      (1 + (θ * (T*s)) ^ 2)⁻¹ * (Real.log (T*s + c)) ^ (6:ℕ)
        ≤ A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2) := by
    intro s hs
    rw [Set.mem_Ioi] at hs
    have hb := pointwise_bound θ T c s hθ hT1 hc1 hcT (le_of_lt hs)
    have heq : 64 * ((Real.log (2*T))^6 + (Real.log s)^6) / (θ^2 * T^2 * s^2)
        = A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2) := by
      rw [hA, hB]
      field_simp
    linarith [hb, heq.le]
  -- monotonicity of the integral
  have hIntbnd : IntegrableOn (fun s : ℝ => A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2))
      (Set.Ioi 1) := (hint_sq.const_mul A).add (hint_log.const_mul B)
  have hmono : ∫ s in Set.Ioi 1, (1 + (θ * (T*s)) ^ 2)⁻¹ * (Real.log (T*s + c)) ^ (6:ℕ)
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
  have hfinal : T * (A * 1 + B * 720) ≤ 46144 / (θ^2 * T) * (1 + (Real.log (2*T))^6) := by
    rw [hA, hB]
    have ha : (0:ℝ) ≤ (Real.log (2*T))^6 :=
      pow_nonneg (Real.log_nonneg (by linarith)) 6
    have hkey : 64 * (Real.log (2*T))^6 + 46080 ≤ 46144 * (1 + (Real.log (2*T))^6) := by
      nlinarith [ha]
    have h1 : (64 * (Real.log (2*T))^6 / (θ^2*T^2) * 1 + 64/(θ^2*T^2)*720)
        = (64 * (Real.log (2*T))^6 + 46080)/(θ^2*T^2) := by
      field_simp; ring
    have h2 : T * ((64 * (Real.log (2*T))^6 + 46080)/(θ^2*T^2))
        = (64 * (Real.log (2*T))^6 + 46080)/(θ^2*T) := by
      field_simp
    rw [h1, h2, div_mul_eq_mul_div]
    rw [div_le_div_iff_of_pos_right hθT]
    linarith [hkey]
  calc ∫ y in Set.Ioi T, (1 + (θ * y) ^ 2)⁻¹ * (Real.log (y + c)) ^ (6:ℕ)
      = T * ∫ s in Set.Ioi 1, (1 + (θ * (T*s)) ^ 2)⁻¹ * (Real.log (T*s + c)) ^ (6:ℕ) := hcv
    _ ≤ T * ∫ s in Set.Ioi 1, (A * (s^2)⁻¹ + B * ((Real.log s)^6/s^2)) :=
        mul_le_mul_of_nonneg_left hmono hTpos.le
    _ = T * (A * 1 + B * 720) := by rw [hbndval]
    _ ≤ 46144 / (θ^2 * T) * (1 + (Real.log (2*T))^6) := hfinal

end Work.FIArea6Road
