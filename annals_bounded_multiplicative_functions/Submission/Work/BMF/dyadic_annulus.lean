import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Work.BMF

/-- One dyadic annulus of the frequency tail, two-sided.  If `0 < R`, `0 ≤ S`, the function `F`
is nonnegative, measurable and bounded, and every `T ≥ R` satisfies
`(R/T) * ∫_{-(2T)}^{2T} F ≤ S`, then the annulus `2^k R < |t| ≤ 2^(k+1) R` contributes at most
`(1/2)^k * S`. -/
theorem dyadic_annulus (F : ℝ → ℝ) (hFnn : ∀ t, 0 ≤ F t) (hFmeas : Measurable F)
    (K : ℝ) (hK : ∀ t, F t ≤ K) (R S : ℝ) (hR : 0 < R) (hS : 0 ≤ S)
    (hsup : ∀ T : ℝ, R ≤ T → R / T * (∫ t in (-(2 * T))..(2 * T), F t) ≤ S) (k : ℕ) :
    (∫ t in (Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R))), F t * (R ^ 2 / t ^ 2))
      ≤ (1 / 2 : ℝ) ^ k * S := by
  rw [show (2:ℝ)^(k+1) * R = 2 * ((2:ℝ)^k * R) from by ring]
  set q : ℝ := (2:ℝ)^k * R with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have hRq : R ≤ q := by
    rw [hq]
    have h1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [hR, h1]
  have hsmeas : MeasurableSet (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)) :=
    measurableSet_Ioc.union measurableSet_Ico
  have hs_fin : volume (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)) < ⊤ :=
    lt_of_le_of_lt (measure_union_le _ _)
      (ENNReal.add_lt_top.mpr ⟨measure_Ioc_lt_top, measure_Ico_lt_top⟩)
  -- the annulus is contained in the outer interval up to the single missing endpoint `-(2*q)`
  have hsub_ae : (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)) ≤ᵐ[volume] Set.Ioc (-(2*q)) (2*q) := by
    rw [ae_le_set]
    apply measure_mono_null _ (Real.volume_singleton (a := -(2*q)))
    intro t ht
    obtain ⟨hts, htn⟩ := ht
    rw [Set.mem_singleton_iff]
    rcases hts with hts | hts
    · exfalso
      exact htn ⟨by linarith [hqpos, hts.1], hts.2⟩
    · by_contra hne
      exact htn ⟨lt_of_le_of_ne hts.1 (Ne.symm hne), by linarith [hqpos, hts.2]⟩
  -- pointwise bound `R^2 / t^2 ≤ (1/4)^k` on the annulus
  have hdiv_le : ∀ t ∈ (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), R^2/t^2 ≤ (1/4:ℝ)^k := by
    have h4 : (1/4:ℝ)^k * ((2:ℝ)^k)^2 = 1 := by
      have hh : ((2:ℝ)^k)^2 = (4:ℝ)^k := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      rw [hh, ← mul_pow]; norm_num
    intro t ht
    rcases ht with ht | ht
    · have hqt : (2:ℝ)^k * R < t := by rw [hq] at ht; exact ht.1
      have hu2 : 0 < t^2 := by nlinarith [sq_nonneg t]
      rw [div_le_iff₀ hu2]
      have hsq : ((2:ℝ)^k*R)^2 ≤ t^2 := by nlinarith
      nlinarith [hsq, h4]
    · have hqt : t < -((2:ℝ)^k * R) := by rw [hq] at ht; exact ht.2
      have hu2 : 0 < t^2 := by nlinarith [sq_nonneg t]
      rw [div_le_iff₀ hu2]
      have hsq : ((2:ℝ)^k*R)^2 ≤ t^2 := by nlinarith
      nlinarith [hsq, h4]
  have hpt : ∀ t ∈ (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)),
      F t * (R^2/t^2) ≤ (1/4:ℝ)^k * F t := by
    intro t ht
    calc F t * (R^2/t^2) ≤ F t * (1/4:ℝ)^k :=
          mul_le_mul_of_nonneg_left (hdiv_le t ht) (hFnn t)
      _ = (1/4:ℝ)^k * F t := by ring
  -- integrability
  have hIntF : IntegrableOn F (Set.Ioc (-(2*q)) (2*q)) volume :=
    IntegrableOn.of_bound measure_Ioc_lt_top hFmeas.aestronglyMeasurable.restrict K (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
      exact hK x)
  have hIntFs : IntegrableOn F (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)) volume :=
    IntegrableOn.of_bound hs_fin hFmeas.aestronglyMeasurable.restrict K (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
      exact hK x)
  have hIntg : IntegrableOn (fun t => F t * (R^2/t^2))
      (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)) volume := by
    refine IntegrableOn.of_bound hs_fin ?_ K ?_
    · exact (hFmeas.mul (by fun_prop : Measurable (fun t : ℝ => R^2/t^2))).aestronglyMeasurable.restrict
    · filter_upwards [MeasureTheory.ae_restrict_mem hsmeas] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnn x),
        abs_of_nonneg (div_nonneg (sq_nonneg R) (sq_nonneg x))]
      have hc1 : R^2/x^2 ≤ 1 :=
        le_trans (hdiv_le x hx) (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) ≤ 1))
      nlinarith [hK x, hFnn x, div_nonneg (sq_nonneg R) (sq_nonneg x), hc1]
  have hIntH : IntegrableOn (fun t => (1/4:ℝ)^k * F t)
      (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)) volume :=
    hIntFs.const_mul _
  -- step A: replace the weight `R^2/t^2` by the constant `(1/4)^k`
  have hA1 : ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t * (R^2/t^2)
      ≤ ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), (1/4:ℝ)^k * F t := by
    refine MeasureTheory.setIntegral_mono_ae_restrict hIntg hIntH ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hsmeas] with x hx
    exact hpt x hx
  have hA2 : ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), (1/4:ℝ)^k * F t
      = (1/4:ℝ)^k * ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t := by
    simp only [MeasureTheory.integral_const_mul]
  have hA : ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t * (R^2/t^2)
      ≤ (1/4:ℝ)^k * ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t := by
    rw [hA2] at hA1; exact hA1
  -- step B: enlarge the domain to the outer interval
  have hC : ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t
      ≤ ∫ t in Set.Ioc (-(2*q)) (2*q), F t :=
    MeasureTheory.setIntegral_mono_set hIntF (Filter.Eventually.of_forall hFnn) hsub_ae
  have hD : ∫ t in Set.Ioc (-(2*q)) (2*q), F t = ∫ t in (-(2*q))..(2*q), F t :=
    (intervalIntegral.integral_of_le (by linarith [hqpos] : -(2*q) ≤ 2*q)).symm
  -- step C: apply the hypothesis with `T = q`
  have hJ : ∫ t in (-(2*q))..(2*q), F t ≤ 2^k * S := by
    have h := hsup q hRq
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (by positivity : (0:ℝ) < q/R))
    have hL : (R/q * (∫ t in (-(2*q))..(2*q), F t)) * (q/R) = ∫ t in (-(2*q))..(2*q), F t := by
      field_simp
    have hRr : S * (q/R) = 2^k * S := by
      have hqr : q/R = (2:ℝ)^k := by rw [hq, mul_div_assoc, div_self (ne_of_gt hR), mul_one]
      rw [hqr, mul_comm]
    rw [hL, hRr] at hmul
    exact hmul
  calc ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t * (R^2/t^2)
      ≤ (1/4:ℝ)^k * ∫ t in (Set.Ioc q (2*q) ∪ Set.Ico (-(2*q)) (-q)), F t := hA
    _ ≤ (1/4:ℝ)^k * ∫ t in Set.Ioc (-(2*q)) (2*q), F t :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (1/4:ℝ)^k * ∫ t in (-(2*q))..(2*q), F t := by rw [hD]
    _ ≤ (1/4:ℝ)^k * (2^k * S) := mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (1/2:ℝ)^k * S := by rw [← mul_assoc, ← mul_pow]; norm_num

end Work.BMF
