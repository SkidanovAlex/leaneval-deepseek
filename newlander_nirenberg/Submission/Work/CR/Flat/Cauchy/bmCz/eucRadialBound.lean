import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

noncomputable section

namespace Work.CR.Flat.Cauchy.bmCz

open MeasureTheory Set
open scoped NNReal ENNReal

/-! ## Auxiliary estimates for the Euclidean norm on `ℂⁿ` -/

lemma measurable_eucNorm_rpow {n : ℕ} (s : ℝ) :
    Measurable (fun x : Fin n → ℂ => eucNorm x ^ s) :=
  (show Measurable (fun y : ℝ => y ^ s) by measurability).comp continuous_eucNorm.measurable

lemma eucNorm_le_sqrt_mul_norm {n : ℕ} (x : Fin n → ℂ) :
    eucNorm x ≤ Real.sqrt n * ‖x‖ := by
  have h1 : eucNorm x ^ 2 ≤ (Real.sqrt n * ‖x‖) ^ 2 := by
    rw [eucNorm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    calc ∑ j, ‖x j‖ ^ 2 ≤ ∑ _j : Fin n, ‖x‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x j) 2
      _ = n * ‖x‖ ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : 0 ≤ Real.sqrt n * ‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [← Real.sqrt_sq (eucNorm_nonneg x), ← Real.sqrt_sq h2]
  exact Real.sqrt_le_sqrt h1

lemma eucNorm_rpow_le {n : ℕ} (s : ℝ) (x : Fin n → ℂ) :
    eucNorm x ^ s ≤ ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s := by
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hxn : 0 ≤ ‖x‖ := norm_nonneg x
  rcases le_or_gt 0 s with hs | hs
  · calc eucNorm x ^ s ≤ (Real.sqrt n * ‖x‖) ^ s :=
          Real.rpow_le_rpow (eucNorm_nonneg x) (eucNorm_le_sqrt_mul_norm x) hs
      _ = (Real.sqrt n) ^ s * ‖x‖ ^ s := Real.mul_rpow hsn hxn
      _ ≤ ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg hxn s)
  · have hrp : 0 ≤ ‖x‖ ^ s := Real.rpow_nonneg hxn s
    refine le_trans ?_ (le_mul_of_one_le_left hrp (by linarith [Real.rpow_nonneg hsn s]))
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hs.ne]
    · exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hx) (pi_norm_le_eucNorm x) hs.le

/-! ## The radial integral of a power of the ambient norm -/

lemma integral_norm_rpow_ball {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : -(2 * (n : ℝ)) < s)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ x in Metric.ball (0 : Fin n → ℂ) ρ, ‖x‖ ^ s
      = (Module.finrank ℝ (Fin n → ℂ) : ℝ)
          * (volume : Measure (Fin n → ℂ)).real (Metric.ball (0 : Fin n → ℂ) 1)
          * (ρ ^ (s + (Module.finrank ℝ (Fin n → ℂ) : ℝ))
              / (s + (Module.finrank ℝ (Fin n → ℂ) : ℝ))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hD1 : 1 ≤ Module.finrank ℝ (Fin n → ℂ) := Nat.succ_le_of_lt Module.finrank_pos
  have hspos : 0 < s + (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    have hfin : (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hfin]; linarith
  have hball : ∫ x in Metric.ball (0 : Fin n → ℂ) ρ, ‖x‖ ^ s
      = ∫ x : Fin n → ℂ, (Set.Iio ρ).indicator (fun y : ℝ => y ^ s) ‖x‖ := by
    classical
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator_apply, Set.mem_Iio, Metric.mem_ball, dist_zero_right]
  rw [hball, integral_fun_norm_addHaar (volume : Measure (Fin n → ℂ))
      ((Set.Iio ρ).indicator (fun y : ℝ => y ^ s))]
  have hint : ∫ y in Set.Ioi (0:ℝ),
        y ^ (Module.finrank ℝ (Fin n → ℂ) - 1) • (Set.Iio ρ).indicator (fun y : ℝ => y ^ s) y
      = ρ ^ (s + (Module.finrank ℝ (Fin n → ℂ) : ℝ))
          / (s + (Module.finrank ℝ (Fin n → ℂ) : ℝ)) := by
    have hDge : ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) + 1
        = (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hD1 :
        Module.finrank ℝ (Fin n → ℂ) - 1 + 1 = Module.finrank ℝ (Fin n → ℂ))
    have hr : -1 < s + ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) := by
      linarith only [hDge, hspos]
    have hcongr : Set.EqOn
        (fun y : ℝ => y ^ (Module.finrank ℝ (Fin n → ℂ) - 1)
            • (Set.Iio ρ).indicator (fun y : ℝ => y ^ s) y)
        ((Set.Ioo (0:ℝ) ρ).indicator
            (fun y : ℝ => y ^ (s + ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ))))
        (Set.Ioi 0) := by
      intro y hy
      have hy0 : 0 < y := hy
      simp only [smul_eq_mul]
      by_cases hyρ : y < ρ
      · rw [Set.indicator_of_mem (show y ∈ Set.Iio ρ from hyρ),
            Set.indicator_of_mem (show y ∈ Set.Ioo (0:ℝ) ρ from ⟨hy0, hyρ⟩),
            ← Real.rpow_natCast y (Module.finrank ℝ (Fin n → ℂ) - 1),
            ← Real.rpow_add hy0, add_comm]
      · rw [Set.indicator_of_notMem (show y ∉ Set.Iio ρ from hyρ),
            Set.indicator_of_notMem (show y ∉ Set.Ioo (0:ℝ) ρ from fun h => hyρ h.2),
            mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self,
      setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le hρ.le,
      integral_rpow (Or.inl hr)]
    rw [Real.zero_rpow
      (ne_of_gt (by linarith only [hDge, hspos] :
        (0:ℝ) < s + ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) + 1))]
    rw [show s + ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) + 1
          = s + (Module.finrank ℝ (Fin n → ℂ) : ℝ) from by rw [add_assoc, hDge]]
    ring
  rw [hint]
  rw [nsmul_eq_mul, smul_eq_mul]
  ring

/-! ## The main estimate -/

/-- For `s > -2n` the integral of `‖x‖^s` over the Euclidean ball of radius `ρ` is `O(ρ^{s+2n})`. -/
theorem eucRadialBound {n : ℕ} (hn : 0 < n) (s : ℝ) (hs : -(2 * (n : ℝ)) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
      ∫ x in Work.CR.Flat.Cauchy.eucBall (n := n) ρ, (Work.CR.Flat.Cauchy.eucNorm x) ^ s
        ≤ C * ρ ^ (s + 2 * (n : ℝ)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hspos : 0 < s + 2 * (n : ℝ) := by linarith
  have hfin : (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const, nsmul_eq_mul]
    ring
  have hFpos : (0:ℝ) < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hcpos : 0 < (volume : Measure (Fin n → ℂ)).real (Metric.ball (0 : Fin n → ℂ) 1) := by
    rw [Measure.real_def]
    exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
      (ne_of_lt MeasureTheory.measure_ball_lt_top)
  refine ⟨((Real.sqrt n) ^ s + 1) * ((Module.finrank ℝ (Fin n → ℂ) : ℝ)
      * (volume : Measure (Fin n → ℂ)).real (Metric.ball (0 : Fin n → ℂ) 1)
      / (s + 2 * (n : ℝ))), ?_, ?_⟩
  · exact mul_pos (by linarith [Real.rpow_nonneg (Real.sqrt_nonneg n) s])
      (div_pos (mul_pos hFpos hcpos) hspos)
  · intro ρ hρ
    have hIntNorm : IntegrableOn (fun x : Fin n → ℂ => ‖x‖ ^ s)
        (Metric.ball (0 : Fin n → ℂ) ρ) volume := by
      refine (integrableOn_fun_norm_addHaar (volume : Measure (Fin n → ℂ)) (r := ρ)
        (f := fun y : ℝ => y ^ s)).mpr ?_
      have hDge : ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) + 1
          = (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt Module.finrank_pos) :
          Module.finrank ℝ (Fin n → ℂ) - 1 + 1 = Module.finrank ℝ (Fin n → ℂ))
      have hr : -1 < s + ((Module.finrank ℝ (Fin n → ℂ) - 1 : ℕ) : ℝ) := by
        linarith only [hDge, hspos, hfin]
      refine ((intervalIntegral.integrableOn_Ioo_rpow_iff hρ).2 hr).congr_fun ?_
        measurableSet_Ioo
      intro y hy
      rw [Set.mem_Ioo] at hy
      simp only [smul_eq_mul]
      rw [← Real.rpow_natCast y (Module.finrank ℝ (Fin n → ℂ) - 1),
        ← Real.rpow_add hy.1, add_comm]
    have hIntK : IntegrableOn (fun x : Fin n → ℂ => ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s)
        (Metric.ball (0 : Fin n → ℂ) ρ) volume :=
      Integrable.const_mul hIntNorm _
    have hIntKe : IntegrableOn (fun x : Fin n → ℂ => ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s)
        (eucBall (n := n) ρ) volume :=
      IntegrableOn.mono_set hIntK eucBall_subset_ball
    have hIntE : IntegrableOn (fun x : Fin n → ℂ => eucNorm x ^ s)
        (eucBall (n := n) ρ) volume := by
      refine Integrable.mono' hIntKe (measurable_eucNorm_rpow s).aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (eucNorm_nonneg x) s)]
      exact eucNorm_rpow_le s x
    calc ∫ x in eucBall (n := n) ρ, eucNorm x ^ s
        ≤ ∫ x in eucBall (n := n) ρ, ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s :=
          setIntegral_mono_on hIntE hIntKe (measurableSet_eucBall ρ)
            (fun x _ => eucNorm_rpow_le s x)
      _ ≤ ∫ x in Metric.ball (0 : Fin n → ℂ) ρ, ((Real.sqrt n) ^ s + 1) * ‖x‖ ^ s :=
          setIntegral_mono_set hIntK
            (Filter.Eventually.of_forall fun x => by
              exact mul_nonneg (by linarith [Real.rpow_nonneg (Real.sqrt_nonneg n) s])
                (Real.rpow_nonneg (norm_nonneg x) s))
            (Filter.Eventually.of_forall fun x hx => eucBall_subset_ball hx)
      _ = ((Real.sqrt n) ^ s + 1)
            * ∫ x in Metric.ball (0 : Fin n → ℂ) ρ, ‖x‖ ^ s := by
          rw [integral_const_mul]
      _ = ((Real.sqrt n) ^ s + 1) * ((Module.finrank ℝ (Fin n → ℂ) : ℝ)
            * (volume : Measure (Fin n → ℂ)).real (Metric.ball (0 : Fin n → ℂ) 1)
            * (ρ ^ (s + (Module.finrank ℝ (Fin n → ℂ) : ℝ))
                / (s + (Module.finrank ℝ (Fin n → ℂ) : ℝ)))) := by
          rw [integral_norm_rpow_ball hn hs hρ]
      _ = ((Real.sqrt n) ^ s + 1) * ((Module.finrank ℝ (Fin n → ℂ) : ℝ)
            * (volume : Measure (Fin n → ℂ)).real (Metric.ball (0 : Fin n → ℂ) 1)
            / (s + 2 * (n : ℝ)))
            * ρ ^ (s + 2 * (n : ℝ)) := by
          rw [hfin]
          ring

end Work.CR.Flat.Cauchy.bmCz
