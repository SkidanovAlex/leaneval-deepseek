import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory intervalIntegral Set

namespace Commons.Analysis.Convolution

/-- The integral `∫₀^∞ t^(n-1) (max 1 t)^(-A')` for `1 ≤ n` and `A' > n`, split at `t = 1`. -/
theorem integral_Ioi_rpow_max_one (n : ℕ) (hn : 1 ≤ n) (A' : ℝ) (hA' : (n : ℝ) < A') :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (n - 1) * (max 1 t) ^ (-A')
      = 1 / (n : ℝ) + 1 / (A' - (n : ℝ)) := by
  set f : ℝ → ℝ := fun t => t ^ (n - 1) * (max 1 t) ^ (-A') with hf
  set c : ℝ := ((n : ℝ) - 1) - A' with hc
  have hc_lt : c < -1 := by rw [hc]; have := hA'; linarith
  have hfcont : Continuous f := by
    rw [hf]
    refine Continuous.mul (continuous_id.pow (n - 1)) ?_
    exact ((continuous_const (y := (1:ℝ))).max continuous_id).rpow_const
      (fun t => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1:ℝ) t))))
  have hpt : ∀ t ∈ Set.Ioi (1 : ℝ), f t = t ^ c := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    simp only [hf]
    rw [max_eq_right ht1, hc, ← Real.rpow_natCast t (n - 1),
      ← Real.rpow_add ht0 (((n - 1 : ℕ) : ℝ)) (-A')]
    congr 1
    rw [Nat.cast_sub hn]
    ring
  have htail_int : IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_rpow_of_lt hc_lt (by norm_num : (0:ℝ) < 1)).congr_fun ?_ measurableSet_Ioi
    intro t ht
    exact (hpt t ht).symm
  have h01 : ∫ t in (0:ℝ)..1, f t = 1 / (n : ℝ) := by
    have hcong : EqOn f (fun t : ℝ => t ^ (n - 1)) (uIcc (0:ℝ) 1) := by
      intro t ht
      have ht1 : t ≤ 1 := by
        have h := ht.2
        rwa [max_eq_right (show (0:ℝ) ≤ 1 by norm_num)] at h
      simp only [hf, max_eq_left ht1, Real.one_rpow, mul_one]
    rw [intervalIntegral.integral_congr hcong, integral_pow]
    have h1 : (1 : ℝ) ^ ((n - 1) + 1) = 1 := by rw [Nat.sub_add_cancel hn, one_pow]
    have h0 : (0 : ℝ) ^ ((n - 1) + 1) = 0 := by
      rw [Nat.sub_add_cancel hn]
      exact zero_pow (by omega : n ≠ 0)
    rw [h1, h0, sub_zero]
    have hden : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by rw [Nat.cast_sub hn]; ring
    rw [hden]
  have htail : ∫ t in Set.Ioi (1 : ℝ), f t = 1 / (A' - (n : ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)]
    rw [integral_Ioi_rpow_of_lt hc_lt (by norm_num : (0:ℝ) < 1)]
    have hc1 : c + 1 = (n : ℝ) - A' := by rw [hc]; ring
    rw [hc1, Real.one_rpow,
      show A' - (n : ℝ) = -((n : ℝ) - A') by ring, one_div_neg_eq_neg_one_div, neg_div]
  have hsplit : ∫ t in Set.Ioi (0:ℝ), f t
      = (∫ t in (0:ℝ)..1, f t) + ∫ t in Set.Ioi (1:ℝ), f t := by
    rw [← integral_interval_add_Ioi' (hfcont.intervalIntegrable 0 1) htail_int]
  rw [hsplit, h01, htail]

end Commons.Analysis.Convolution