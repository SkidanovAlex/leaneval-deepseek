import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotic

theorem rpow_four_thirds_mul_sqrt_div_sq {f : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hfpos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < f t)
    (hIn : Filter.Tendsto (fun t : ℝ => f t / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds κ)) :
    Filter.Tendsto (fun t : ℝ => t ^ ((4:ℝ)/3) * Real.sqrt (f t) / t ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt κ)) := by
  have _ := hκ
  have hcont : Filter.Tendsto (fun t : ℝ => Real.sqrt (f t / t ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt κ)) :=
    (Real.continuous_sqrt.continuousAt.tendsto).comp hIn
  refine Filter.Tendsto.congr' ?_ hcont
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)), hfpos] with t ht hft
  rw [Set.mem_Ioi] at ht
  have htpos : 0 < t := ht
  have hs : t ^ ((2:ℝ)/3) = Real.sqrt (t ^ ((4:ℝ)/3)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt htpos)]
    norm_num
  have hL : t ^ ((4:ℝ)/3) * Real.sqrt (f t) / t ^ 2 = Real.sqrt (f t) / t ^ ((2:ℝ)/3) := by
    have h23 : t ^ ((2:ℝ)/3) * t ^ ((4:ℝ)/3) = t ^ 2 := by
      rw [← Real.rpow_add htpos, ← Real.rpow_natCast t 2]
      congr 1
      norm_num
    have hw : t ^ ((4:ℝ)/3) / t ^ 2 = 1 / t ^ ((2:ℝ)/3) := by
      rw [div_eq_mul_inv, one_div, ← h23, mul_inv_rev, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos htpos _)), one_mul]
    calc t ^ ((4:ℝ)/3) * Real.sqrt (f t) / t ^ 2
        = Real.sqrt (f t) * (t ^ ((4:ℝ)/3) / t ^ 2) := by ring
      _ = Real.sqrt (f t) * (1 / t ^ ((2:ℝ)/3)) := by rw [hw]
      _ = Real.sqrt (f t) / t ^ ((2:ℝ)/3) := by ring
  have hR : Real.sqrt (f t) / t ^ ((2:ℝ)/3) = Real.sqrt (f t / t ^ ((4:ℝ)/3)) := by
    rw [hs, ← Real.sqrt_div' (f t) (Real.rpow_nonneg (le_of_lt htpos) _)]
  rw [hL, hR]

end Commons.Analysis.Asymptotic