import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotic

/-- Algebraic identity underlying the main limit: for `t > 0` and `f t > 0`,
`t^{1/3} g t / √(f t) = (g t / t^{1/3}) / √(f t / t^{4/3})`. -/
private lemma rpow_one_third_mul_div_sqrt_eq (f g : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hft : 0 < f t) :
    t ^ ((1:ℝ)/3) * g t / Real.sqrt (f t)
      = (g t / t ^ ((1:ℝ)/3)) / Real.sqrt (f t / t ^ ((4:ℝ)/3)) := by
  have h33 : t ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3) = t ^ ((2:ℝ)/3) := by
    rw [← Real.rpow_add ht]; norm_num
  have hsqrtden : Real.sqrt (t ^ ((4:ℝ)/3)) = t ^ ((2:ℝ)/3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt ht)]
    norm_num
  have hden : Real.sqrt (f t / t ^ ((4:ℝ)/3))
      = Real.sqrt (f t) / (t ^ ((1:ℝ)/3) * t ^ ((1:ℝ)/3)) := by
    rw [Real.sqrt_div (le_of_lt hft), hsqrtden, h33]
  rw [hden]
  have hft12 : 0 < Real.sqrt (f t) := Real.sqrt_pos.mpr hft
  field_simp

theorem rpow_one_third_deriv_div_sqrt {f g : ℝ → ℝ} {κ a : ℝ} (hκ : 0 < κ)
    (hfpos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < f t)
    (hIn : Filter.Tendsto (fun t : ℝ => f t / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds κ))
    (hDer : Filter.Tendsto (fun t : ℝ => g t / t ^ ((1:ℝ)/3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds a)) :
    Filter.Tendsto (fun t : ℝ => t ^ ((1:ℝ)/3) * g t / Real.sqrt (f t))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (a / Real.sqrt κ)) := by
  have hκsqrt : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hκ)
  have hlim : Filter.Tendsto
      (fun t : ℝ => (g t / t ^ ((1:ℝ)/3)) / Real.sqrt (f t / t ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (a / Real.sqrt κ)) :=
    hDer.div hIn.sqrt hκsqrt
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hfpos] with t ht hft
  exact (rpow_one_third_mul_div_sqrt_eq f g t ht hft).symm

end Commons.Analysis.Asymptotic