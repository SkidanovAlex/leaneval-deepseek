import Mathlib

namespace Work.ZeroDensity.Zeta.Balanced

open MeasureTheory Set

/-- The function `u ↦ cos (a u) * u ^ (-s - 2)` is integrable on `(N, ∞)` for `N ≥ 1`
and `0 < s.re`.

Indeed `cos (a u)` is bounded by `1` in norm, while `‖u ^ (-s - 2)‖ = u ^ (-s.re - 2)`
decays integrably since `-s.re - 2 < -1`. -/
theorem cosCpowIoiIntegrable (s : ℂ) (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) (a : ℝ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => ((Real.cos (a * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      (Set.Ioi (N : ℝ)) := by
  have ha : (-s - 2 : ℂ).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat]
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  -- An integrable majorant: the norm of the power factor.
  have hg : Integrable (fun u : ℝ => ‖(u : ℂ) ^ (-s - 2)‖)
      (volume.restrict (Ioi (N : ℝ))) :=
    integrableOn_Ioi_norm_cpow_of_lt ha hNpos
  -- Measurability of the bounded factor.
  have hmeas1 : AEStronglyMeasurable (fun u : ℝ => ((Real.cos (a * u) : ℝ) : ℂ))
      (volume.restrict (Ioi (N : ℝ))) :=
    (Complex.continuous_ofReal.measurable.comp (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 2))
      (volume.restrict (Ioi (N : ℝ))) :=
    (integrableOn_Ioi_cpow_of_lt ha hNpos).aestronglyMeasurable
  refine Integrable.mono' hg (hmeas1.mul hmeas2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _hu
  rw [norm_mul]
  have hle : ‖((Real.cos (a * u) : ℝ) : ℂ)‖ ≤ 1 := by
    have h1 : ‖((Real.cos (a * u) : ℝ) : ℂ)‖ = |Real.cos (a * u)| := RCLike.norm_ofReal _
    rw [h1, abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc ‖((Real.cos (a * u) : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 2)‖
      ≤ 1 * ‖(u : ℂ) ^ (-s - 2)‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖(u : ℂ) ^ (-s - 2)‖ := one_mul _

end Work.ZeroDensity.Zeta.Balanced
