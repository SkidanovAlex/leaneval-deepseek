import Mathlib

namespace Work.ZeroDensity.Zeta.Balanced

theorem sinCpowIoiIntegrable (s : ℂ) (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) (a : ℝ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => ((Real.sin (a * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (Set.Ioi (N : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  -- the dominating (integrable) function `u ↦ u ^ (-Re s - 1)`
  have hmaj : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · -- measurability: the integrand is continuous on `Ioi N`, `N ≥ 1 > 0`
    refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ioi
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn
    · refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_
      intro u hu
      exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le hNpos (le_of_lt hu))
  · -- pointwise domination by the modulus bound
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le hNpos (le_of_lt hu)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    have hsin : ‖((Real.sin (a * u) : ℝ) : ℂ)‖ ≤ 1 := by
      have key : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := fun x => by simp
      rw [key]
      exact Real.abs_sin_le_one _
    exact mul_le_of_le_one_left (Real.rpow_nonneg (le_of_lt hu0) _) hsin

end Work.ZeroDensity.Zeta.Balanced
