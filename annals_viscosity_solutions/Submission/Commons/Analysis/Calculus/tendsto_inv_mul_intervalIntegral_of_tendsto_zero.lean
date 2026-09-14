import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter Set
open scoped Topology

namespace Commons.Analysis.Calculus

theorem tendsto_inv_mul_intervalIntegral_of_tendsto_zero {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hg : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)) (hint : ∀ t ∈ Set.Ioo (0:ℝ) ε, IntervalIntegrable g MeasureTheory.volume 0 t) : Filter.Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, g s) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ' : 0 < δ / 2 := by linarith
  have hge : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), dist (g s) 0 < δ / 2 :=
    (Metric.tendsto_nhds.mp hg) (δ / 2) hδ'
  have hmem : {s : ℝ | ‖g s‖ < δ / 2} ∈ 𝓝[Set.Ioi 0] (0:ℝ) := by
    filter_upwards [hge] with s hs
    simpa only [dist_eq_norm, sub_zero] using hs
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨r, hr, hsub⟩ := hmem
  have hmin : 0 < min r ε := lt_min hr hε
  refine Filter.mem_of_superset (x := Set.Ioo (0:ℝ) (min r ε)) ?_ ?_
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio (min r ε), Iio_mem_nhds hmin, fun x hx => ⟨hx.2, hx.1⟩⟩
  · intro t ht
    change dist (t⁻¹ * ∫ s in (0:ℝ)..t, g s) 0 < δ
    have ht0 : 0 < t := ht.1
    have htr : t < r := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htε : t < ε := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have _hintt : IntervalIntegrable g MeasureTheory.volume 0 t := hint t ⟨ht0, htε⟩
    have hbound : ‖∫ s in (0:ℝ)..t, g s‖ ≤ (δ / 2) * |t - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : 0 < x ∧ x ≤ t := by
        rwa [Set.uIoc_of_le (le_of_lt ht0), Set.mem_Ioc] at hx
      have hxr : dist x 0 < r := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx'.1]
        exact lt_of_le_of_lt hx'.2 htr
      have hgx : ‖g x‖ < δ / 2 := hsub ⟨Metric.mem_ball.mpr hxr, hx'.1⟩
      exact le_of_lt hgx
    have hdist : dist (t⁻¹ * ∫ s in (0:ℝ)..t, g s) 0
        = ‖t⁻¹ * ∫ s in (0:ℝ)..t, g s‖ := by
      rw [dist_eq_norm, sub_zero]
    rw [hdist]
    calc ‖t⁻¹ * ∫ s in (0:ℝ)..t, g s‖
        = |t⁻¹| * ‖∫ s in (0:ℝ)..t, g s‖ := by
            rw [norm_mul, Real.norm_eq_abs]
      _ = t⁻¹ * ‖∫ s in (0:ℝ)..t, g s‖ := by
            rw [abs_of_pos (inv_pos.mpr ht0)]
      _ ≤ t⁻¹ * ((δ / 2) * |t - 0|) :=
            mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr ht0))
      _ = δ / 2 := by
            rw [sub_zero, abs_of_pos ht0, mul_comm (δ / 2) t, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht0),
              one_mul]
      _ < δ := by linarith

end Commons.Analysis.Calculus