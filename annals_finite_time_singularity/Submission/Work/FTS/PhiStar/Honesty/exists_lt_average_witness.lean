import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem exists_lt_average_witness {G : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hGint : MeasureTheory.IntegrableOn G (Set.Ici 0))
    (hGnn : ∀ s ∈ Set.Ici (0 : ℝ), 0 ≤ G s) :
    ∃ u ∈ Set.Icc (t / 2) t, G u * t ≤ 4 * ∫ s in (t / 2)..t, G s := by
  -- First moment method: some point of `(t/2, t]` is at most the average of `G`,
  -- i.e. `G u ≤ (∫_{t/2}^t G) / (t/2) = 2 * ∫_{t/2}^t G / t`.
  have hhalf : t / 2 ≤ t := by linarith
  have hsub : Set.Ioc (t / 2) t ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simp only [Set.mem_Ici]
    linarith [hx.1, ht]
  have hfOn : MeasureTheory.IntegrableOn G (Set.Ioc (t / 2) t) := hGint.mono_set hsub
  have hne0 : MeasureTheory.volume (Set.Ioc (t / 2) t) ≠ 0 := by
    rw [Real.volume_Ioc, ENNReal.ofReal_ne_zero_iff]
    linarith
  have hneTop : MeasureTheory.volume (Set.Ioc (t / 2) t) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, hu, hle⟩ := MeasureTheory.exists_le_setAverage hne0 hneTop hfOn
  refine ⟨u, ⟨hu.1.le, hu.2⟩, ?_⟩
  -- the integral is nonnegative because `G ≥ 0` on `[0, ∞) ⊇ (t/2, t]`
  have hA : 0 ≤ ∫ s in (t / 2)..t, G s :=
    intervalIntegral.integral_nonneg hhalf
      (fun x hx => hGnn x (by simp only [Set.mem_Ici]; linarith [hx.1, ht]))
  have hAi : ∫ x in Set.Ioc (t / 2) t, G x = ∫ s in (t / 2)..t, G s := by
    rw [intervalIntegral.integral_of_le hhalf]
  rw [MeasureTheory.setAverage_eq, Real.volume_real_Ioc_of_le hhalf, hAi, smul_eq_mul] at hle
  have h1 : G u * t ≤ 2 * ∫ s in (t / 2)..t, G s := by
    have h2 := mul_le_mul_of_nonneg_right hle ht.le
    have h3 : (t - t / 2)⁻¹ * (∫ s in (t / 2)..t, G s) * t
        = 2 * ∫ s in (t / 2)..t, G s := by
      have htne : t ≠ 0 := ne_of_gt ht
      field_simp
      ring
    linarith [h2, h3]
  linarith [h1, hA]

end Work.FTS.PhiStar.Honesty
