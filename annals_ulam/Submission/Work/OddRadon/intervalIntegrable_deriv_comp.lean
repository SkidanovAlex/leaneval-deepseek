import Mathlib

open MeasureTheory Set

namespace Work.OddRadon

lemma intervalIntegrable_deriv_comp {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntervalIntegrable (fun t : ℝ => deriv G (c * t)) MeasureTheory.volume (0 : ℝ) 1 := by
  -- On `Icc 0 1` the one-sided derivative `derivWithin G (Icc 0 1)` is continuous,
  -- while on the interior it coincides with the ordinary `deriv G`.
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hcont : ContinuousOn (derivWithin G (Set.Icc 0 1)) (Set.Icc 0 1) :=
    hG.continuousOn_derivWithin hu (le_refl 1)
  -- `t ↦ c * t` maps `Icc 0 1` into `Icc 0 1` because `0 < c < 1`.
  have hmaps : Set.MapsTo (fun t : ℝ => c * t) (Set.Icc 0 1) (Set.Icc 0 1) := by
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    exact ⟨mul_nonneg hc.le ht.1, by nlinarith [hc, hc1, ht.1, ht.2]⟩
  have hcomp : ContinuousOn (fun t : ℝ => derivWithin G (Set.Icc 0 1) (c * t)) (Set.Icc 0 1) :=
    hcont.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have hI : IntervalIntegrable (fun t : ℝ => derivWithin G (Set.Icc 0 1) (c * t))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- The two functions agree on `(0, 1]`, hence a.e. on `Ioc 0 1`.
  refine IntervalIntegrable.congr (f := fun t : ℝ => derivWithin G (Set.Icc 0 1) (c * t))
    (g := fun t : ℝ => deriv G (c * t)) ?_ hI
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have ht0 : 0 < t := ht.1
  have hpos : 0 < c * t := mul_pos hc ht0
  have hlt : c * t < 1 := by
    calc c * t < 1 * t := mul_lt_mul_of_pos_right hc1 ht0
      _ = t := by ring
      _ ≤ 1 := ht.2
  have hnb : Set.Icc (0 : ℝ) 1 ∈ nhds (c * t) := by
    rw [← mem_interior_iff_mem_nhds, interior_Icc]
    exact ⟨hpos, hlt⟩
  exact derivWithin_of_mem_nhds hnb

end Work.OddRadon
