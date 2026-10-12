import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.SmallBoxA0.OneDPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Filter Set

theorem OneDPotTailTendsto {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    (hint : MeasureTheory.IntegrableOn (fun r : ℝ => (r ^ 2 * p r) * Gfun p r) (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto (fun ε : ℝ => ∫ r in Set.Ioo ε R, (r ^ 2 * p r) * Gfun p r)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ r in Set.Ioi (0 : ℝ), (r ^ 2 * p r) * Gfun p r)) := by
  set g : ℝ → ℝ := fun r => (r ^ 2 * p r) * Gfun p r with hg
  set G0 : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator g with hG0
  have hgi : MeasureTheory.IntegrableOn g (Set.Ioi (0 : ℝ)) := by rw [hg]; exact hint
  have hG0int : Integrable G0 := by
    rw [hG0]; exact (integrable_indicator_iff measurableSet_Ioi).2 hgi
  have hG0meas : AEStronglyMeasurable G0 := hG0int.aestronglyMeasurable
  -- Pointwise convergence of the indicator family.
  have hlim : ∀ a : ℝ, Tendsto (fun n : ℝ => (Set.Ioo n R).indicator G0 a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (G0 a)) := by
    intro a
    by_cases ha : a ∈ Set.Ioo (0 : ℝ) R
    · have hmem : Set.Ioo (0 : ℝ) a ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
        rw [mem_nhdsWithin_iff_eventually]
        filter_upwards [Iio_mem_nhds ha.1] with n hn hpos
        exact ⟨hpos, hn⟩
      have hev : (fun n : ℝ => (Set.Ioo n R).indicator G0 a) =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
          (fun _ => G0 a) := by
        filter_upwards [hmem] with n hn
        rw [Set.indicator_of_mem (show a ∈ Set.Ioo n R from ⟨hn.2, ha.2⟩)]
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
    · have hz : G0 a = 0 := by
        rw [hG0]
        by_cases hpos : a ∈ Set.Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hpos]
          have hge : R ≤ a := by
            rcases lt_or_ge a R with h | h
            · exact absurd ⟨hpos, h⟩ ha
            · exact h
          rw [hg]
          simp only
          rw [hp0 a hge]
          ring
        · exact Set.indicator_of_notMem hpos g
      have hev : (fun n : ℝ => (Set.Ioo n R).indicator G0 a) =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
          (fun _ => G0 a) := by
        filter_upwards [self_mem_nhdsWithin] with n hn
        simp only [Set.mem_Ioi] at hn
        rw [Set.indicator_of_notMem (show a ∉ Set.Ioo n R from by
          rintro ⟨hna, haR⟩
          rcases lt_or_ge a R with h | h
          · exact ha ⟨lt_trans hn hna, h⟩
          · exact absurd haR (not_lt.mpr h))]
        exact hz.symm
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  -- Dominated convergence.
  have hDCT : Tendsto (fun n : ℝ => ∫ a, (Set.Ioo n R).indicator G0 a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ a, G0 a)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (F := fun n : ℝ => (Set.Ioo n R).indicator G0) (f := G0) (fun a => ‖G0 a‖)
      (Filter.Eventually.of_forall fun n => hG0meas.indicator measurableSet_Ioo)
      (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun a =>
        norm_indicator_le_norm_self G0 a)
      hG0int.norm
      (Filter.Eventually.of_forall hlim)
  have hRHS : (∫ a, G0 a) = ∫ a in Set.Ioi (0 : ℝ), g a := by
    rw [hG0, MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [hRHS] at hDCT
  refine Filter.Tendsto.congr' ?_ hDCT
  filter_upwards [self_mem_nhdsWithin] with n hn
  simp only [Set.mem_Ioi] at hn
  rw [MeasureTheory.integral_indicator measurableSet_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro a ha
  rw [hG0, Set.indicator_of_mem (show a ∈ Set.Ioi (0 : ℝ) from lt_trans hn ha.1)]

end Work.SmallBoxA0
