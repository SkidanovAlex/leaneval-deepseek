import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ZTracesAux

/-- Helper principle: if `G` is integrable on `Ioi 0` and `l` is a countably generated filter
on `ℝ` such that (i) `Ioi 0 ∈ l` and (ii) for every fixed point `x` the interval
`Ioo (z/2) (3*z/2)` eventually avoids `x` along `l`, then `∫ x in Ioo (z/2) (3*z/2), G x → 0`
along `l`.  The point is to write the set integral of the indicator of `Ioi 0` and apply
dominated convergence with dominating function `‖(Ioi 0).indicator G‖`. -/
private lemma tendsto_local_integral {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G (Set.Ioi 0))
    (l : Filter ℝ) [l.IsCountablyGenerated]
    (hx : ∀ x : ℝ, ∀ᶠ z in l, x ∉ Set.Ioo (z / 2) (3 * z / 2))
    (hpos : Set.Ioi (0 : ℝ) ∈ l) :
    Filter.Tendsto (fun z : ℝ => ∫ x in Set.Ioo (z / 2) (3 * z / 2), G x) l (nhds 0) := by
  have hGi : Integrable ((Set.Ioi 0).indicator G) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hG
  have hconv : Tendsto
      (fun z : ℝ =>
        ∫ x, (Set.Ioo (z / 2) (3 * z / 2)).indicator ((Set.Ioi 0).indicator G) x ∂volume)
      l (nhds 0) := by
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := l)
      (F := fun z : ℝ => fun x : ℝ =>
        (Set.Ioo (z / 2) (3 * z / 2)).indicator ((Set.Ioi 0).indicator G) x)
      (f := fun _ : ℝ => (0 : ℝ))
      (bound := fun x : ℝ => ‖(Set.Ioi 0).indicator G x‖)
      (Filter.Eventually.of_forall (fun z => hGi.1.indicator measurableSet_Ioo))
      (Filter.Eventually.of_forall (fun z => Filter.Eventually.of_forall (fun x => by
        by_cases h : x ∈ Set.Ioo (z / 2) (3 * z / 2)
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]
          simp)))
      hGi.norm
      (Filter.Eventually.of_forall (fun x => by
        refine Tendsto.congr' ?_ tendsto_const_nhds
        exact Filter.eventuallyEq_of_mem (hx x)
          (fun z hz => (Set.indicator_of_notMem hz ((Set.Ioi 0).indicator G)).symm)))
    simpa using hmain
  have hEq : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ x in Set.Ioo (z / 2) (3 * z / 2), G x)
        = ∫ x, (Set.Ioo (z / 2) (3 * z / 2)).indicator ((Set.Ioi 0).indicator G) x ∂volume := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have hsub : Set.Ioo (z / 2) (3 * z / 2) ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact lt_trans (by linarith : (0 : ℝ) < z / 2) hx.1
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun x hx => (Set.indicator_of_mem (hsub hx) G).symm)]
    exact (MeasureTheory.integral_indicator (f := (Set.Ioi 0).indicator G)
      (μ := volume) measurableSet_Ioo).symm
  refine Tendsto.congr' ?_ hconv
  exact Filter.eventuallyEq_of_mem hpos (fun z hz => (hEq z hz).symm)

theorem local_integral_tendsto_zero {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G (Set.Ioi 0)) :
    Filter.Tendsto (fun z : ℝ => ∫ x in Set.Ioo (z / 2) (3 * z / 2), G x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z : ℝ => ∫ x in Set.Ioo (z / 2) (3 * z / 2), G x)
        Filter.atTop (nhds 0) := by
  constructor
  · refine tendsto_local_integral hG (nhdsWithin 0 (Set.Ioi 0)) ?_ self_mem_nhdsWithin
    intro x
    rcases le_or_gt x 0 with hx | hx
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro hmem
      have hz0 : (0 : ℝ) < z := hz
      linarith [hmem.1, hz0, hx]
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 2 * x / 3 by linarith))] with z hz hz'
      intro hmem
      have h1 : z < 2 * x / 3 := hz'
      have h2 : x < 3 * z / 2 := hmem.2
      linarith
  · refine tendsto_local_integral hG Filter.atTop ?_ (Ioi_mem_atTop 0)
    intro x
    filter_upwards [Ioi_mem_atTop (2 * x)] with z hz
    intro hmem
    have h2 : 2 * x < z := hz
    linarith [h2, hmem.1]

end Work.FTS.EpsEngine.ZTracesAux
