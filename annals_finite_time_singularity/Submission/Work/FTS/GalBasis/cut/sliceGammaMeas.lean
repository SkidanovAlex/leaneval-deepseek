import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cut

open MeasureTheory Set Filter

/-- The measure `volume` restricted to `Ioo 0 (π/2)` is the same as `volume` restricted to
`Icc 0 (π/2)`: the two sets differ by the (finite, hence null) set `{0, π/2}`. -/
private theorem restrict_Ioo_eq_restrict_Icc :
    volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict (Set.Icc 0 (Real.pi / 2)) := by
  have hs_sub : Set.Ioo 0 (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsub : Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo] at hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hθ with ⟨⟨h0, h2⟩, hns⟩
    rcases not_and_or.mp hns with h | h
    · exact Or.inl (le_antisymm (not_lt.mp h) h0)
    · exact Or.inr (le_antisymm h2 (not_lt.mp h))
  have hnull : volume (Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2)) = 0 :=
    measure_mono_null hsub (by
      refine Set.Finite.measure_zero ?_ volume
      exact (Set.finite_singleton (Real.pi / 2)).insert 0)
  refine Measure.restrict_congr_set ?_
  rw [ae_eq_set]
  exact ⟨by simp [Set.sdiff_eq_empty.mpr hs_sub], hnull⟩

/- On `Ioo 0 (π/2)` the sine `sin (2θ)` is strictly positive, hence so is any of its real
powers, and the functions `θ ↦ G θ ^ 2 * sin (2θ) ^ (-γ)`, `θ ↦ ∂ G θ ^ 2 * sin (2θ) ^ (2-γ)`
are continuous there.  Off that set (i.e. on `Icc 0 (π/2) \ Ioo 0 (π/2) = {0, π/2}`) we do not
care: that set is null, and `AEStronglyMeasurable` is an a.e. notion. -/
open MeasureTheory Set Filter in
theorem sliceGammaMeas {γ : ℝ} {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun θ => (G θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        (volume.restrict (Set.Icc 0 (Real.pi / 2))) ∧
    AEStronglyMeasurable (fun θ => (deriv G θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        (volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
  have hs_open : IsOpen s := isOpen_Ioo
  have hs_meas : MeasurableSet s := hs_open.measurableSet
  have hrestrict : volume.restrict s = volume.restrict (Set.Icc 0 (Real.pi / 2)) :=
    restrict_Ioo_eq_restrict_Icc
  have hsin_pos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsinc : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) s := by fun_prop
  have hsin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)) s :=
    hsinc.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsin2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - γ)) s :=
    hsinc.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hdc : ContinuousOn (derivWithin G s) s :=
    hG.continuousOn_derivWithin hs_open.uniqueDiffOn le_rfl
  refine ⟨?_, ?_⟩
  · rw [← hrestrict]
    exact ((hG.continuousOn.pow 2).mul hsin).aestronglyMeasurable hs_meas
  · rw [← hrestrict]
    have h2c : ContinuousOn
        (fun θ : ℝ => (derivWithin G s θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) s := by
      fun_prop
    refine (aestronglyMeasurable_congr ?_).mpr (h2c.aestronglyMeasurable hs_meas)
    filter_upwards [ae_restrict_mem hs_meas] with θ hθ
    rw [derivWithin_of_isOpen hs_open hθ]

end Work.FTS.GalBasis.cut
