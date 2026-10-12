import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotSum_sectorPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- For almost every complement configuration `y`, the squared-norm integrand
`u ↦ ‖sectorSlice e S Φ y u‖²` of the slice is integrable.  (`Θ = slotExact e S Φ` is assumed
measurable, bounded and compactly supported.) -/
theorem aeIntegrableSectorSlice {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΘm : Measurable (Work.BoseBoxFock.slotExact e S Φ))
    (hΘb : ∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Φ x‖ ≤ C)
    (hΘc : HasCompactSupport (Work.BoseBoxFock.slotExact e S Φ)) :
    ∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      MeasureTheory.Integrable (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) =>
        ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2) := by
  classical
  obtain ⟨C, hC⟩ := hΘb
  refine Filter.Eventually.of_forall (fun y => ?_)
  -- The projection onto the slots in `S`, which is continuous, and the compact set cut out by the
  -- support of `Θ` in those slots.
  set proj : (Fin n → EuclideanSpace ℝ (Fin 3)) →
      ({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) := fun x i => x i.1 with hproj_def
  have hproj : Continuous proj := continuous_pi (fun i => continuous_apply (i : Fin n))
  set K' : Set ({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) :=
    proj '' tsupport (slotExact e S Φ) with hK'_def
  have hK'c : IsCompact K' := hΘc.isCompact.image hproj
  -- Every `u` outside `K'` has vanishing slice: the support of `Θ` forces the `S`-slots of an
  -- occupied configuration to lie in `K'`.
  have hzero : ∀ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3), u ∉ K' →
      sectorSlice e S Φ y u = 0 := by
    intro u hu
    by_contra hne
    have hmem : pairCoord S u y ∈ tsupport (slotExact e S Φ) :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hproj_apply : proj (pairCoord S u y) = u := by
      funext i
      exact pairCoord_mem S u y i.1 i.2
    have hmem' : proj (pairCoord S u y) ∈ K' := Set.mem_image_of_mem proj hmem
    rw [hproj_apply] at hmem'
    exact hu hmem'
  -- The slice is bounded by `C` on `K'` and vanishes off it, so it is dominated by the constant
  -- `C ^ 2` on the compact set `K'`.
  refine MeasureTheory.Integrable.mono'
    (g := K'.indicator (fun _ : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) => C ^ 2)) ?_ ?_ ?_
  · rw [MeasureTheory.integrable_indicator_iff hK'c.isClosed.measurableSet]
    exact MeasureTheory.integrableOn_const (hK'c.measure_lt_top.ne)
  · refine (hΘm.comp ?_).norm.pow_const 2 |>.aestronglyMeasurable
    refine measurable_pi_iff.mpr (fun i => ?_)
    by_cases hi : i ∈ S
    · simp only [pairCoord, dif_pos hi]
      exact measurable_pi_apply (⟨i, hi⟩ : {i // i ∈ S})
    · simp only [pairCoord, dif_neg hi]
      exact measurable_const
  · filter_upwards with u
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hu : u ∈ K'
    · rw [Set.indicator_of_mem hu]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC (pairCoord S u y)) 2
    · rw [Set.indicator_of_notMem hu, hzero u hu]
      simp

end Work.BoseBoxFock
