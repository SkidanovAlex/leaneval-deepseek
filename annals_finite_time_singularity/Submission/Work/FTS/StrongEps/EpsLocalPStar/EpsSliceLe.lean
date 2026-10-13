import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem EpsSliceLe :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : ℝ → ℝ → ℝ, ∀ z : ℝ, 0 < z →
      ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
        (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  -- The slice Hardy inequality `∫ sin(2θ)^{-c} u² ≤ C/(c-1)² ∫ sin(2θ)^{2-c}(u')²` for
  -- `1 < c ≤ 3/2`, applied at `c = γ = 1 + α/10` and `u = (f z ·)`.
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak
  refine ⟨CH, hCHpos, ?_⟩
  intro α hα f z hz hcd ht1 ht2 hslot
  obtain ⟨hα0, hα1⟩ := hα
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγ32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- the Hardy hypothesis on the derivative side, converted from the `(0,1)`-slot
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.StrongEps.EpsSqTools.pth_slice_integrable (α := α) (z := z) (f := f)
      hα0 hα1 hz hslot
  obtain ⟨hL1, hL2⟩ := hCH (Work.Spaces.gam α) (fun θ => f z θ) hγ1 hγ32 hcd ht1 ht2 hint
  have hcomm : (∫ θ in Work.Spaces.Iθ,
        (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ _ => by ring)
  have hbound : (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CH / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Work.FTS.StrongEps.EpsSqTools.epsSq_slice_eq α z f
      _ = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (f z θ) ^ 2 := by rw [hcomm]
      _ ≤ (Work.Spaces.w z) ^ 2 * (CH / (Work.Spaces.gam α - 1) ^ 2 *
            ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
      _ = CH / (Work.Spaces.gam α - 1) ^ 2 * ((Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z θ) ^ 2) := by
          ring
      _ = CH / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
          rw [Work.FTS.StrongEps.EpsSqTools.slot_slice_eq (α := α) (z := z) hα0 hα1 f]
  refine ⟨?_, hbound⟩
  -- integrability of the `EpsSq`-slice, transported from the Hardy conclusion
  refine (hL1.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
  have h1 : (Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Work.FTS.StrongEps.EpsSqTools.epsW_sq_eq hθ
  simp only []
  rw [mul_pow, h1]
  ring

end Work.FTS.StrongEps.EpsLocalPStar
