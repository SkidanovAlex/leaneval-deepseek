import Mathlib
import Submission.Work.Koebe.gwDefs
import Submission.Work.Koebe.gwWindMem
import Submission.Work.Koebe.degreeFormula
import Submission.Work.Area.img_sphere_null

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Koebe

open Complex Metric Set MeasureTheory
open scoped Topology

noncomputable section

/-- `F` is holomorphic on the punctured disc. -/
theorem diffOn_F (F H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, F z = 1 / z + H z) :
    DifferentiableOn ℂ F (Metric.ball 0 1 \ {0}) := by
  refine DifferentiableOn.congr ?_ (fun z hz => (hexp z hz))
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hz1 : z ∈ Metric.ball (0:ℂ) 1 := hz.1
  have h1 : DifferentiableAt ℂ (fun z : ℂ => 1/z) z := by
    have : (fun z : ℂ => 1/z) = (fun z => z⁻¹) := by funext u; rw [one_div]
    rw [this]; exact differentiableAt_inv hz0
  exact (h1.add (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hz1))).differentiableWithinAt

theorem sArea_nonpos (F H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hF : Set.InjOn F (Metric.ball 0 1 \ {0}))
    (hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, F z = 1 / z + H z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (sArea F r).re ≤ 0 := by
  have hsphere_sub : Metric.sphere (0:ℂ) r ⊆ Metric.ball (0:ℂ) 1 \ {0} := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨by rw [Metric.mem_ball, dist_zero_right, hz]; exact hr1,
           by intro h0; rw [h0, norm_zero] at hz; linarith⟩
  have hFd := diffOn_F F H hH hexp
  obtain ⟨C, hC⟩ := (isCompact_sphere (0:ℂ) r).exists_bound_of_continuousOn
      (hFd.continuousOn.mono hsphere_sub)
  have hM : ∀ z, ‖z‖ = r → ‖F z‖ < C + 1 := by
    intro z hz
    have := hC z (by rwa [mem_sphere_zero_iff_norm])
    linarith
  rw [degreeFormula F H hH hF hexp r hr hr1 (C + 1) hM]
  have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ F '' (Metric.sphere 0 r) :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (Work.Area.img_sphere_null F H hH hF hexp hr hr1)
  have hle : (fun z => (winding F r z).re) ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) (C + 1))] 0 := by
    refine (MeasureTheory.ae_restrict_of_ae hnull).mono fun z hz => ?_
    rcases (gwWindMem F H hH hF hexp hr hr1 hz).1 with h | h <;> simp [h]
  by_cases hint : Integrable (fun z => winding F r z) (volume.restrict (Metric.ball (0 : ℂ) (C + 1)))
  · change RCLike.re (∫ z in Metric.ball (0 : ℂ) (C + 1), winding F r z) ≤ 0
    rw [← integral_re hint]
    exact MeasureTheory.integral_nonpos_of_ae hle
  · rw [MeasureTheory.integral_undef hint]
    simp

end

end Work.Koebe
