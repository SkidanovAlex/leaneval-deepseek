import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.TanTheta

/-- The `L²` square root of the weight `sin (2θ) ^ (-η)`: `sqWeight η θ ^ 2 = sin (2*θ) ^ (-η)`
for `θ ∈ (0, π/2)`, and `θ ↦ sqWeight η θ` is measurable. -/
private def sqWeight (η : ℝ) : ℝ → ℝ := fun θ => Real.sqrt ((Real.sin (2 * θ)) ^ (-η))

/-- **Cauchy–Schwarz in `L²` for the weight `sin(2θ)^{-η}` on `(0, π/2)`, in the form that is
actually true**: if `f` and `g` are a.e. measurable and `f² sin(2θ)^{-η}`, `g² sin(2θ)^{-η}`
are integrable on `(0, π/2)`, then so is `f g sin(2θ)^{-η}`.

This is `L² · L² ⊆ L¹` for the measure `sin(2θ)^{-η} dθ` on `(0, π/2)`: writing
`sin(2θ)^{-η} = sqWeight η θ · sqWeight η θ`, the two functions `f · sqWeight η` and
`g · sqWeight η` have square-integrable squares, hence are in `L²`, and Hölder with the triple
`(2, 2, 1)` bounds their product in `L¹`.

The hypothesis `AEMeasurable` cannot be dropped: see the module
`Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight` for a counterexample to
the version without it.  For `ℝ`-valued functions `AEMeasurable` and `AEStronglyMeasurable`
agree, and `AEMeasurable` holds e.g. as soon as `f` is continuous on `(0, π/2)`
(`ContinuousOn.aemeasurable f measurableSet_Ioo`). -/
theorem integrable_mul_of_sq_weight_of_aemeasurable (η : ℝ) {f g : ℝ → ℝ}
    (hf_meas : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hg_meas : AEMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hf : MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)))
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => f θ * g θ * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hu_sq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      sqWeight η θ ^ 2 = (Real.sin (2 * θ)) ^ (-η) := by
    intro θ hθ
    simp only [sqWeight]
    exact Real.sq_sqrt (Real.rpow_nonneg (le_of_lt (hsin θ hθ)) _)
  have hu_meas : Measurable (sqWeight η) := by
    show Measurable fun θ : ℝ => Real.sqrt ((Real.sin (2 * θ)) ^ (-η))
    fun_prop
  -- `f * sqWeight η` is in `L²` for the restricted measure (its square is `f² sin(2θ)^{-η}`)
  have hFu : MeasureTheory.IntegrableOn (fun θ => (f θ * sqWeight η θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hf.congr_fun (fun θ hθ => by rw [mul_pow, hu_sq θ hθ]) measurableSet_Ioo
  have hGu : MeasureTheory.IntegrableOn (fun θ => (g θ * sqWeight η θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hg.congr_fun (fun θ hθ => by rw [mul_pow, hu_sq θ hθ]) measurableSet_Ioo
  have hF_meas : MeasureTheory.AEStronglyMeasurable (fun θ => f θ * sqWeight η θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hf_meas.mul hu_meas.aemeasurable).aestronglyMeasurable
  have hG_meas : MeasureTheory.AEStronglyMeasurable (fun θ => g θ * sqWeight η θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hg_meas.mul hu_meas.aemeasurable).aestronglyMeasurable
  have hF : MeasureTheory.MemLp (fun θ => f θ * sqWeight η θ) 2
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hF_meas).2 hFu
  have hG : MeasureTheory.MemLp (fun θ => g θ * sqWeight η θ) 2
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hG_meas).2 hGu
  -- Hölder with the triple `(2, 2, 1)`
  have hI : MeasureTheory.IntegrableOn
      (fun θ => (f θ * sqWeight η θ) * (g θ * sqWeight η θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.MemLp.integrable_mul hF hG
  refine hI.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  show (f θ * sqWeight η θ) * (g θ * sqWeight η θ) = f θ * g θ * (Real.sin (2 * θ)) ^ (-η)
  rw [show (f θ * sqWeight η θ) * (g θ * sqWeight η θ)
      = f θ * g θ * (sqWeight η θ * sqWeight η θ) by ring, ← pow_two, hu_sq θ hθ]

end Work.FTS.EllipticEst.TanTheta
