import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set

/-- If a function is continuous on the open interval `(0, π/2)` and is pointwise dominated by a
constant multiple of `θ ↦ θ ^ (-η) + (π/2 - θ) ^ (-η)` with `η < 1`, then it is integrable on the
closed interval `[0, π/2]`. -/
theorem integrableOn_of_rpow_majorant {η C : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hC : 0 ≤ C)
    {g : ℝ → ℝ} (hgc : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖g θ‖ ≤ C * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) :
    MeasureTheory.IntegrableOn g (Set.Icc 0 (Real.pi / 2)) MeasureTheory.volume := by
  have ha : 0 < Real.pi / 2 := by positivity
  -- Integrability of the singular part `θ ↦ θ ^ (-η)`.
  have hA : IntegrableOn (fun θ : ℝ => θ ^ (-η)) (Ioo 0 (Real.pi / 2)) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ha).mpr (by linarith)
  -- Integrability of the reflected singular part `θ ↦ (π/2 - θ) ^ (-η)`, via the measure-preserving
  -- reflection `θ ↦ π/2 - θ`.
  have hB : IntegrableOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-η)) (Ioo 0 (Real.pi / 2)) volume := by
    have hmp : MeasurePreserving (fun θ : ℝ => Real.pi / 2 - θ) volume volume :=
      Measure.measurePreserving_sub_left volume (Real.pi / 2)
    have hemb : MeasurableEmbedding (fun θ : ℝ => Real.pi / 2 - θ) := by
      have h' := (Homeomorph.subLeft (Real.pi / 2)).toMeasurableEquiv.measurableEmbedding
      simpa using h'
    have hpre : (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' (Ioo 0 (Real.pi / 2)) = Ioo 0 (Real.pi / 2) := by
      ext θ; simp only [Set.mem_preimage, Set.mem_Ioo]
      constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
    have h2 := (MeasurePreserving.integrableOn_comp_preimage hmp hemb
      (f := fun u : ℝ => u ^ (-η)) (s := Ioo 0 (Real.pi / 2))).mpr hA
    rwa [hpre] at h2
  -- The majorant is integrable on the open interval, hence on the closed interval.
  have hF : IntegrableOn (fun θ : ℝ => C * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)))
      (Ioo 0 (Real.pi / 2)) volume := (hA.add hB).const_mul C
  have hFicc : IntegrableOn (fun θ : ℝ => C * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)))
      (Icc 0 (Real.pi / 2)) volume :=
    hF.congr_set_ae (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  -- `g` is almost everywhere strongly measurable on `[0, π/2]`.
  have hmeas : AEStronglyMeasurable g (volume.restrict (Icc 0 (Real.pi / 2))) := by
    rw [Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]
    exact hgc.aestronglyMeasurable measurableSet_Ioo
  -- Almost every point of `[0, π/2]` lies in `(0, π/2)`.
  have hIcc : ∀ᵐ θ ∂(volume.restrict (Icc 0 (Real.pi / 2))), θ ∈ Ioo 0 (Real.pi / 2) := by
    rw [Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]
    exact self_mem_ae_restrict measurableSet_Ioo
  refine hFicc.mono' hmeas ?_
  filter_upwards [hIcc] with θ hθ
  exact h θ hθ

end Work.Elliptic
