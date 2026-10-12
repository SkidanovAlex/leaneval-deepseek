import ChallengeDeps
import Submission.ScatKernelChosen
import Submission.ScatProfileExterior
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

theorem ae_profile_norm_transfer {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hrad : _root_.BoseGases.IsRadial w) {U : ℝ → ℝ}
    (h : ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      0 < r → U r = r * Submission.BoseGases.radialProfile w r) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      0 < ‖x‖ → U ‖x‖ = ‖x‖ * w x := by
  -- The 1D bad set of radii: the `h` hypothesis makes it null.
  let N : Set ℝ := {r : ℝ | 0 < r ∧ U r ≠ r * Submission.BoseGases.radialProfile w r}
  have hNvol : (MeasureTheory.volume : MeasureTheory.Measure ℝ) N = 0 := by
    have hbad := MeasureTheory.ae_iff.mp h
    refine MeasureTheory.measure_mono_null (s := N)
      (t := {r : ℝ | ¬(0 < r → U r = r * Submission.BoseGases.radialProfile w r)})
      ?_ hbad
    intro r hr hEq
    exact hr.2 (hEq hr.1)
  -- Replace `N` by a measurable hull `S`, still null.
  let S : Set ℝ :=
    MeasureTheory.toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ) N
  have hSmeas : MeasurableSet S := MeasureTheory.measurableSet_toMeasurable _ _
  have hNS : N ⊆ S := MeasureTheory.subset_toMeasurable _ _
  have hSvol : (MeasureTheory.volume : MeasureTheory.Measure ℝ) S = 0 := by
    rw [MeasureTheory.measure_toMeasurable]
    exact hNvol
  -- Push the null set of radii back to `ℝ³` through the norm.
  have hTvol : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ∈ S} = 0 :=
    Submission.BoseGases.volume_preimage_norm_null_r3 hSmeas hSvol
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null
    (s := {x : EuclideanSpace ℝ (Fin 3) | ¬(0 < ‖x‖ → U ‖x‖ = ‖x‖ * w x)})
    (t := {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ∈ S}) ?_ hTvol
  intro x hx
  have hxpos : 0 < ‖x‖ := by
    by_contra hc
    exact hx (fun hpos => absurd hpos hc)
  have hxne : U ‖x‖ ≠ ‖x‖ * w x := by
    intro hEq
    exact hx (fun _ => hEq)
  exact hNS ⟨hxpos, fun hEq => hxne (by rw [hEq, Submission.BoseGases.radial_eq_profile hrad x])⟩

end Work.BoseFixB1B
