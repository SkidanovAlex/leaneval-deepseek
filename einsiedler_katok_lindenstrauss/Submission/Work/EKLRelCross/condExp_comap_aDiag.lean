import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.setIntegral_comp_preimage_restrict

namespace Work.EKLRelCross

open MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Conditional expectation of a composition with a measure-preserving self-map.**

Let `T : α → α` preserve a probability measure `μ`, let `m ≤ mX` be a sub-σ-algebra and `Z` be
`m`-measurable.  Then for every bounded measurable `f` and `μ.restrict (T ⁻¹' Z)`-a.e. `x`,

`E[f ∘ T | T ⁻¹' m](x) = E[f | m](T x)`,

where both conditional expectations are taken for the restrictions of `μ` to `T ⁻¹' Z`,
respectively `Z`.  The point is that `T` pushes `μ.restrict (T ⁻¹' Z)` forward to `μ.restrict Z`,
so `T` transports the conditional expectation from `Z` to `T ⁻¹' Z`; no invertibility of `T` is
needed, because the defining set integral identity only has to be checked on sets of the form
`T ⁻¹' B`, `B` measurable for `m`. -/
theorem condExp_comap_of_measurePreserving
    {α : Type*} (mX : MeasurableSpace α) (T : α → α)
    (μ : @MeasureTheory.Measure α mX) [MeasureTheory.IsProbabilityMeasure μ]
    (hT : @MeasureTheory.MeasurePreserving α α mX mX T μ μ)
    (m : MeasurableSpace α) (hm : m ≤ mX) {Z : Set α} (hZ : @MeasurableSet α m Z)
    {f : α → ℝ} (hf : @Measurable α ℝ mX Real.measurableSpace f)
    (hbdd : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂(μ.restrict (T ⁻¹' Z)),
      @MeasureTheory.condExp α ℝ (MeasurableSpace.comap T m) mX _ _ (μ.restrict (T ⁻¹' Z))
        (f ∘ T) x
      = @MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f (T x) := by
  -- Make `mX` the preferred `MeasurableSpace α` instance inside the proof: the σ-algebra `m` is
  -- also a local hypothesis of class type, and without this every instance argument that is not
  -- pinned by an explicit application would be resolved to `m` instead of `mX`.
  letI : MeasurableSpace α := mX
  obtain ⟨C, hC⟩ := hbdd
  have hTmeas : @Measurable α α mX mX T := hT.measurable
  have hZ' : @MeasurableSet α mX Z := hm Z hZ
  have hm' : MeasurableSpace.comap T m ≤ mX :=
    (MeasurableSpace.comap_mono hm).trans hTmeas.comap_le
  have hmap : MeasureTheory.Measure.map T (μ.restrict (T ⁻¹' Z)) = μ.restrict Z := by
    have h := MeasureTheory.Measure.restrict_map (μ := μ) hTmeas hZ'
    rw [@MeasureTheory.MeasurePreserving.map_eq α α mX mX T μ μ hT] at h
    exact h.symm
  -- `f` is integrable for `μ.restrict Z` (it is bounded and the measure is finite)
  have hfi : MeasureTheory.Integrable f (μ.restrict Z) :=
    MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hC y))
  -- and so is its conditional expectation with respect to `m`
  have hci : MeasureTheory.Integrable
      (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f) (μ.restrict Z) :=
    MeasureTheory.integrable_condExp (m := m) (m₀ := mX) (μ := μ.restrict Z) (f := f)
  -- integrability of `f ∘ T` for `μ.restrict (T ⁻¹' Z)`
  have hfi_comp : MeasureTheory.Integrable (f ∘ T) (μ.restrict (T ⁻¹' Z)) := by
    have h1 : MeasureTheory.Integrable f
        (MeasureTheory.Measure.map T (μ.restrict (T ⁻¹' Z))) := by
      rw [hmap]; exact hfi
    exact h1.comp_measurable hTmeas
  -- integrability of `E[f | m] ∘ T` for `μ.restrict (T ⁻¹' Z)`
  have hci_comp : MeasureTheory.Integrable
      (fun x => (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f) (T x))
      (μ.restrict (T ⁻¹' Z)) := by
    have h1 : MeasureTheory.Integrable
        (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f)
        (MeasureTheory.Measure.map T (μ.restrict (T ⁻¹' Z))) := by
      rw [hmap]; exact hci
    exact h1.comp_measurable hTmeas
  -- `E[f | m] ∘ T` is `(comap T m)`-strongly measurable
  have hci_aesm : @MeasureTheory.AEStronglyMeasurable α ℝ _ (MeasurableSpace.comap T m) mX
      (fun x => (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f) (T x))
      (μ.restrict (T ⁻¹' Z)) :=
    ((MeasureTheory.stronglyMeasurable_condExp (m := m) (m₀ := mX) (μ := μ.restrict Z)
        (f := f)).comp_measurable
      ((measurable_iff_comap_le (m₁ := MeasurableSpace.comap T m) (m₂ := m)
        (f := T)).mpr le_rfl)).aestronglyMeasurable
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (m := MeasurableSpace.comap T m)
    (m₀ := mX) (μ := μ.restrict (T ⁻¹' Z)) (f := f ∘ T)
    (g := fun x => (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f) (T x))
    hm' hfi_comp ?_ ?_ hci_aesm).symm
  · intro s _ _
    exact hci_comp.integrableOn
  · intro s hs _
    obtain ⟨B, hB, hBs⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← hBs]
    calc ∫ x in T ⁻¹' B, (fun x => (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f) (T x)) x
          ∂(μ.restrict (T ⁻¹' Z))
        = ∫ x in B, (@MeasureTheory.condExp α ℝ m mX _ _ (μ.restrict Z) f) x
            ∂(μ.restrict Z) :=
          setIntegral_comp_preimage_restrict T μ hT hZ' (hm B hB) hci
      _ = ∫ x in B, f x ∂(μ.restrict Z) :=
          MeasureTheory.setIntegral_condExp hm hfi hB
      _ = ∫ x in T ⁻¹' B, (f ∘ T) x ∂(μ.restrict (T ⁻¹' Z)) :=
          (setIntegral_comp_preimage_restrict T μ hT hZ' (hm B hB) hfi).symm

theorem condExp_comap_aDiag
    {μ : @MeasureTheory.Measure Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : @MeasureTheory.MeasurePreserving Work.EKLContract.X3 Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 Work.EKLContract.instMeasurableSpaceX3
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (m : MeasurableSpace Work.EKLContract.X3) (hm : m ≤ borel Work.EKLContract.X3)
    {Z : Set Work.EKLContract.X3} (hZ : @MeasurableSet Work.EKLContract.X3 m Z)
    {f : Work.EKLContract.X3 → ℝ}
    (hf : @Measurable Work.EKLContract.X3 ℝ Work.EKLContract.instMeasurableSpaceX3
      Real.measurableSpace f)
    (hbdd : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂(μ.restrict ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) ⁻¹' Z)),
      @MeasureTheory.condExp Work.EKLContract.X3 ℝ
        (MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) m)
        Work.EKLContract.instMeasurableSpaceX3
        _ _ (μ.restrict ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) ⁻¹' Z))
        (f ∘ (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)) x
      = @MeasureTheory.condExp Work.EKLContract.X3 ℝ m Work.EKLContract.instMeasurableSpaceX3
        _ _ (μ.restrict Z) f (Work.EKLContract.aDiag t • x) :=
  condExp_comap_of_measurePreserving Work.EKLContract.instMeasurableSpaceX3
    (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) μ hmp m hm hZ hf hbdd

end Work.EKLRelCross
