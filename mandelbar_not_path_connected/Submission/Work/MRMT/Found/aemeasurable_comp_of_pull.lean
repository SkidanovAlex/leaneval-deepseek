import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- If the pushforward of `volume.restrict Ω` along a continuous `f` is dominated (in the
sense of arbitrary `ENNReal`-valued test functions, i.e. as measures) by a multiple of
`volume.restrict Φ`, then any function `g` which is a.e. strongly measurable for `volume`
pulls back to an a.e. measurable function on `Ω`. -/
theorem aemeasurable_comp_of_pull {Ω Φ : Set ℂ} {f : ℂ → ℂ} (hf : Continuous f)
    (hpull : ∃ Cp : ℝ, 0 < Cp ∧ ∀ H : ℂ → ENNReal,
      MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) (fun z => H (f z))
        ≤ ENNReal.ofReal Cp * MeasureTheory.lintegral
            (MeasureTheory.Measure.restrict MeasureTheory.volume Φ) H)
    {g : ℂ → ℂ} (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    AEMeasurable (fun z => g (f z)) (MeasureTheory.Measure.restrict MeasureTheory.volume Ω) := by
  obtain ⟨Cp, hCp, hpull⟩ := hpull
  -- A measurable representative of `g`.
  obtain ⟨g', hg'meas, hgg'⟩ := hg.aemeasurable
  -- `N` is the (possibly non-measurable) null set on which `g` and `g'` differ.
  set N : Set ℂ := {x | ¬ (g x = g' x)} with hNdef
  have hNnull : (MeasureTheory.volume : MeasureTheory.Measure ℂ) N = 0 := by
    rw [hNdef]
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hgg'
    exact hgg'
  -- A measurable null superset `B ⊇ N`.
  set B : Set ℂ := MeasureTheory.toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℂ) N with hBdef
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact MeasureTheory.measurableSet_toMeasurable _ _
  have hNB : N ⊆ B := by
    rw [hBdef]; exact MeasureTheory.subset_toMeasurable _ _
  have hBnull : (MeasureTheory.volume : MeasureTheory.Measure ℂ) B = 0 := by
    rw [hBdef, MeasureTheory.measure_toMeasurable]; exact hNnull
  have hpre : MeasurableSet (f ⁻¹' B) := hf.measurable hBmeas
  -- Test the pullback inequality against the indicator of `B`.
  let H : ℂ → ENNReal := B.indicator (1 : ℂ → ENNReal)
  have hHcomp : (fun z => H (f z)) = (f ⁻¹' B).indicator (1 : ℂ → ENNReal) := by
    funext z
    change B.indicator (1 : ℂ → ENNReal) (f z) = (f ⁻¹' B).indicator (1 : ℂ → ENNReal) z
    by_cases hz : f z ∈ B
    · have hz' : z ∈ f ⁻¹' B := hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
      rfl
    · have hz' : z ∉ f ⁻¹' B := hz
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  have hR : MeasureTheory.lintegral
      (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Φ) H = 0 := by
    have h1 : MeasureTheory.lintegral
        (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Φ) H
        = (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Φ) B := by
      exact MeasureTheory.lintegral_indicator_one hBmeas
    rw [h1, MeasureTheory.Measure.restrict_apply hBmeas]
    exact MeasureTheory.measure_mono_null Set.inter_subset_left hBnull
  have hpullH := hpull H
  rw [hHcomp, MeasureTheory.lintegral_indicator_one hpre, hR, mul_zero] at hpullH
  -- The pushforward measure of `f ⁻¹' B` under `volume.restrict Ω` is zero.
  have hBzero :
      (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Ω) (f ⁻¹' B) = 0 :=
    le_antisymm hpullH bot_le
  have hNzero :
      (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Ω) (f ⁻¹' N) = 0 :=
    MeasureTheory.measure_mono_null (Set.preimage_mono hNB) hBzero
  -- Hence `g ∘ f` agrees with the measurable `g' ∘ f` almost everywhere on `Ω`.
  have hae : (fun z => g (f z)) =ᵐ[MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Ω]
      (fun z => g' (f z)) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    have hset : (f ⁻¹' N) = {a | ¬ ((fun z => g (f z)) a = (fun z => g' (f z)) a)} := by
      ext z; simp [hNdef]
    rw [← hset]
    exact hNzero
  have hmeasf : AEMeasurable (fun z => g' (f z))
      (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℂ) Ω) :=
    (hg'meas.comp hf.measurable).aemeasurable
  exact hmeasf.congr hae.symm

end Work.MRMT.Found
