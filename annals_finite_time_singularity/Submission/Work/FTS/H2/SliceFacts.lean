import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- Elementary slice facts for a function smooth on an open neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd f`, i.e. `ContDiffOn ℝ ⊤ (Function.uncurry f)` on
`Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)`):

* for `z ∈ Work.Spaces.Iz = Set.Ici 0` the angular slice `θ ↦ f z θ` is continuous on
  `Work.Spaces.Iθ = Set.Icc 0 (π/2)`;
* hence `θ ↦ (f z θ)²` is integrable on `Iθ` for each `z ∈ Iz`;
* the radial function `r ↦ ∫_θ (f r θ)²` is almost everywhere strongly measurable for
  `volume.restrict (Set.Ioi 0)`.

These are the regularity inputs of the Cauchy–Schwarz estimate
`|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}` (Elgindi, Proposition `muestimate`).

Intended proof: for the first, compose the continuous map `θ ↦ (z,θ) : Iθ → ℝ × ℝ` (whose
image lies in `Ioi (-1) ×ˢ Ioo (-1) (π/2+1)` because `z ≥ 0 > -1` and `0 ≤ θ ≤ π/2`) with
`(hf.continuousOn)` and square with `ContinuousOn.pow`; `ContinuousOn.integrableOn_compact`
(or `ContinuousOn.integrableOn_Icc`) gives the second.  For the third, the function
`(r,θ) ↦ (f r θ)²` is continuous on `Ioi 0 ×ˢ Iθ`, hence `AEStronglyMeasurable` for
`(volume.prod volume).restrict (Ioi 0 ×ˢ Iθ)` (`ContinuousOn.aestronglyMeasurable`), which
equals `(volume.restrict (Ioi 0)).prod (volume.restrict Iθ)` by
`MeasureTheory.Measure.prod_restrict`; then
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` integrates out the second variable. -/
theorem SliceFacts {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) :
    (∀ z ∈ Work.Spaces.Iz, ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ) ∧
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- The neighbourhood box on which `f` is smooth
  have hsm : ContDiffOn ℝ ⊤ (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hf
  have hzbox : ∀ z ∈ Work.Spaces.Iz, z ∈ Set.Ioi (-1) := by
    intro z hz
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
    simp only [Set.mem_Ioi]
    linarith
  have hθbox : ∀ θ ∈ Work.Spaces.Iθ, θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- ### 1. continuity of the angular slice
  have hslice : ∀ z ∈ Work.Spaces.Iz, ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ := by
    intro z hz
    have hslice' : ContDiffOn ℝ ⊤ (fun θ => f z θ) (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
      have h2 : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ))
          (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
        contDiffOn_const.prodMk contDiffOn_id
      have h3 := hsm.comp h2 (fun θ hθ => ⟨hzbox z hz, hθ⟩)
      have hfun : (Function.uncurry f ∘ fun θ : ℝ => (z, θ)) = fun θ => f z θ := rfl
      rwa [hfun] at h3
    exact hslice'.continuousOn.mono (fun θ hθ => hθbox θ hθ)
  refine ⟨hslice, ?_, ?_⟩
  -- ### 2. integrability of the squared slice on the compact interval
  · intro z hz
    exact ((hslice z hz).pow 2).integrableOn_compact isCompact_Icc
  -- ### 3. a.e. strong measurability of the radial function
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
      have hsub : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ)
          ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        refine ⟨?_, hθbox y hy⟩
        simp only [Set.mem_Ioi] at hx ⊢
        linarith
      have h : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
          (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
        have h' : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
            (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := (hsm.continuousOn.mono hsub).pow 2
        simpa only [Function.uncurry] using h'
      exact h
    have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict]
      have hmeas : MeasurableSet ((Set.Ioi (0 : ℝ)) ×ˢ Work.Spaces.Iθ) :=
        measurableSet_Ioi.prod measurableSet_Icc
      exact hcont.aestronglyMeasurable (μ := MeasureTheory.volume) hmeas
    exact haesm.integral_prod_right'

end Work.FTS.H2
