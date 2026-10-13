import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.aesm_uncurry_of_continuousOn_of_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set

/-- Indicator to a measurable set of an a.e. strongly measurable function (the a.e. statement
being relative to the restriction of the measure to that set) is a.e. strongly measurable for
the unrestricted measure. -/
private lemma aesm_indicator_of_aesm_restrict {A : Set ℝ} (hA : MeasurableSet A) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict A)) :
    AEStronglyMeasurable (A.indicator f) volume := by
  obtain ⟨h, hh, heq⟩ := hf
  refine ⟨A.indicator h, hh.indicator hA, ?_⟩
  have hnull : (volume.restrict A) {x : ℝ | f x ≠ h x} = 0 := ae_iff.mp heq
  rw [Filter.EventuallyEq, ae_iff]
  have hsub : {x : ℝ | ¬ (A.indicator f x = A.indicator h x)}
      ⊆ {x : ℝ | f x ≠ h x} ∩ A := by
    intro x hx
    change ¬ (A.indicator f x = A.indicator h x) at hx
    change f x ≠ h x ∧ x ∈ A
    by_cases hxA : x ∈ A
    · refine ⟨?_, hxA⟩
      intro hfh
      exact hx (by rw [Set.indicator_of_mem hxA f, Set.indicator_of_mem hxA h, hfh])
    · exact absurd (by rw [Set.indicator_of_notMem hxA f, Set.indicator_of_notMem hxA h]) hx
  exact measure_mono_null hsub (by rw [← Measure.restrict_apply' hA]; exact hnull)

/-- **Carathéodory measurability relative to a measurable `s`-set.**  If `g : ℝ → ℝ → ℝ → ℝ` is,
for every `s ∈ A`, continuous on the open quadrant and zero off it, and if for every `(z,θ)` the
map `s ↦ g s z θ` is a.e. strongly measurable for `volume.restrict A`, then `(s,z,θ) ↦ g s z θ`
is a.e. strongly measurable for `(volume.restrict A).prod volume`.  The proof truncates `g` to
`A` (which is Carathéodory on all of `ℝ`) and applies the unrestricted lemma
`aesm_uncurry_of_continuousOn_of_zero`, then uses that the restricted product measure is the
product measure of a measure supported on `A`. -/
theorem aesm_uncurry_restricted {A : Set ℝ} (hA : MeasurableSet A) {g : ℝ → ℝ → ℝ → ℝ}
    (hcont : ∀ s ∈ A, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ s ∈ A, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → g s q.1 q.2 = 0)
    (hmeas : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2)
      (MeasureTheory.volume.restrict A)) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume) := by
  classical
  -- truncate `g` to `A`: the resulting `g₁` is Carathéodory on all of `ℝ`
  set g₁ : ℝ → ℝ → ℝ → ℝ := fun s z θ => if s ∈ A then g s z θ else 0 with hg₁
  have hcont₁ : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g₁ s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro s
    by_cases hs : s ∈ A
    · refine (hcont s hs).congr ?_
      intro q _
      simp only [hg₁]
      rw [if_pos hs]
    · have hz : (fun q : ℝ × ℝ => g₁ s q.1 q.2) = fun _ => (0 : ℝ) := by
        funext q
        simp only [hg₁]
        rw [if_neg hs]
      rw [hz]
      exact continuousOn_const
  have hzero₁ : ∀ s : ℝ, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → g₁ s q.1 q.2 = 0 := by
    intro s q hq
    by_cases hs : s ∈ A
    · have hs' := hzero s hs q hq
      simp only [hg₁]
      rw [if_pos hs, hs']
    · simp only [hg₁]
      rw [if_neg hs]
  have hmeas₁ : ∀ q : ℝ × ℝ, AEStronglyMeasurable (fun s : ℝ => g₁ s q.1 q.2) volume := by
    intro q
    refine (aesm_indicator_of_aesm_restrict hA (hmeas q)).congr ?_
    filter_upwards with s
    simp only [hg₁, Set.indicator_apply]
  have hbig := aesm_uncurry_of_continuousOn_of_zero (g := g₁) hcont₁ hzero₁ hmeas₁
  -- the restricted product measure is supported on `A ×ˢ univ`
  have haeA : ∀ᵐ p ∂((volume.restrict A).prod (volume : Measure (ℝ × ℝ))), p.1 ∈ A := by
    rw [ae_iff]
    have hset : {p : ℝ × (ℝ × ℝ) | ¬ p.1 ∈ A} = Prod.fst ⁻¹' Aᶜ := by
      ext p; simp
    rw [hset]
    have hmap : Measure.map (Prod.fst : ℝ × (ℝ × ℝ) → ℝ)
          (((volume.restrict A).prod (volume : Measure (ℝ × ℝ))))
        = (volume Set.univ) • (volume.restrict A) :=
      Measure.map_fst_prod (μ := volume.restrict A) (ν := (volume : Measure (ℝ × ℝ)))
    have h := Measure.map_apply (μ := (volume.restrict A).prod (volume : Measure (ℝ × ℝ)))
      (f := (Prod.fst : ℝ × (ℝ × ℝ) → ℝ))
      (measurable_fst : Measurable (Prod.fst : ℝ × (ℝ × ℝ) → ℝ)) hA.compl
    rw [hmap, Measure.smul_apply, Measure.restrict_apply' hA] at h
    simp only [Set.compl_inter_self, measure_empty, smul_zero] at h
    exact h.symm
  have hle : ((volume.restrict A).prod (volume : Measure (ℝ × ℝ)))
      ≤ (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  refine (hbig.mono_measure hle).congr ?_
  filter_upwards [haeA] with p hp
  simp only [hg₁]
  rw [if_pos hp]

end Work.FTS.EpsEngine
