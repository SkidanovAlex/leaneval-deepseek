import Mathlib
import Submission.Mostow.Interfaces

/-!
# Shared measure-theoretic helper for the natural-map areas (N1, N2, N3)

For `φ` a continuous bijection of `Sph n` and `u : E n`, the pushforward
`ν = (visual n u).map φ` is again a probability measure carried by `Sph n`; it has no atoms
because `φ` is injective on `Sph n` and `visual n u` has none; and `φ` is a.e.-measurable for
`visual n u` (this last fact is what makes `Measure.map_map` / `AEMeasurable.map_map_of_aemeasurable`
applicable in the equivariance and Jacobian arguments).

The three measure conditions collected here are exactly the side conditions that `BaryProp`
requires of `ν`, so they are what lets one apply the barycentre equivariance
`bar (ν.map (bd g)) = g • bar ν`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- A function continuous on a set `s` is a.e.-measurable for any measure whose mass all lies
on `s`. (The proof glues `f` to a constant outside `s`, which stays continuous on `sᶜ`.) -/
lemma aemeasurable_of_continuousOn_of_compl_eq_zero {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : α → β} {s : Set α} {μ : Measure α} (b : β) (hs : MeasurableSet s)
    (hf : ContinuousOn f s) (hμ : μ sᶜ = 0) : AEMeasurable f μ := by
  classical
  have hpiece : Measurable (s.piecewise f fun _ => b) :=
    hf.measurable_piecewise continuousOn_const hs
  have hmem : ∀ᵐ x ∂μ, x ∈ s := by
    rw [ae_iff]
    simpa only [Set.compl_def] using hμ
  have hae : (s.piecewise f fun _ => b) =ᵐ[μ] f :=
    hmem.mono fun x hx => by simp only [Set.piecewise_eq_of_mem _ _ _ hx]
  exact hpiece.aemeasurable.congr hae

/-- The pushforward of a visual measure by a continuous bijection of the sphere is again a
probability measure on the sphere, atomless, and the map is a.e.-measurable. -/
lemma natMeasure_good (n : ℕ) (hV : VisualProp n) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n)) (u : E n) :
    IsProbabilityMeasure ((visual n u).map φ) ∧ ((visual n u).map φ) (Sph n)ᶜ = 0 ∧
    (∀ ξ, ((visual n u).map φ) {ξ} = 0) ∧ AEMeasurable φ (visual n u) := by
  have hprob : IsProbabilityMeasure (visual n u) := (hV u).1
  have hsupp : visual n u (Sph n)ᶜ = 0 := (hV u).2.1
  have hatom : ∀ ξ, visual n u {ξ} = 0 := (hV u).2.2.1
  have hSph : MeasurableSet (Sph n) := Metric.isClosed_sphere.measurableSet
  have hae : AEMeasurable φ (visual n u) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : E n) hSph hcont hsupp
  refine ⟨inferInstance, ?_, ?_, hae⟩
  · -- the pushforward is still carried by the sphere: `φ` maps `Sph n` into `Sph n`
    rw [Measure.map_apply_of_aemeasurable hae hSph.compl]
    refine le_antisymm ?_ zero_le
    calc visual n u (φ ⁻¹' (Sph n)ᶜ) ≤ visual n u ((Sph n)ᶜ) := by
          apply measure_mono
          intro x hx
          exact fun hxs => hx (hbij.1 hxs)
      _ = 0 := hsupp
  · -- no atoms: the fibre of `ξ` meets the sphere in at most one point
    intro ξ
    rw [Measure.map_apply_of_aemeasurable hae (measurableSet_singleton ξ)]
    have hsplit : φ ⁻¹' {ξ} = (φ ⁻¹' {ξ} ∩ Sph n) ∪ (φ ⁻¹' {ξ} ∩ (Sph n)ᶜ) := by
      ext x
      constructor
      · intro hx
        by_cases h : x ∈ Sph n
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    have hsub : (φ ⁻¹' {ξ} ∩ Sph n).Subsingleton := by
      intro x hx y hy
      exact hbij.2.1 hx.2 hy.2 (by rw [hx.1, hy.1])
    have hm1 : visual n u (φ ⁻¹' {ξ} ∩ Sph n) = 0 := by
      rcases hsub.eq_empty_or_singleton with h | ⟨z, hz⟩
      · rw [h, measure_empty]
      · rw [hz, hatom z]
    have hm2 : visual n u (φ ⁻¹' {ξ} ∩ (Sph n)ᶜ) = 0 := by
      refine le_antisymm ?_ zero_le
      calc visual n u (φ ⁻¹' {ξ} ∩ (Sph n)ᶜ) ≤ visual n u ((Sph n)ᶜ) :=
            measure_mono Set.inter_subset_right
        _ = 0 := hsupp
    rw [hsplit]
    refine le_antisymm ?_ zero_le
    calc visual n u ((φ ⁻¹' {ξ} ∩ Sph n) ∪ (φ ⁻¹' {ξ} ∩ (Sph n)ᶜ))
        ≤ visual n u (φ ⁻¹' {ξ} ∩ Sph n) + visual n u (φ ⁻¹' {ξ} ∩ (Sph n)ᶜ) :=
          measure_union_le _ _
      _ = 0 := by rw [hm1, hm2, add_zero]

end Work.Mostow
