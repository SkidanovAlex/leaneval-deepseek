import Mathlib
import Submission.Work.Drive.Mono.oneEvBad_null3
import Submission.Work.Drive.Mono.OneEventNDDefs

/-!
# `Work.Drive.Mono.ae_oneEvBad_slice_null`

The bad set of "one event per level" is null in `(u, h, τ)` (`Work.Drive.Mono.oneEvBad_null3`);
here we read it as a statement about the cutting level `u`: for almost every `u` the
`(h, τ)`-slice of the bad set is null.

The mathematical content is Fubini for a null set of `ℝ × (ℝ × ℝ)`: a null set has a.e. null
slices, with no measurability hypothesis on the set
(`MeasureTheory.Measure.measure_ae_null_of_prod_null`).  This is the form in which the
producers consume the statement (`Submission/Work/Drive/Mono/NOTES_LEAD_LD_interface.md` §5,
`ae_all_iff` over the countable family of members).
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal RealInnerProductSpace

namespace Work.Drive.Mono

noncomputable section

/-- **Slicing a null set**: for a set `S ⊆ ℝ × (ℝ × ℝ)` of Lebesgue measure zero, almost every
slice `u ↦ {y | (u, y) ∈ S}` is Lebesgue-null.  The set `S` need not be measurable. -/
theorem ae_volume_slice_null_of_volume_null {S : Set (ℝ × ℝ × ℝ)}
    (h : MeasureTheory.volume S = 0) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      MeasureTheory.volume {y : ℝ × ℝ | (u, (y.1, y.2)) ∈ S} = 0 := by
  rw [MeasureTheory.Measure.volume_eq_prod] at h
  have hslice := MeasureTheory.Measure.measure_ae_null_of_prod_null h
  filter_upwards [hslice] with u hu
  simpa [Set.preimage] using hu

theorem ae_oneEvBad_slice_null (ψ : Submission.Diffeo) {s : ℝ}
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1)
    (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0)
    (hvb : inner ℝ v b₀ = 0) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      MeasureTheory.volume {y : ℝ × ℝ |
        Work.Drive.Mono.OneEvBad ψ s c σ v a₀ b₀ u y.1 y.2} = 0 := by
  have h3 := oneEvBad_null3 ψ s c σ v a₀ b₀ hv ha hb hab hva hvb
  filter_upwards [ae_volume_slice_null_of_volume_null h3] with u hu
  simpa using hu

end

end Work.Drive.Mono
