import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

namespace Work.Holonomy3

open MeasureTheory

set_option linter.unusedVariables false

/-- If `S ⊆ ℝ × (Fin d → ℝ)` has null `u`-fibres over the complement of a `torMeasure d`-null set
`N`, then `S` is null for the product of `volume.restrict (Icc 0 1)` with `torMeasure d`.

This is the Fubini/Tonelli computation for the situation of the paper: on the exceptional set `N`
the outer measure `torMeasure d` vanishes, while on its complement every fibre is assumed null. -/
theorem prod_measure_zero_of_fibers {d : ℕ} (N : Set (Fin d → ℝ)) (hN : MeasurableSet N)
    (hN0 : torMeasure d N = 0) (S : Set (ℝ × (Fin d → ℝ))) (hS : MeasurableSet S)
    (hfiber : ∀ s, s ∉ N →
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) {u : ℝ | (u, s) ∈ S} = 0) :
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).prod (torMeasure d)) S = 0 := by
  rw [MeasureTheory.Measure.prod_apply_symm hS]
  -- `N` has measure zero, so the exceptional set is negligible.
  have hae : ∀ᵐ s ∂(torMeasure d), s ∉ N := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hN0] with s hs
    simpa using hs
  -- Hence the integrand vanishes almost everywhere.
  have hcongr :
      (fun y => (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ((fun x => (x, y)) ⁻¹' S))
        =ᵐ[torMeasure d] (fun _ => 0) :=
    hae.mono (fun s hs => by
      show (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ((fun x => (x, s)) ⁻¹' S) = 0
      rw [show ((fun x => (x, s)) ⁻¹' S) = {u : ℝ | (u, s) ∈ S} from rfl]
      exact hfiber s hs)
  rw [MeasureTheory.lintegral_congr_ae hcongr]
  simp

end Work.Holonomy3
