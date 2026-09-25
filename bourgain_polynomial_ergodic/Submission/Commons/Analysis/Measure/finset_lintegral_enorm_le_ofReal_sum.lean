import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Measure

/-- For a finite family of `IntegrableOn` functions `g i` on a set `S`, the sum of the
`lintegral`s of the (extended) norms is exactly `ofReal` of the sum of the Bochner integrals of
the norms.  In particular it is bounded by the latter. -/
lemma finset_lintegral_enorm_le_ofReal_sum {ι H : Type*} [NormedAddCommGroup H] (s : Finset ι) (g : ι → ℝ → H) (S : Set ℝ) (hg : ∀ i ∈ s, MeasureTheory.IntegrableOn (g i) S MeasureTheory.volume) : ∑ i ∈ s, MeasureTheory.lintegral (MeasureTheory.volume.restrict S) (fun x => enorm (g i x)) ≤ ENNReal.ofReal (∑ i ∈ s, MeasureTheory.integral (MeasureTheory.volume.restrict S) (fun x => ‖g i x‖)) := by
  have h_eq : ∀ i ∈ s,
      MeasureTheory.lintegral (MeasureTheory.volume.restrict S) (fun x => enorm (g i x))
        = ENNReal.ofReal (MeasureTheory.integral (MeasureTheory.volume.restrict S)
            (fun x => ‖g i x‖)) := by
    intro i hi
    exact (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hg i hi)).symm
  rw [Finset.sum_congr rfl h_eq, ENNReal.ofReal_sum_of_nonneg]
  intro i hi
  exact MeasureTheory.integral_nonneg fun x => norm_nonneg _

end Commons.Analysis.Measure