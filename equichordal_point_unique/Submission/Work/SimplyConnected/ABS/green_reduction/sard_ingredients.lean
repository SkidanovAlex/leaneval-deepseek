import Mathlib

/-!
# Ingredients of the two-variable Sard lemma

`NOTES_s25_engulfing_and_sard_crux.md` records that the deliverable
`green_reduction.exists_barrier_regular_precompact_region` follows from a level of the smooth
exhaustion function of `X` that is not a critical value, i.e. from *Sard's lemma for a `C^∞`
function of two real variables*, which is absent from Mathlib (`Work.CriticalSet` supplies the
harmonic case only).  This module collects the elementary ingredients of a self-contained proof of
the quantitative form of that statement, in the formulation
`le_sum_length_of_Icc_subset_iUnion` below.
-/

open scoped Topology
open Set MeasureTheory

namespace Work.SimplyConnected.ABS

/-- **The elementary covering-length lemma.**  A finite cover of an interval by intervals has total
length at least the length of the interval.  (Proved via Lebesgue measure, which is the shortest
route in Mathlib.) -/
theorem le_sum_length_of_Icc_subset_iUnion {a b : ℝ} {ι : Type*} [Fintype ι] {l u : ι → ℝ}
    (hlu : ∀ i, l i ≤ u i) (h : Set.Icc a b ⊆ ⋃ i, Set.Icc (l i) (u i)) :
    b - a ≤ ∑ i, (u i - l i) := by
  have hmono : volume (Set.Icc a b) ≤ volume (⋃ i, Set.Icc (l i) (u i)) := measure_mono h
  have hunion : volume (⋃ i, Set.Icc (l i) (u i)) ≤ ∑ i, volume (Set.Icc (l i) (u i)) :=
    measure_iUnion_fintype_le volume _
  rw [Real.volume_Icc] at hmono
  have hsum : (∑ i, volume (Set.Icc (l i) (u i))) = ENNReal.ofReal (∑ i, (u i - l i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hlu i))]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.volume_Icc]
  rw [hsum] at hunion
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hlu i))]
  exact hmono.trans hunion

end Work.SimplyConnected.ABS
