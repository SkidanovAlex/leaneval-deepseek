import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.CompletePartialOrder

namespace Commons.MeasureTheory

open Set Filter
open scoped ENNReal

theorem tail_blocks_le_measure_limsup {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (s : ℕ → Set α) (hs : ∀ n, MeasureTheory.NullMeasurableSet (s n) μ)
    {c : ℝ≥0∞} (hc : 0 < c)
    (hblock : ∀ N : ℕ, ∃ Y : ℕ, N < Y ∧ c ≤ μ (⋃ n ∈ Finset.Icc N Y, s n)) :
    c ≤ μ (limsup s atTop) := by
  let t : ℕ → Set α := fun N => ⋃ n ≥ N, s n
  have ht_mem (N : ℕ) (x : α) : x ∈ t N ↔ ∃ n : ℕ, N ≤ n ∧ x ∈ s n := by
    simp [t]
  have ht_anti : Antitone t := by
    intro N M hNM x hx
    rw [ht_mem] at hx ⊢
    rcases hx with ⟨n, hMn, hsn⟩
    exact ⟨n, le_trans hNM hMn, hsn⟩
  have ht_null : ∀ N : ℕ, MeasureTheory.NullMeasurableSet (t N) μ := by
    intro N
    have heq : t N = ⋃ n : {m : ℕ // N ≤ m}, s (n : ℕ) := by
      ext x
      simp [t]
    rw [heq]
    exact MeasureTheory.NullMeasurableSet.iUnion (fun n : {m : ℕ // N ≤ m} => hs (n : ℕ))
  have hlim : (⋂ N : ℕ, t N) = limsup s atTop := by
    ext x
    rw [limsup_eq_iInf_iSup_of_nat]
    simp [t]
  have hsubset (N Y : ℕ) : (⋃ n ∈ Finset.Icc N Y, s n) ⊆ t N := by
    intro x hx
    rw [ht_mem N x]
    simp at hx
    rcases hx with ⟨n, hn, hsn⟩
    exact ⟨n, hn.1, hsn⟩
  have hc_le_t : ∀ N : ℕ, c ≤ μ (t N) := by
    intro N
    rcases hblock N with ⟨Y, _hNY, hblockN⟩
    exact le_trans hblockN (MeasureTheory.measure_mono (hsubset N Y))
  calc
    c ≤ ⨅ N : ℕ, μ (t N) := le_iInf hc_le_t
    _ = μ (⋂ N : ℕ, t N) := by
      exact (ht_anti.measure_iInter ht_null ⟨0, MeasureTheory.measure_ne_top μ (t 0)⟩).symm
    _ = μ (limsup s atTop) := by rw [hlim]

end Commons.MeasureTheory