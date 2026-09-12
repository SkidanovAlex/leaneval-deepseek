import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

namespace Commons.Nat.Card

open Finset
open scoped BigOperators

/-- If the sum of the squares of the coordinates of a real vector `v : Fin m → ℝ` is at most
`η²·r` (η ≥ 0), then at most `r` of its coordinates have absolute value larger than `η`.
This is the counting step behind the tensorization lemma (Tikhomirov 2020, Lemma 2.2(2)):
a vector whose ℓ₂-norm is at most `η·√r` has at most `r` coordinates above `η` in absolute value. -/
theorem big_coords_le {m r : ℕ} (v : Fin m → ℝ) {η : ℝ} (hη0 : 0 ≤ η)
    (h : (∑ i : Fin m, (v i) ^ 2) ≤ η ^ 2 * (r : ℝ)) :
    ((univ : Finset (Fin m)).filter (fun i : Fin m => η < |v i|)).card ≤ r := by
  by_cases hη0' : η = 0
  · -- η = 0: the hypothesis forces every coordinate to vanish, so the set is empty.
    have hsum0 : (∑ i : Fin m, (v i) ^ 2) = 0 := by
      apply le_antisymm
      · simpa [hη0'] using h
      · exact sum_nonneg (fun i _hi => sq_nonneg (v i))
    have hv0 : ∀ i : Fin m, v i = 0 := by
      intro i
      have hi0 : (v i) ^ 2 = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg (s := (univ : Finset (Fin m)))
          (f := fun j : Fin m => (v j) ^ 2) (fun j _hj => sq_nonneg (v j))).mp hsum0 i (mem_univ i)
      exact sq_eq_zero_iff.mp hi0
    have hB : ((univ : Finset (Fin m)).filter (fun i : Fin m => η < |v i|)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _hi
      simp [hη0', hv0 i]
    rw [hB]
    simp
  · -- η ≠ 0 (and η ≥ 0), so η > 0.
    have hηpos : 0 < η := lt_of_le_of_ne hη0 (Ne.symm hη0')
    let B : Finset (Fin m) := (univ : Finset (Fin m)).filter (fun i : Fin m => η < |v i|)
    change B.card ≤ r
    -- Upper bound: the contribution of B to the sum of squares is at most the whole sum.
    have hsub : (∑ i ∈ B, (v i) ^ 2) ≤ ∑ i : Fin m, (v i) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun i _hi _hnot => sq_nonneg (v i))
    -- Lower bound: on B, every square is at least η².
    have hterm : ∀ i : Fin m, i ∈ B → η ^ 2 ≤ (v i) ^ 2 := by
      intro i hiB
      have hiη : η < |v i| := (mem_filter.mp hiB).2
      have hsq : η ^ 2 ≤ |v i| ^ 2 := by nlinarith
      rwa [sq_abs] at hsq
    have hlow1 : (∑ i ∈ B, η ^ 2) ≤ ∑ i ∈ B, (v i) ^ 2 := by
      exact Finset.sum_le_sum hterm
    have hlow2 : (B.card : ℝ) * η ^ 2 ≤ ∑ i ∈ B, (v i) ^ 2 := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hlow1
    have hchain : (B.card : ℝ) * η ^ 2 ≤ η ^ 2 * (r : ℝ) := by
      exact le_trans hlow2 (le_trans hsub h)
    have hη2pos : 0 < η ^ 2 := sq_pos_of_pos hηpos
    have hcard : (B.card : ℝ) ≤ (r : ℝ) := by nlinarith
    exact_mod_cast hcard

end Commons.Nat.Card