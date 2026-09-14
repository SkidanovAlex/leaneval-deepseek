import Mathlib
import Submission.Commons.Data.Fin.pairFilter_snd
import Submission.Commons.Data.Fin.pairFilter_fst

namespace Commons.Data.Fin

open scoped BigOperators
set_option autoImplicit false

lemma pairSum_k_partition {N : ℕ} {α : Type*} [AddCommMonoid α] (k : Fin N) (f : Fin N → Fin N → α) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), f p.1 p.2) =
      (∑ i ∈ Finset.Iio k, f i k) + (∑ j ∈ Finset.Ioi k, f k j) +
        ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).filter
          (fun p => p.1 ≠ k ∧ p.2 ≠ k), f p.1 p.2 := by
  classical
  let M : Finset (Fin N × Fin N) := Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)
  -- Within M (i.e. under `p.1 < p.2`), fixing the first coordinate to `k` already
  -- forces the second coordinate to differ from `k`.
  have hB1 : (M.filter (fun p => p.2 ≠ k)).filter (fun p => p.1 = k) =
      M.filter (fun p => p.1 = k) := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩
    · intro hp
      have hpM : p ∈ M := (Finset.mem_filter.mp hp).1
      have hpk : p.1 = k := (Finset.mem_filter.mp hp).2
      have hlt : p.1 < p.2 := by
        have h := (Finset.mem_filter.mp hpM).2
        simpa [M] using h
      have hp2ne : p.2 ≠ k := by
        intro hpk2
        rw [hpk, hpk2] at hlt
        exact (lt_irrefl k) hlt
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpM, hp2ne⟩, hpk⟩
  -- Filtering twice (first `p.2 ≠ k`, then `p.1 ≠ k`) is the same as filtering once
  -- by the conjunction.
  have hB2 : (M.filter (fun p => p.2 ≠ k)).filter (fun p => p.1 ≠ k) =
      M.filter (fun p => p.1 ≠ k ∧ p.2 ≠ k) := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
          ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2⟩⟩
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.2⟩,
          (Finset.mem_filter.mp hp).2.1⟩
  calc
    (∑ p ∈ M, f p.1 p.2)
        = (∑ p ∈ M.filter (fun p => p.2 = k), f p.1 p.2)
          + (∑ p ∈ M.filter (fun p => p.2 ≠ k), f p.1 p.2) := by
          exact (Finset.sum_filter_add_sum_filter_not M (fun p : Fin N × Fin N => p.2 = k)
            (fun p => f p.1 p.2)).symm
    _ = (∑ p ∈ M.filter (fun p => p.2 = k), f p.1 p.2)
          + ((∑ p ∈ (M.filter (fun p => p.2 ≠ k)).filter (fun p => p.1 = k), f p.1 p.2)
             + (∑ p ∈ (M.filter (fun p => p.2 ≠ k)).filter (fun p => p.1 ≠ k), f p.1 p.2)) := by
          exact congrArg (fun t => (∑ p ∈ M.filter (fun p => p.2 = k), f p.1 p.2) + t)
            ((Finset.sum_filter_add_sum_filter_not (M.filter (fun p : Fin N × Fin N => p.2 ≠ k))
              (fun p : Fin N × Fin N => p.1 = k) (fun p : Fin N × Fin N => f p.1 p.2)).symm)
    _ = (∑ p ∈ M.filter (fun p => p.2 = k), f p.1 p.2)
          + ((∑ p ∈ M.filter (fun p => p.1 = k), f p.1 p.2)
             + (∑ p ∈ M.filter (fun p => p.1 ≠ k ∧ p.2 ≠ k), f p.1 p.2)) := by
          rw [hB1, hB2]
    _ = (∑ i ∈ Finset.Iio k, f i k) + ((∑ j ∈ Finset.Ioi k, f k j)
          + (∑ p ∈ M.filter (fun p => p.1 ≠ k ∧ p.2 ≠ k), f p.1 p.2)) := by
          rw [pairFilter_snd k f, pairFilter_fst k f]
    _ = (∑ i ∈ Finset.Iio k, f i k) + (∑ j ∈ Finset.Ioi k, f k j)
          + (∑ p ∈ M.filter (fun p => p.1 ≠ k ∧ p.2 ≠ k), f p.1 p.2) := by
          rw [← add_assoc]

end Commons.Data.Fin
