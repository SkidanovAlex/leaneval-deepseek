import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- The primes in `[2, 11]` are exactly `2, 3, 5, 7, 11`. -/
private lemma primesUpToEleven : (Finset.Icc 2 11).filter Nat.Prime = ({2, 3, 5, 7, 11} : Finset ℕ) := by
  decide

/-- For `2 ≤ A` and `B ≤ 11` the reciprocal-prime sum over `[A,B]` is at most `3/2`; indeed the
primes `≤ 11` are `2,3,5,7,11` with reciprocal sum `< 3/2`. -/
theorem primesIn_small_sum_le (A B : ℝ) (hA : 2 ≤ A) (hB : B ≤ 11) :
    (∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ)) ≤ 3 / 2 := by
  have : (0 : ℝ) < A := by linarith
  -- Every element of `primesIn A B` lies in `{2, 3, 5, 7, 11}`.
  have hsub : Work.BMF.primesIn A B ⊆ ({2, 3, 5, 7, 11} : Finset ℕ) := by
    intro p hp
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨_hlo, hhi⟩, hprime⟩ := hp
    have hfloor : ⌊B⌋₊ ≤ 11 := by
      have := Nat.floor_mono hB
      simpa using this
    have h11 : p ≤ 11 := le_trans hhi hfloor
    have hp2 : 2 ≤ p := hprime.two_le
    have hmem : p ∈ (Finset.Icc 2 11).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp2, h11⟩, hprime⟩
    rwa [primesUpToEleven] at hmem
  calc ∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ 3 / 2 := by norm_num

end Work.BMF.mr_direct
