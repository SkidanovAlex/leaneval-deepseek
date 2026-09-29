import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.chunks

open Work.Main

/-- The cyclic correlation of the padded chunk sequences equals the (linear) coefficient
`hcoeff`: averaging over the cyclic group `ℤ/S` with `S ≥ 2N-1` recovers the truncated
convolution. Only the `i < N` terms survive on the left (padding), and for those
`(m + S - i) % S` is `m - i` when `i ≤ m` and a value `≥ N` (hence a zero chunk) otherwise. -/
theorem sum_cyclic_eq_hcoeff {x y b N S m : ℕ} (hSN : 2 * N - 1 ≤ S) (hm : m < S) :
    (∑ i ∈ Finset.range S, pchunk x b N i * pchunk y b N ((m + S - i) % S)) = hcoeff x y b N m := by
  have hNS : N ≤ S := by omega
  -- terms with `N ≤ i` vanish, so the sum over `range S` restricts to `range N`
  have hzero : ∀ i ∈ Finset.range S, i ∉ Finset.range N →
      pchunk x b N i * pchunk y b N ((m + S - i) % S) = 0 := by
    intro i _ hiN
    have hi : N ≤ i := by simpa using hiN
    rw [pchunk]
    simp [Nat.not_lt.mpr hi]
  have hswap : (∑ i ∈ Finset.range S, pchunk x b N i * pchunk y b N ((m + S - i) % S))
      = ∑ i ∈ Finset.range N, pchunk x b N i * pchunk y b N ((m + S - i) % S) :=
    (Finset.sum_subset (Finset.range_subset_range.mpr hNS) hzero).symm
  rw [hswap, hcoeff]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  by_cases hle : i ≤ m
  · -- then `(m + S - i) % S = m - i`
    have hms : m + S - i = (m - i) + S := by omega
    have hmod : (m + S - i) % S = m - i := by
      rw [hms, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, if_pos hle]
  · -- then `(m + S - i) % S ≥ N`, so the `y`-chunk is the padding zero
    have hmod : (m + S - i) % S = m + S - i := by
      rw [Nat.mod_eq_of_lt (by omega)]
    have hge : N ≤ m + S - i := by omega
    rw [hmod, if_neg hle]
    have hz : pchunk y b N (m + S - i) = 0 := by
      rw [pchunk]
      simp [Nat.not_lt.mpr hge]
    rw [hz, mul_zero]

end Work.Main.chunks
