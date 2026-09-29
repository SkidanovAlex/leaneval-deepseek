import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.bitrevLib

set_option autoImplicit false

namespace Work.SynFFT

/-- The low `j` bits of `bitrev k p` are the first `j` reversed bits of `p`:
the `i`-th bit of `bitrev k p` (for `i < j ≤ k`) is the `(k-1-i)`-th bit of `p`. -/
theorem bitrevMod :
    ∀ (k j p : ℕ), j ≤ k → p < 2 ^ k →
      (∑ i ∈ Finset.range j,
          (if p % 2 ^ (k - i) ≥ 2 ^ (k - i - 1) then 1 else 0) * 2 ^ i) = bitrev k p % 2 ^ j := by
  intro k j p hjk hp
  rw [bitrev_eq_bitsum]
  rw [bitsum_mod (fun j => p / 2 ^ (k - 1 - j) % 2) (fun i => by
        have := Nat.mod_lt (p / 2 ^ (k - 1 - i)) (show 0 < 2 by norm_num); omega) hjk]
  rw [bitsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : k - i - 1 = k - 1 - i := by omega
  have h2 : k - i = (k - 1 - i) + 1 := by omega
  rw [h1, h2, ← nat_bit_iff p (k - 1 - i)]

end Work.SynFFT
