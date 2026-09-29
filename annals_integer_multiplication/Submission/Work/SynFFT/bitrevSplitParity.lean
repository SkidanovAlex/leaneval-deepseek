import Mathlib
import Submission.Work.SynFFT.defs
import Submission.Work.SynFFT.bitrevRec

/-!
# Splitting off the low bit of a bit reversal

`bitrev k n` reverses the low `k` bits of `n`.  Reversing one more bit places the (new) low bit
of `b` at the top, and reverses the remaining bits below it:

`bitrev (k+1) b = (b % 2) * 2^k + bitrev k (b / 2)`.

This is the mirror image of `Work.SynFFT.bitrevRec` (which peels the low bit of `b` off on the
input side); the two cases `b = 2*n` and `b = 2*n+1` are exactly the two recursions there.
-/

set_option autoImplicit false

namespace Work.SynFFT

/-- Reversing `k+1` bits of `b`: the low bit of `b` becomes the top bit `2^k`, and the remaining
`k` bits are reversed below it. -/
theorem bitrevSplitParity (k b : ℕ) : bitrev (k + 1) b = (b % 2) * 2 ^ k + bitrev k (b / 2) := by
  obtain h | h := Nat.mod_two_eq_zero_or_one b
  · obtain ⟨n, rfl⟩ : ∃ n, b = 2 * n := ⟨b / 2, by omega⟩
    simp [bitrev_succ_two_mul]
  · obtain ⟨n, rfl⟩ : ∃ n, b = 2 * n + 1 := ⟨b / 2, by omega⟩
    have hd : (2 * n + 1) / 2 = n := by omega
    rw [hd, bitrev_succ_two_mul_add_one, h]
    ring

end Work.SynFFT
