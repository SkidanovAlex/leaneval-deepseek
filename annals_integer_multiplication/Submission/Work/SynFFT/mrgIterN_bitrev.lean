import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgS
import Submission.Work.SynFFT.bitrevSplitParity
import Submission.Work.SynFFT.mrgSArith

/-!
# The interleave passes of the synthetic FFT compose to a bit reversal

`mrgIterN r k` is the composition of the `k` interleave ("merge") passes of scales
`1, 2, …, 2^{k-1}` of the slice word (`Submission/Work/SynFFT/kit2.lean`).  Its index map at level
`k` is the map `mrgS (2^k)`, and the point of `Work.SynFFT.MrgBitrevProp` is that the whole
composition *is* the bit-reversal permutation: it undoes the bit reversal of the in-place DIF
scheme, so that the slice word produces the 1-D transform in natural order.

The index computation is the following.  Write `p = A * 2^{k+1} + b` with `b < 2^{k+1}`.  One
pass of scale `2^k` sends the offset `b` to `b / 2 + (b % 2) * 2^k` (keeping the high part
`A * 2^{k+1}`, see `mrgSArith`), i.e. it moves the low bit of `b` to the top of the block and
shifts the rest down — precisely the recursion `bitrev (k+1) b = (b % 2) * 2^k + bitrev k (b/2)`
of `bitrevSplitParity`.  Induction on `k` gives that `k` passes act as `bitrev k` on the offset,
and restricted to a single block (`A = 0`, i.e. `p < 2^k`) that is the bit reversal itself.

The main lemma below is therefore the block statement

`mrgIterN r k u p = u (p / 2 ^ k * 2 ^ k + bitrev k (p % 2 ^ k))`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- One interleave pass of scale `s`, read at a position: `mrgN` applies `mrgS s` to the index. -/
lemma mrgN_apply (r s : ℕ) (u : Arr r) (p : ℕ) : mrgN r s u p = u (mrgS s p) := rfl

/-- Unfolding `mrgIterN` at a successor: the pass of scale `2^k` acts on the index first. -/
lemma mrgIterN_succ (r k : ℕ) (u : Arr r) (p : ℕ) :
    mrgIterN r (k + 1) u p = mrgIterN r k u (mrgS (2 ^ k) p) := rfl

/-- **The index map of `k` interleave passes.**  `mrgIterN r k` preserves each block of `2^k`
consecutive positions and, inside a block, acts on the offset by the bit reversal of the low
`k` bits. -/
theorem mrgIterN_getD (r k : ℕ) (u : Arr r) (p : ℕ) :
    mrgIterN r k u p = u (p / 2 ^ k * 2 ^ k + bitrev k (p % 2 ^ k)) := by
  induction k generalizing p with
  | zero =>
      simp [mrgIterN, bitrev]
  | succ k ih =>
      -- the pass of scale `2^k` sends `p` to `mrgS (2^k) p`, whose block and offset are computed
      -- by `mrgSArith`; the offset of the image is `(p % 2^{k+1}) / 2` with block `2 A + p % 2`.
      rw [mrgIterN_succ, ih]
      obtain ⟨h1, h2⟩ := mrgSArith k p
      rw [h1, h2]
      -- `bitrev (k+1) b = (b % 2) * 2^k + bitrev k (b / 2)`, and `b % 2 = p % 2` as `2 ∣ 2^{k+1}`
      rw [bitrevSplitParity k (p % 2 ^ (k + 1))]
      have hmod : p % 2 ^ (k + 1) % 2 = p % 2 :=
        Nat.mod_mod_of_dvd p ⟨2 ^ k, by rw [pow_succ']⟩
      rw [hmod]
      -- `(2 A + p % 2) * 2^k = A * 2^{k+1} + (p % 2) * 2^k`
      have key : (2 * (p / 2 ^ (k + 1)) + p % 2) * 2 ^ k
          = p / 2 ^ (k + 1) * 2 ^ (k + 1) + p % 2 * 2 ^ k := by
        rw [pow_succ']; ring
      rw [key, Nat.add_assoc]

/-- On a single block of `2^k` positions, `k` interleave passes are exactly the bit reversal of
the offset. -/
theorem mrgIterN_block (r k a : ℕ) (u : Arr r) (p : ℕ) (hp : p < 2 ^ k) :
    mrgIterN r k u (a * 2 ^ k + p) = u (a * 2 ^ k + bitrev k p) := by
  rw [mrgIterN_getD]
  have h1 : (a * 2 ^ k + p) / 2 ^ k = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hp, Nat.zero_add]
  have h2 : (a * 2 ^ k + p) % 2 ^ k = p := by
    rw [Nat.add_comm, Nat.mul_comm a (2 ^ k), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
  rw [h1, h2]

/-- **The interleave passes of the slice word compose to the bit-reversal permutation.** -/
theorem mrgIterN_bitrev : Work.SynFFT.MrgBitrevProp := by
  intro r k u p hp
  rw [mrgIterN_getD r k u p, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
  simp

end Work.SynFFT
