import Mathlib
import Submission.Work.SynFFT.mrgS

/-!
# Arithmetic of the interleave index map

`mrgS s p = p / (2s) * (2s) + (p / 2 % s) + (p % 2) * s` moves the position `p` of a block of
`2s` consecutive indices: inside each block the element `2j + ε` is filled from `j + ε * s`.
For the FFT we only ever use the scale `s = 2 ^ k`, and the two facts needed are that dividing
(resp. taking the remainder mod) `2 ^ k` of `mrgS (2 ^ k) p` are the binary "even part" and
"odd part" of `p / 2` at scale `k`.  Both are instances of the general scale-`s` statement
`mrgS_general` proved below.
-/

namespace Work.SynFFT

/-- For any positive scale `n`, the interleave map `mrgS n` is affine on blocks of length `n`:
dividing by `n` recovers the block number together with the parity of the position, and the
remainder is the position's floor-halved offset inside the `2n`-block. -/
lemma mrgS_general {n p : ℕ} (hn : 0 < n) :
    mrgS n p / n = 2 * (p / (2 * n)) + p % 2 ∧
    mrgS n p % n = (p % (2 * n)) / 2 := by
  -- write `p = q * (2n) + r`: decompose `p` into its `2n`-block number `q` and offset `r`.
  set q := p / (2 * n) with hq
  set r := p % (2 * n) with hr
  have hp : p = 2 * n * q + r := by
    rw [hq, hr]
    exact (Nat.div_add_mod p (2 * n)).symm
  have hrlt : r < 2 * n := by rw [hr]; exact Nat.mod_lt _ (by omega)
  have hr2 : r / 2 < n := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
    omega
  -- halving: `p / 2 = n * q + r / 2`
  have hdiv2 : p / 2 = n * q + r / 2 := by
    rw [hp]
    have h1 : 2 * n * q + r = r + 2 * (n * q) := by ring
    rw [h1, Nat.add_mul_div_left r (n * q) (by norm_num : 0 < 2)]
    ring
  -- the low half of `p / 2` is the low bit of `r`, and the parity of `p` is that of `r`
  have hmod2 : p / 2 % n = r / 2 := by
    rw [hdiv2]
    have h1 : n * q + r / 2 = r / 2 + n * q := by ring
    rw [h1, Nat.add_mul_mod_self_left (r / 2) n q, Nat.mod_eq_of_lt hr2]
  have hpmod2 : p % 2 = r % 2 := by
    rw [hp]
    have h1 : 2 * n * q + r = r + 2 * (n * q) := by ring
    rw [h1, Nat.add_mul_mod_self_left r 2 (n * q)]
  -- hence `mrgS n p = (2q + r % 2) * n + r / 2`
  have hmain : mrgS n p = (2 * q + r % 2) * n + r / 2 := by
    rw [mrgS, hmod2, hpmod2]
    ring
  constructor
  · rw [hmain, hq, hpmod2]
    have h1 : (2 * q + r % 2) * n + r / 2 = r / 2 + n * (2 * q + r % 2) := by ring
    rw [h1, Nat.add_mul_div_left (r / 2) (2 * q + r % 2) hn, Nat.div_eq_of_lt hr2]
    ring
  · rw [hmain, hq]
    have h1 : (2 * q + r % 2) * n + r / 2 = r / 2 + n * (2 * q + r % 2) := by ring
    rw [h1, Nat.add_mul_mod_self_left (r / 2) n (2 * q + r % 2), Nat.mod_eq_of_lt hr2]

theorem mrgSArith (k p : ℕ) :
    mrgS (2 ^ k) p / 2 ^ k = 2 * (p / 2 ^ (k + 1)) + p % 2 ∧
    mrgS (2 ^ k) p % 2 ^ k = (p % 2 ^ (k + 1)) / 2 := by
  have h := mrgS_general (n := 2 ^ k) (p := p) (by positivity)
  have h2 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  rwa [h2] at h

end Work.SynFFT
