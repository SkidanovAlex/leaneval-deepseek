import Mathlib
import Submission.Work.MainP.basic
import Submission.Work.MainP.rpBound

namespace Work.MainP

/-- **Conjunct 1 of `PolyFacts`** (`3 d p² < T`): with `b = bpar n ≥ 2^61`,
`T = Tpar n`, `p = ppar n = 6b`, `d = D = 1729`, the hypothesis `4n ≤ T b` together with
`b^10 ≤ n` (`Work.MainP.bpow10_le_n`) gives `T ≥ 4b^9 ≥ 4·5^7 b^2 > 186732 b^2 = 3d p^2`. -/
theorem pSq_lt_Tpar (n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n)
    (h4n : 4 * n ≤ HvdH.Tpar n * HvdH.bpar n) :
    3 * HvdH.D * HvdH.ppar n ^ 2 < HvdH.Tpar n := by
  have h400 : 400 ≤ HvdH.bpar n := (by norm_num : (400 : ℕ) ≤ 2 ^ 61).trans hb
  have h5 : 5 ≤ HvdH.bpar n := (by norm_num : (5 : ℕ) ≤ 2 ^ 61).trans hb
  have hb10 : HvdH.bpar n ^ 10 ≤ n := bpow10_le_n n h400
  have hbpos : 0 < HvdH.bpar n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2 ^ 61) hb
  -- `4 b^9 ≤ T` from `4 b^10 ≤ 4 n ≤ T b`
  have hT : 4 * HvdH.bpar n ^ 9 ≤ HvdH.Tpar n := by
    have h1 : 4 * HvdH.bpar n ^ 10 ≤ HvdH.Tpar n * HvdH.bpar n :=
      (Nat.mul_le_mul_left 4 hb10).trans h4n
    have h2 : 4 * HvdH.bpar n ^ 10 = (4 * HvdH.bpar n ^ 9) * HvdH.bpar n := by
      rw [mul_assoc, pow_succ]
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hbpos
  -- `186732 b^2 < 4 b^9` since `b ≥ 5`
  have hmono : 186732 * HvdH.bpar n ^ 2 < 4 * HvdH.bpar n ^ 9 := by
    have h1 : 186732 < 4 * HvdH.bpar n ^ 7 := by
      have h57 : 5 ^ 7 ≤ HvdH.bpar n ^ 7 := Nat.pow_le_pow_left h5 7
      exact (by norm_num : (186732 : ℕ) < 4 * 5 ^ 7).trans_le (Nat.mul_le_mul_left 4 h57)
    have h2 : (4 * HvdH.bpar n ^ 7) * HvdH.bpar n ^ 2 = 4 * HvdH.bpar n ^ 9 := by
      rw [mul_assoc, ← pow_add]
    calc 186732 * HvdH.bpar n ^ 2 < (4 * HvdH.bpar n ^ 7) * HvdH.bpar n ^ 2 :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 4 * HvdH.bpar n ^ 9 := h2
  calc 3 * HvdH.D * HvdH.ppar n ^ 2 = 186732 * HvdH.bpar n ^ 2 := by
        rw [HvdH.D, HvdH.ppar]; ring
    _ < 4 * HvdH.bpar n ^ 9 := hmono
    _ ≤ HvdH.Tpar n := hT

/-- **Conjunct 3 of `PolyFacts`** (`K p < n`): with `b = bpar n ≥ 2^61`, `p = ppar n = 6b` and
`(6K+1)^20 ≤ n`: `(6K+1)^10 ≤ n` (else `n^2 < (6K+1)^20 ≤ n ≤ n^2`), while `b^10 ≤ n` and `b ≥ 2`
give `(6Kb)^10 = (6K)^10 b^10 ≤ (6K+1)^10 n ≤ n^2 < n^10`, so `6Kb < n`. -/
theorem mul_ppar_lt (K n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n) (hK : (6 * K + 1) ^ 20 ≤ n) :
    K * HvdH.ppar n < n := by
  have h400 : 400 ≤ HvdH.bpar n := (by norm_num : (400 : ℕ) ≤ 2 ^ 61).trans hb
  have hb10 : HvdH.bpar n ^ 10 ≤ n := bpow10_le_n n h400
  have hn2 : 2 ≤ n := by
    have hb2 : 2 ≤ HvdH.bpar n := (by norm_num : (2 : ℕ) ≤ 2 ^ 61).trans hb
    have hble : HvdH.bpar n ≤ HvdH.bpar n ^ 10 := by
      simpa using Nat.pow_le_pow_right (show 0 < HvdH.bpar n by omega)
        (show 1 ≤ 10 by norm_num)
    exact hb2.trans (hble.trans hb10)
  -- `(6K+1)^10 ≤ n`
  have hx10 : (6 * K + 1) ^ 10 ≤ n := by
    have hx20 : ((6 * K + 1) ^ 10) ^ 2 ≤ n ^ 2 := by
      have he : ((6 * K + 1) ^ 10) ^ 2 = (6 * K + 1) ^ 20 := by rw [← pow_mul]
      have hle : n ≤ n ^ 2 := by
        simpa using Nat.pow_le_pow_right (show 0 < n by omega) (show 1 ≤ 2 by norm_num)
      rw [he]; exact hK.trans hle
    exact (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp hx20
  -- `(6Kb)^10 ≤ n^2`
  have hsq : (6 * K * HvdH.bpar n) ^ 10 ≤ n ^ 2 := by
    have h1 : (6 * K) ^ 10 ≤ (6 * K + 1) ^ 10 := Nat.pow_le_pow_left (by omega) 10
    have h3 : (6 * K) ^ 10 * HvdH.bpar n ^ 10 ≤ (6 * K + 1) ^ 10 * n :=
      Nat.mul_le_mul h1 hb10
    have h4 : (6 * K + 1) ^ 10 * n ≤ n * n := Nat.mul_le_mul hx10 le_rfl
    have h5 : (6 * K * HvdH.bpar n) ^ 10 = (6 * K) ^ 10 * HvdH.bpar n ^ 10 := by
      rw [mul_pow]
    rw [h5]
    calc (6 * K) ^ 10 * HvdH.bpar n ^ 10 ≤ (6 * K + 1) ^ 10 * n := h3
      _ ≤ n * n := h4
      _ = n ^ 2 := by ring
  have hfin : 6 * K * HvdH.bpar n < n :=
    (Nat.pow_lt_pow_iff_left (show (10 : ℕ) ≠ 0 by norm_num)).mp
      (hsq.trans_lt ((Nat.pow_lt_pow_iff_right (show 1 < n by omega)).mpr (by norm_num)))
  have hc : K * HvdH.ppar n = 6 * K * HvdH.bpar n := by
    rw [HvdH.ppar]; ring
  rwa [hc]

/-- "polylog < linear": for large `bpar n`, `3d p² < T`, `3 r p < n` and `K p < n`
(with `p = ppar n = 6b`, `T = Tpar n`, `r = rpar n`, `d = D = 1729`).
Uses `b^10 ≤ n` (`Work.MainP.bpow10_le_n`, from `2^61 ≤ bpar n`), `18^10 ≤ n`, `2^(d+2) ≤ n`.
Conjunct 2: `(18 b r)^d` hmm — use exponent `10d`: `(18br)^{10d} = (18^10)^d (b^10)^d (r^d)^{10}
≤ n^d n^d (2^{d+2} n)^{10} ≤ n^{2d+11} < n^{10d}`, so `18br < n` (if `18br ≥ n` then `n`-powers
contradict `10d > 2d+11`).  Conjunct 3: `(6Kb)^10 = (6K)^10 b^10 ≤ (6K+1)^10 n ≤ n^2`, so `6Kb < n`. -/
theorem PolyFacts (K n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n)
    (h4n : 4 * n ≤ HvdH.Tpar n * HvdH.bpar n)
    (hr : HvdH.rpar n ^ HvdH.D ≤ 2 ^ (HvdH.D + 2) * n)
    (hK : (6 * K + 1) ^ 20 ≤ n) :
    3 * HvdH.D * HvdH.ppar n ^ 2 < HvdH.Tpar n ∧
    3 * HvdH.rpar n * HvdH.ppar n < n ∧ K * HvdH.ppar n < n :=
  ⟨pSq_lt_Tpar n hb h4n, rpBound n hb hr, mul_ppar_lt K n hb hK⟩

end Work.MainP
