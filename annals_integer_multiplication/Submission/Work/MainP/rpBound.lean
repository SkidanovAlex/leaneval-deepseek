import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-! ## `3 r p < n`: polylog is below linear (`d = 1729`, `r = rpar n`, `p = ppar n = 6·bpar n`)

The whole content is the bound `b^(9d-10) ≤ 18^d · 2^(d+2)`, obtained from the hypothesis
`r^d ≤ 2^(d+2) n` plus `b^10 ≤ n`, and the numerical contradiction
`2^(61·(9d-10)) = 2^948611 > 2^10376 = 2^(6·1729+2)`.  No gigantic power is ever evaluated:
all comparisons go through `Nat.pow_le_pow_right` / `Nat.pow_lt_pow_right` on the *exponents*. -/

theorem rpBound (n : ℕ) (hb : 2 ^ 61 ≤ HvdH.bpar n)
    (hr : HvdH.rpar n ^ HvdH.D ≤ 2 ^ (HvdH.D + 2) * n) :
    3 * HvdH.rpar n * HvdH.ppar n < n := by
  have hD : HvdH.D = 1729 := rfl
  rw [hD] at hr
  have hpp : HvdH.ppar n = 6 * HvdH.bpar n := rfl
  rw [hpp]
  -- basic facts about `b = bpar n`
  have hb400 : 400 ≤ HvdH.bpar n := by
    have : (400 : ℕ) ≤ 2 ^ 61 := by norm_num
    exact this.trans hb
  have hb10 : HvdH.bpar n ^ 10 ≤ n := bpow10_le_n n hb400
  have hbpos : 0 < HvdH.bpar n := by
    have : (0 : ℕ) < 2 ^ 61 := by norm_num
    exact lt_of_lt_of_le this hb
  have hnpos : 0 < n := lt_of_lt_of_le (pow_pos hbpos 10) hb10
  -- suppose for contradiction that `n ≤ 18 r b`
  by_contra hlt
  rw [not_lt] at hlt
  have hle : n ≤ 18 * HvdH.rpar n * HvdH.bpar n := by
    have heq : 3 * HvdH.rpar n * (6 * HvdH.bpar n)
        = 18 * HvdH.rpar n * HvdH.bpar n := by ring
    rwa [heq] at hlt
  -- upper bound: `n^1729 ≤ (18 r b)^1729 = 18^1729 r^1729 b^1729 ≤ 18^1729 2^1731 n b^1729`
  have h1 : n ^ 1729 ≤ (18 * HvdH.rpar n * HvdH.bpar n) ^ 1729 :=
    Nat.pow_le_pow_left hle 1729
  have h2 : (18 * HvdH.rpar n * HvdH.bpar n) ^ 1729
      = 18 ^ 1729 * HvdH.rpar n ^ 1729 * HvdH.bpar n ^ 1729 := by
    rw [mul_pow, mul_pow]
  have h3 : HvdH.rpar n ^ 1729 ≤ 2 ^ (1729 + 2) * n := hr
  have h4 : 18 ^ 1729 * HvdH.rpar n ^ 1729 * HvdH.bpar n ^ 1729
      ≤ 18 ^ 1729 * (2 ^ (1729 + 2) * n) * HvdH.bpar n ^ 1729 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
  have h4eq : 18 ^ 1729 * (2 ^ (1729 + 2) * n) * HvdH.bpar n ^ 1729
      = (18 ^ 1729 * 2 ^ (1729 + 2)) * n * HvdH.bpar n ^ 1729 := by ring
  have hupper : n ^ 1729 ≤ (18 ^ 1729 * 2 ^ (1729 + 2)) * n * HvdH.bpar n ^ 1729 :=
    h1.trans ((le_of_eq h2).trans (h4.trans (le_of_eq h4eq)))
  -- lower bound: `b^(10·1728) · n ≤ n^1729`
  have hlow1 : HvdH.bpar n ^ (10 * 1728) ≤ n ^ 1728 := by
    have h := Nat.pow_le_pow_left hb10 1728
    rwa [← pow_mul] at h
  have hlow3 : n ^ 1729 = n ^ 1728 * n := by
    have : (1729 : ℕ) = 1728 + 1 := rfl
    rw [this, pow_succ]
  have hlow : HvdH.bpar n ^ (10 * 1728) * n ≤ n ^ 1729 := by
    rw [hlow3]
    exact Nat.mul_le_mul_right n hlow1
  have hcomb : HvdH.bpar n ^ (10 * 1728) * n
      ≤ (18 ^ 1729 * 2 ^ (1729 + 2)) * n * HvdH.bpar n ^ 1729 := hlow.trans hupper
  -- cancel `n > 0`
  have hcomb2 : HvdH.bpar n ^ (10 * 1728) * n
      ≤ ((18 ^ 1729 * 2 ^ (1729 + 2)) * HvdH.bpar n ^ 1729) * n := by
    rw [show (18 ^ 1729 * 2 ^ (1729 + 2)) * n * HvdH.bpar n ^ 1729
        = ((18 ^ 1729 * 2 ^ (1729 + 2)) * HvdH.bpar n ^ 1729) * n from by ring] at hcomb
    exact hcomb
  have hcancel1 : HvdH.bpar n ^ (10 * 1728)
      ≤ (18 ^ 1729 * 2 ^ (1729 + 2)) * HvdH.bpar n ^ 1729 :=
    Nat.le_of_mul_le_mul_right hcomb2 hnpos
  -- cancel `b^1729 > 0`:  10·1728 = (10·1728 - 1729) + 1729
  have hsplit : HvdH.bpar n ^ (10 * 1728)
      = HvdH.bpar n ^ (10 * 1728 - 1729) * HvdH.bpar n ^ 1729 := by
    rw [← pow_add]
  have hcancel2 : HvdH.bpar n ^ (10 * 1728 - 1729)
      ≤ 18 ^ 1729 * 2 ^ (1729 + 2) := by
    have h := hcancel1
    rw [hsplit] at h
    exact Nat.le_of_mul_le_mul_right h (pow_pos hbpos 1729)
  -- numerics:  `18^1729 · 2^1731 ≤ 2^(6·1729+2)`
  have hC : 18 ^ 1729 * 2 ^ (1729 + 2) ≤ 2 ^ (6 * 1729 + 2) := by
    have h18 : 18 ^ 1729 ≤ 2 ^ (5 * 1729) := by
      have h : (18 : ℕ) ≤ 2 ^ 5 := by norm_num
      calc 18 ^ 1729 ≤ (2 ^ 5) ^ 1729 := Nat.pow_le_pow_left h 1729
        _ = 2 ^ (5 * 1729) := by rw [pow_mul]
    calc 18 ^ 1729 * 2 ^ (1729 + 2) ≤ 2 ^ (5 * 1729) * 2 ^ (1729 + 2) :=
          Nat.mul_le_mul_right _ h18
      _ = 2 ^ (6 * 1729 + 2) := by
          rw [← pow_add]
  -- `2^(61·(10·1728-1729)) = 2^948611 ≤ b^(15551)`
  have hlowb : 2 ^ (61 * (10 * 1728 - 1729)) ≤ HvdH.bpar n ^ (10 * 1728 - 1729) := by
    have h := Nat.pow_le_pow_left hb (10 * 1728 - 1729)
    rwa [← pow_mul] at h
  have hstrict : 2 ^ (6 * 1729 + 2) < 2 ^ (61 * (10 * 1728 - 1729)) :=
    Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have hfinal : 2 ^ (61 * (10 * 1728 - 1729)) ≤ 2 ^ (6 * 1729 + 2) :=
    hlowb.trans (hcancel2.trans hC)
  omega

end Work.MainP
