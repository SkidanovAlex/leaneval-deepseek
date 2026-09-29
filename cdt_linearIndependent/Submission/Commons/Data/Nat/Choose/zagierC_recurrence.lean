import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star

/-! # The three-term recurrence of Zagier's sequence `C`

`a(m) = ∑ₖ C(m,k)²·C(2k,k)` (Zagier's sequence C; OEIS A002893) satisfies
`(n+1)² a(n+1) = (10n²+10n+3) a(n) − 9n² a(n−1)` for `n ≥ 1`.

The proof below is a creative-telescoping (Zeilberger) verification: with
`A(m,k) = C(m,k)²·C(2k,k)` one checks that

```
9(m+1)² A(m,k) − (10m²+30m+23) A(m+1,k) + (m+2)² A(m+2,k)
  = G(m,k) − G(m,k+1)
```

for the rational certificate `G(m,k) = A(m,k)·(m+1)²k³(4m+8−3k) /
((m+1−k)²(m+2−k)²)`, valid on `0 ≤ k < m`.  Summing over `k` and handling
the three top corner terms `k = m, m+1, m+2` by the closed central-binomial
relations gives `9(m+1)² S(m) − (10m²+30m+23) S(m+1) + (m+2)² S(m+2) = 0`,
which is the target recurrence after shifting `n ↦ m+1`.

Everything is done over `ℤ` for the sums themselves and over `ℚ` for the
certificate (the sums are integers, the certificate is rational); the final
equality is an equality of integers.
-/

open scoped BigOperators

namespace Commons.Data.Nat.Choose

namespace ZagierC

open scoped BigOperators

def A (m k : ℕ) : ℤ := (Nat.choose m k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)

/-- `S(m) = ∑ₖ A(m,k)` over `0 ≤ k ≤ m`. -/
def S (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), A m k

lemma A_of_gt {m k : ℕ} (h : m < k) : A m k = 0 := by
  unfold A
  simp [Nat.choose_eq_zero_of_lt h]

lemma A_succ_left (m k : ℕ) :
    A (m + 1) k * (((m + 1 - k : ℕ) : ℤ) ^ 2) = A m k * (((m + 1 : ℕ) : ℤ) ^ 2) := by
  unfold A
  have hz : ((Nat.choose (m+1) k : ℕ) : ℤ) * (((m + 1 - k) : ℕ) : ℤ) =
      ((Nat.choose m k : ℕ) : ℤ) * (((m + 1 : ℕ) : ℤ)) := by
    exact_mod_cast (Nat.choose_mul_succ_eq m k).symm
  have hsq : ((Nat.choose (m+1) k : ℕ) : ℤ)^2 * (((m + 1 - k) : ℕ) : ℤ)^2 =
      ((Nat.choose m k : ℕ) : ℤ)^2 * (((m + 1 : ℕ) : ℤ)^2) := by
    calc ((Nat.choose (m+1) k : ℕ) : ℤ)^2 * (((m + 1 - k) : ℕ) : ℤ)^2
        = (((Nat.choose (m+1) k : ℕ) : ℤ) * (((m + 1 - k) : ℕ) : ℤ))^2 := by ring
    _ = (((Nat.choose m k : ℕ) : ℤ) * (((m + 1 : ℕ) : ℤ)))^2 := by rw [hz]
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (((m + 1 : ℕ) : ℤ)^2) := by ring
  calc
    ((Nat.choose (m+1) k : ℕ) : ℤ)^2 * (Nat.choose (2*k) k : ℤ) * (((m + 1 - k : ℕ) : ℤ)^2)
        = (Nat.choose (2*k) k : ℤ) * (((Nat.choose (m+1) k : ℕ) : ℤ)^2 * (((m + 1 - k : ℕ) : ℤ)^2)) := by ring
    _ = (Nat.choose (2*k) k : ℤ) * (((Nat.choose m k : ℕ) : ℤ)^2 * (((m + 1 : ℕ) : ℤ)^2)) := by rw [hsq]
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (Nat.choose (2*k) k : ℤ) * (((m + 1 : ℕ) : ℤ)^2) := by ring

lemma A_succ_left' (m k : ℕ) :
    A (m + 2) k * (((m + 2 - k : ℕ) : ℤ) ^ 2) = A (m + 1) k * (((m + 2 : ℕ) : ℤ) ^ 2) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, show (m+1)+1 = m+2 by omega] using (A_succ_left (m+1) k)

lemma A_double_left (m k : ℕ) :
    A (m + 2) k * (((m + 2 - k : ℕ) : ℤ) ^ 2) * (((m + 1 - k : ℕ) : ℤ) ^ 2)
      = A m k * (((m + 2 : ℕ) : ℤ) ^ 2) * (((m + 1 : ℕ) : ℤ) ^ 2) := by
  have h1 := A_succ_left m k
  have h2 := A_succ_left' m k
  calc
    A (m + 2) k * (((m + 2 - k : ℕ) : ℤ) ^ 2) * (((m + 1 - k : ℕ) : ℤ) ^ 2)
        = (A (m + 2) k * (((m + 2 - k : ℕ) : ℤ) ^ 2)) * (((m + 1 - k : ℕ) : ℤ) ^ 2) := by ring
    _ = (A (m + 1) k * (((m + 2 : ℕ) : ℤ) ^ 2)) * (((m + 1 - k : ℕ) : ℤ) ^ 2) := by rw [h2]
    _ = (A (m + 1) k * (((m + 1 - k : ℕ) : ℤ) ^ 2)) * (((m + 2 : ℕ) : ℤ) ^ 2) := by ring
    _ = (A m k * (((m + 1 : ℕ) : ℤ) ^ 2)) * (((m + 2 : ℕ) : ℤ) ^ 2) := by rw [h1]
    _ = A m k * (((m + 2 : ℕ) : ℤ) ^ 2) * (((m + 1 : ℕ) : ℤ) ^ 2) := by ring

lemma central_binom_succ (k : ℕ) :
    ((Nat.choose (2 * k + 2) (k + 1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 2)
      = ((Nat.choose (2 * k) k : ℕ) : ℤ) * (((2 * k + 2 : ℕ) : ℤ)) * (((2 * k + 1 : ℕ) : ℤ)) := by
  have h1 : Nat.choose (2 * k + 2) (k + 1) * (k + 1) =
      Nat.choose (2 * k + 1) k * (2 * k + 2) := by
    have h := Nat.choose_mul_succ_eq (2 * k + 1) (k + 1)
    have hstep : 2 * k + 2 - (k + 1) = k + 1 := by omega
    have hsym : Nat.choose (2 * k + 1) (k + 1) = Nat.choose (2 * k + 1) k := by
      have hk : k ≤ 2 * k + 1 := by omega
      have := Nat.choose_symm hk  -- (2k+1).choose ((2k+1)-k) = (2k+1).choose k
      simpa [show 2 * k + 1 - k = k + 1 by omega] using this
    calc
      Nat.choose (2 * k + 2) (k + 1) * (k + 1)
          = Nat.choose (2 * k + 2) (k + 1) * ((2 * k + 2) - (k + 1)) := by rw [hstep]
      _ = Nat.choose (2 * k + 1) (k + 1) * (2 * k + 2) := by rw [Nat.choose_mul_succ_eq (2*k+1) (k+1)]
      _ = Nat.choose (2 * k + 1) k * (2 * k + 2) := by rw [hsym]
  have h2 : Nat.choose (2 * k + 1) k * (k + 1) =
      Nat.choose (2 * k) k * (2 * k + 1) := by
    have hstep : 2 * k + 1 - k = k + 1 := by omega
    calc
      Nat.choose (2 * k + 1) k * (k + 1)
          = Nat.choose (2 * k + 1) k * ((2 * k + 1) - k) := by rw [hstep]
      _ = Nat.choose (2 * k) k * (2 * k + 1) := by rw [Nat.choose_mul_succ_eq (2 * k) k]
  have h3 : (k + 1)^2 * Nat.choose (2 * k + 2) (k + 1) =
      (2 * k + 2) * ((2 * k + 1) * Nat.choose (2 * k) k) := by
    calc
      (k + 1)^2 * Nat.choose (2 * k + 2) (k + 1)
          = (k + 1) * (Nat.choose (2 * k + 2) (k + 1) * (k + 1)) := by ring
      _ = (k + 1) * (Nat.choose (2 * k + 1) k * (2 * k + 2)) := by rw [h1]
      _ = (k + 1) * ((2 * k + 2) * Nat.choose (2 * k + 1) k) := by ring
      _ = ((k + 1) * Nat.choose (2 * k + 1) k) * (2 * k + 2) := by ring
      _ = (Nat.choose (2 * k + 1) k * (k + 1)) * (2 * k + 2) := by ring
      _ = (Nat.choose (2 * k) k * (2 * k + 1)) * (2 * k + 2) := by rw [h2]
      _ = (2 * k + 2) * ((2 * k + 1) * Nat.choose (2 * k) k) := by ring
  have hz := congrArg (fun x : ℕ => (x : ℤ)) h3
  calc
    ((Nat.choose (2 * k + 2) (k + 1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 2)
        = ((k + 1 : ℕ) : ℤ)^2 * ((Nat.choose (2 * k + 2) (k + 1) : ℕ) : ℤ) := by ring
    _ = ((2 * k + 2 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) * ((Nat.choose (2 * k) k : ℕ) : ℤ)) := hz
    _ = ((Nat.choose (2 * k) k : ℕ) : ℤ) * (((2 * k + 2 : ℕ) : ℤ)) * (((2 * k + 1 : ℕ) : ℤ)) := by ring

lemma A_succ_right (m k : ℕ) :
    A m (k + 1) * (((k + 1 : ℕ) : ℤ) ^ 4)
      = A m k * (((m - k : ℕ) : ℤ) ^ 2) * (((2 * k + 2 : ℕ) : ℤ)) * (((2 * k + 1 : ℕ) : ℤ)) := by
  unfold A
  have hrow : ((Nat.choose m (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ)) =
      ((Nat.choose m k : ℕ) : ℤ) * (((m - k : ℕ) : ℤ)) := by
    exact_mod_cast (Nat.choose_succ_right_eq m k)
  have hrow2 : ((Nat.choose m (k+1) : ℕ) : ℤ)^2 * (((k + 1 : ℕ) : ℤ) ^ 2) =
      ((Nat.choose m k : ℕ) : ℤ)^2 * (((m - k : ℕ) : ℤ) ^ 2) := by
    calc ((Nat.choose m (k+1) : ℕ) : ℤ)^2 * (((k + 1 : ℕ) : ℤ) ^ 2)
        = (((Nat.choose m (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ)))^2 := by ring
    _ = (((Nat.choose m k : ℕ) : ℤ) * (((m - k : ℕ) : ℤ)))^2 := by rw [hrow]
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (((m - k : ℕ) : ℤ) ^ 2) := by ring
  have htwo : 2 * (k + 1) = 2 * k + 2 := by ring
  have hcen := central_binom_succ k
  -- reorganize: LHS = C(m,k+1)^2 * C(2k+2,k+1) * (k+1)^4
  --        = (C(m,k+1)*(k+1))^2 * (C(2k+2,k+1)*(k+1)^2)
  --        = C(m,k)^2 (m-k)^2 * (2k+2)(2k+1) C(2k,k)
  calc
    ((Nat.choose m (k+1) : ℕ) : ℤ)^2 * ((Nat.choose (2*(k+1)) (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 4)
        = ((Nat.choose m (k+1) : ℕ) : ℤ)^2 * (((k + 1 : ℕ) : ℤ) ^ 2) * ((Nat.choose (2*(k+1)) (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 2) := by ring
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (((m - k : ℕ) : ℤ) ^ 2) * ((Nat.choose (2*(k+1)) (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 2) := by
          rw [hrow2]   -- rw on first two factors? they are outermost on the left of the product? LHS of goal: ((C(m,k+1)^2*(k+1)^2)*(C2)*(k+1)^2): subterm at position 1
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (((m - k : ℕ) : ℤ) ^ 2) * ((Nat.choose (2*k+2) (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 2) := by
          rw [htwo]
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (((m - k : ℕ) : ℤ) ^ 2) * (((Nat.choose (2*k+2) (k+1) : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) ^ 2)) := by ring
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * (((m - k : ℕ) : ℤ) ^ 2) * (((Nat.choose (2*k) k : ℕ) : ℤ) * (((2 * k + 2 : ℕ) : ℤ)) * (((2 * k + 1 : ℕ) : ℤ))) := by
          rw [hcen]
    _ = ((Nat.choose m k : ℕ) : ℤ)^2 * ((Nat.choose (2*k) k : ℕ) : ℤ) * (((m - k : ℕ) : ℤ) ^ 2) * (((2 * k + 2 : ℕ) : ℤ)) * (((2 * k + 1 : ℕ) : ℤ)) := by ring

-- ============ Q-side ============
open scoped BigOperators

def c0Q (m : ℕ) : ℚ := 9 * ((m : ℚ) + 1)^2
def c1Q (m : ℕ) : ℚ := -(10 * (m : ℚ)^2 + 30 * (m : ℚ) + 23)
def c2Q (m : ℕ) : ℚ := ((m : ℚ) + 2)^2

def masterQ (m k : ℕ) : ℚ := c0Q m * (A m k : ℚ) + c1Q m * (A (m+1) k : ℚ) + c2Q m * (A (m+2) k : ℚ)

def GQ (m k : ℕ) : ℚ :=
  (A m k : ℚ) * ((m : ℚ) + 1)^2 * (k : ℚ)^3 * (4 * (m : ℚ) + 8 - 3 * (k : ℚ)) /
    (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)

lemma AC_m1 (m k : ℕ) (hk : k ≤ m) :
    (A (m + 1) k : ℚ) = (A m k : ℚ) * ((m : ℚ) + 1)^2 / ((m : ℚ) + 1 - (k : ℚ))^2 := by
  have hz := A_succ_left m k
  have hq : ((A (m + 1) k : ℚ)) * (((m + 1 - k : ℕ) : ℚ)^2) =
      (A m k : ℚ) * (((m + 1 : ℕ) : ℚ)^2) := by
    exact_mod_cast hz
  have hsub : ((m + 1 - k : ℕ) : ℚ) = (m : ℚ) + 1 - (k : ℚ) := by
    rw [Nat.cast_sub (by omega : k ≤ m + 1)]
    norm_num
  have hm1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  rw [hsub, hm1] at hq
  have hden : (m : ℚ) + 1 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 1 - k := by omega
    have hs : (m : ℚ) + 1 - (k : ℚ) = ((m + 1 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 1)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  calc
    (A (m + 1) k : ℚ) = (A (m + 1) k : ℚ) * (((m : ℚ) + 1 - (k : ℚ))^2) / (((m : ℚ) + 1 - (k : ℚ))^2) := by
          field_simp [hden]
    _ = (A m k : ℚ) * ((m : ℚ) + 1)^2 / (((m : ℚ) + 1 - (k : ℚ))^2) := by rw [hq]

lemma AC_m2 (m k : ℕ) (hk : k ≤ m) :
    (A (m + 2) k : ℚ) = (A m k : ℚ) * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2 /
      (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) := by
  have hz := A_double_left m k
  have hq : ((A (m + 2) k : ℚ)) * (((m + 2 - k : ℕ) : ℚ)^2) * (((m + 1 - k : ℕ) : ℚ)^2) =
      (A m k : ℚ) * (((m + 2 : ℕ) : ℚ)^2) * (((m + 1 : ℕ) : ℚ)^2) := by
    exact_mod_cast hz
  have hsub2 : ((m + 2 - k : ℕ) : ℚ) = (m : ℚ) + 2 - (k : ℚ) := by
    rw [Nat.cast_sub (by omega : k ≤ m + 2)]
    norm_num
  have hsub1 : ((m + 1 - k : ℕ) : ℚ) = (m : ℚ) + 1 - (k : ℚ) := by
    rw [Nat.cast_sub (by omega : k ≤ m + 1)]
    norm_num
  have hm1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  have hm2 : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by norm_num
  rw [hsub2, hsub1, hm1, hm2] at hq
  have hd1 : (m : ℚ) + 1 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 1 - k := by omega
    have hs : (m : ℚ) + 1 - (k : ℚ) = ((m + 1 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 1)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  have hd2 : (m : ℚ) + 2 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 2 - k := by omega
    have hs : (m : ℚ) + 2 - (k : ℚ) = ((m + 2 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 2)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  have hq2 : (A (m + 2) k : ℚ) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) =
      (A m k : ℚ) * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2 := by
    calc
      (A (m + 2) k : ℚ) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
          = (A (m + 2) k : ℚ) * ((m : ℚ) + 2 - (k : ℚ))^2 * ((m : ℚ) + 1 - (k : ℚ))^2 := by ring
      _ = (A m k : ℚ) * ((m : ℚ) + 2)^2 * ((m : ℚ) + 1)^2 := hq
      _ = (A m k : ℚ) * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2 := by ring
  calc
    (A (m + 2) k : ℚ) = (A (m + 2) k : ℚ) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
          / (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) := by
          field_simp [hd1, hd2]
    _ = (A m k : ℚ) * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2
          / (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) := by rw [hq2]

lemma AC_k1 (m k : ℕ) (hk : k + 1 ≤ m) :
    (A m (k + 1) : ℚ) = (A m k : ℚ) * ((2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1) * ((m : ℚ) - (k : ℚ))^2) /
      ((k : ℚ) + 1)^4 := by
  have hz := A_succ_right m k
  have hq : (A m (k + 1) : ℚ) * (((k + 1 : ℕ) : ℚ)^4) =
      (A m k : ℚ) * (((m - k : ℕ) : ℚ)^2) * (((2 * k + 2 : ℕ) : ℚ)) * (((2 * k + 1 : ℕ) : ℚ)) := by
    exact_mod_cast hz
  have hk1 : ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 := by norm_num
  have hsub : ((m - k : ℕ) : ℚ) = (m : ℚ) - (k : ℚ) := by
    rw [Nat.cast_sub (by omega : k ≤ m)]
  have h2k2 : ((2 * k + 2 : ℕ) : ℚ) = 2 * (k : ℚ) + 2 := by norm_num
  have h2k1 : ((2 * k + 1 : ℕ) : ℚ) = 2 * (k : ℚ) + 1 := by norm_num
  rw [hk1, hsub, h2k2, h2k1] at hq
  have hd : (k : ℚ) + 1 ≠ 0 := by
    have : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    simpa [hk1] using this
  calc
    (A m (k + 1) : ℚ) = (A m (k + 1) : ℚ) * ((k : ℚ) + 1)^4 / ((k : ℚ) + 1)^4 := by
          field_simp [hd]
    _ = (A m k : ℚ) * ((2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1) * ((m : ℚ) - (k : ℚ))^2) /
          ((k : ℚ) + 1)^4 := by
          rw [hq]
          field_simp [hd]

/-- `masterQ(m,k)·D = A(m,k)·Q₁` where `D=(m+1−k)²(m+2−k)²`. -/
lemma masterQ_mul_D (m k : ℕ) (hk : k ≤ m) :
    masterQ m k * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) =
      (A m k : ℚ) * (9 * ((m : ℚ) + 1)^2 * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
        + c1Q m * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2 - (k : ℚ))^2
        + c2Q m * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2) := by
  unfold masterQ c0Q c1Q c2Q
  rw [AC_m1 m k hk]
  rw [AC_m2 m k hk]
  have hd1 : (m : ℚ) + 1 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 1 - k := by omega
    have hs : (m : ℚ) + 1 - (k : ℚ) = ((m + 1 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 1)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  have hd2 : (m : ℚ) + 2 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 2 - k := by omega
    have hs : (m : ℚ) + 2 - (k : ℚ) = ((m + 2 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 2)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  field_simp [hd1, hd2]

/-- `(GQ(m,k)−GQ(m,k+1))·D = A(m,k)·Q₂`. -/
lemma GQ_mul_D (m k : ℕ) (hk : k + 1 ≤ m) :
    (GQ m k - GQ m (k + 1)) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) =
      (A m k : ℚ) * ((m : ℚ) + 1)^2 * ((k : ℚ)^3 * (4 * (m : ℚ) + 8 - 3 * (k : ℚ))
        - 2 * (2 * (k : ℚ) + 1) * (4 * (m : ℚ) + 5 - 3 * (k : ℚ)) * ((m : ℚ) + 2 - (k : ℚ))^2) := by
  unfold GQ
  rw [AC_k1 m k hk]
  simp only [Nat.cast_add, Nat.cast_one]
  have hkm : k ≤ m := by omega
  have hd1 : (m : ℚ) + 1 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 1 - k := by omega
    have hs : (m : ℚ) + 1 - (k : ℚ) = ((m + 1 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 1)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  have hd2 : (m : ℚ) + 2 - (k : ℚ) ≠ 0 := by
    have : 0 < m + 2 - k := by omega
    have hs : (m : ℚ) + 2 - (k : ℚ) = ((m + 2 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m + 2)]
      norm_num
    rw [hs]; exact_mod_cast (ne_of_gt this)
  have hd3 : (m : ℚ) - (k : ℚ) ≠ 0 := by
    have : 0 < m - k := by omega
    have hs : (m : ℚ) - (k : ℚ) = ((m - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : k ≤ m)]
    rw [hs]; exact_mod_cast (ne_of_gt this)
  have hd4 : (k : ℚ) + 1 ≠ 0 := by
    have : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    simpa using this
  have hd5 : (m : ℚ) + 1 - ((k : ℚ) + 1) ≠ 0 := by
    have : (m : ℚ) + 1 - ((k : ℚ) + 1) = (m : ℚ) - (k : ℚ) := by ring
    rw [this]; exact hd3
  have hd6 : (m : ℚ) + 2 - ((k : ℚ) + 1) ≠ 0 := by
    have : (m : ℚ) + 2 - ((k : ℚ) + 1) = (m : ℚ) + 1 - (k : ℚ) := by ring
    rw [this]; exact hd1
  field_simp [hd1, hd2, hd3, hd4, hd5, hd6]
  ring

/-- `Q₁ = Q₂`, the polynomial identity behind the telescoping. -/
lemma Q1_eq_Q2 (m k : ℕ) :
    9 * ((m : ℚ) + 1)^2 * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
      + c1Q m * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2 - (k : ℚ))^2
      + c2Q m * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2 =
      ((m : ℚ) + 1)^2 * ((k : ℚ)^3 * (4 * (m : ℚ) + 8 - 3 * (k : ℚ))
        - 2 * (2 * (k : ℚ) + 1) * (4 * (m : ℚ) + 5 - 3 * (k : ℚ)) * ((m : ℚ) + 2 - (k : ℚ))^2) := by
  unfold c1Q c2Q
  ring

lemma tel (m k : ℕ) (hk : k + 1 ≤ m) : masterQ m k = GQ m k - GQ m (k+1) := by
  have hkm : k ≤ m := by omega
  have h1 := masterQ_mul_D m k hkm
  have h2 := GQ_mul_D m k hk
  have h3 := Q1_eq_Q2 m k
  have hden : (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) ≠ 0 := by
    have hd1 : (m : ℚ) + 1 - (k : ℚ) ≠ 0 := by
      have : 0 < m + 1 - k := by omega
      have hs : (m : ℚ) + 1 - (k : ℚ) = ((m + 1 - k : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega : k ≤ m + 1)]
        norm_num
      rw [hs]; exact_mod_cast (ne_of_gt this)
    have hd2 : (m : ℚ) + 2 - (k : ℚ) ≠ 0 := by
      have : 0 < m + 2 - k := by omega
      have hs : (m : ℚ) + 2 - (k : ℚ) = ((m + 2 - k : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega : k ≤ m + 2)]
        norm_num
      rw [hs]; exact_mod_cast (ne_of_gt this)
    exact mul_ne_zero (pow_ne_zero 2 hd1) (pow_ne_zero 2 hd2)
  have hzD : (masterQ m k - (GQ m k - GQ m (k + 1))) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) = 0 := by
    calc
      (masterQ m k - (GQ m k - GQ m (k + 1))) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
          = masterQ m k * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
            - (GQ m k - GQ m (k + 1)) * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2) := by ring
      _ = (A m k : ℚ) * (9 * ((m : ℚ) + 1)^2 * (((m : ℚ) + 1 - (k : ℚ))^2 * ((m : ℚ) + 2 - (k : ℚ))^2)
            + c1Q m * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2 - (k : ℚ))^2
            + c2Q m * ((m : ℚ) + 1)^2 * ((m : ℚ) + 2)^2)
          - (A m k : ℚ) * ((m : ℚ) + 1)^2 * ((k : ℚ)^3 * (4 * (m : ℚ) + 8 - 3 * (k : ℚ))
            - 2 * (2 * (k : ℚ) + 1) * (4 * (m : ℚ) + 5 - 3 * (k : ℚ)) * ((m : ℚ) + 2 - (k : ℚ))^2) := by
          rw [h1, h2]
      _ = 0 := by
          rw [h3]
          ring
  have hz : masterQ m k - (GQ m k - GQ m (k + 1)) = 0 := by
    exact (mul_eq_zero.mp hzD).resolve_right hden
  exact sub_eq_zero.mp hz


-- ===== corner / central relations and A-value expansions =====

noncomputable def qC (m : ℕ) : ℚ := (Nat.choose (2 * m) m : ℚ)
noncomputable def qX (m : ℕ) : ℚ := (Nat.choose (2 * m + 2) (m + 1) : ℚ)
noncomputable def qZ (m : ℕ) : ℚ := (Nat.choose (2 * m + 4) (m + 2) : ℚ)

lemma relX (m : ℕ) : qX m * ((m : ℚ) + 1) = 2 * (2 * (m : ℚ) + 1) * qC m := by
  have h := central_binom_succ m
  have hq : ((Nat.choose (2 * m + 2) (m + 1) : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ)^2) =
      ((Nat.choose (2 * m) m : ℕ) : ℚ) * (((2 * m + 2 : ℕ) : ℚ)) * (((2 * m + 1 : ℕ) : ℚ)) := by
    exact_mod_cast h
  have hm1n : ((m + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have h1 : ((2 * m + 2 : ℕ) : ℚ) = 2 * (m : ℚ) + 2 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have h2 : ((2 * m + 1 : ℕ) : ℚ) = 2 * (m : ℚ) + 1 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have h3 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  rw [h3, h1, h2] at hq
  unfold qX qC
  calc
    ((Nat.choose (2*m+2) (m+1):ℕ):ℚ) * ((m : ℚ) + 1)
        = ((Nat.choose (2*m+2) (m+1):ℕ):ℚ) * (((m : ℚ) + 1)^2) / ((m : ℚ) + 1) := by
          field_simp [show (m : ℚ) + 1 ≠ 0 by simpa [h3] using hm1n]
    _ = ((Nat.choose (2*m) m:ℕ):ℚ) * (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1) / ((m : ℚ) + 1) := by rw [hq]
    _ = 2 * (2 * (m : ℚ) + 1) * ((Nat.choose (2*m) m : ℕ) : ℚ) := by
          field_simp [show (m : ℚ) + 1 ≠ 0 by simpa [h3] using hm1n]

lemma relZ (m : ℕ) : qZ m * ((m : ℚ) + 2) = 2 * (2 * (m : ℚ) + 3) * qX m := by
  have h := central_binom_succ (m + 1)
  have h2m4n : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
  have h2m1n : 2 * (m + 1) = 2 * m + 2 := by ring
  have h2m3n : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
  have hmp1n : (m + 1) + 1 = m + 2 := by omega
  rw [h2m4n, h2m3n, h2m1n, hmp1n] at h
  have hq : ((Nat.choose (2 * m + 4) (m + 2) : ℕ) : ℚ) * (((m + 2 : ℕ) : ℚ)^2) =
      ((Nat.choose (2 * m + 2) (m + 1) : ℕ) : ℚ) * (((2 * m + 4 : ℕ) : ℚ)) * (((2 * m + 3 : ℕ) : ℚ)) := by
    exact_mod_cast h
  have hm2n : ((m + 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have h1 : ((2 * m + 4 : ℕ) : ℚ) = 2 * (m : ℚ) + 4 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have h2 : ((2 * m + 3 : ℕ) : ℚ) = 2 * (m : ℚ) + 3 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have h3 : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by norm_num
  rw [h3, h1, h2] at hq
  unfold qZ qX
  calc
    ((Nat.choose (2*m+4) (m+2):ℕ):ℚ) * ((m : ℚ) + 2)
        = ((Nat.choose (2*m+4) (m+2):ℕ):ℚ) * (((m : ℚ) + 2)^2) / ((m : ℚ) + 2) := by
          field_simp [show (m : ℚ) + 2 ≠ 0 by simpa [h3] using hm2n]
    _ = ((Nat.choose (2*m+2) (m+1):ℕ):ℚ) * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 3) / ((m : ℚ) + 2) := by rw [hq]
    _ = 2 * (2 * (m : ℚ) + 3) * ((Nat.choose (2*m+2) (m+1) : ℕ) : ℚ) := by
          field_simp [show (m : ℚ) + 2 ≠ 0 by simpa [h3] using hm2n]
          ring


lemma A_mm (m : ℕ) : (A m m : ℚ) = qC m := by
  unfold A qC
  simp [Nat.choose_self]

lemma A_succm_succm (m : ℕ) : (A (m + 1) (m + 1) : ℚ) = qX m := by
  unfold A qX
  have htwo : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [htwo]
  simp [Nat.choose_self]

lemma A_succ2m_succ2m (m : ℕ) : (A (m + 2) (m + 2) : ℚ) = qZ m := by
  unfold A qZ
  have htwo : 2 * (m + 2) = 2 * m + 4 := by ring
  rw [htwo]
  simp [Nat.choose_self]

/-- `A(m+1,m) = A(m,m)·(m+1)²`. -/
lemma A_succm_m (m : ℕ) : (A (m + 1) m : ℚ) = (A m m : ℚ) * ((m : ℚ) + 1)^2 := by
  have h := A_succ_left m m
  have hsub : (m + 1 - m : ℕ) = 1 := by omega
  have h' : A (m + 1) m = A m m * (((m + 1 : ℕ) : ℤ)^2) := by
    simpa [hsub] using h
  have hq : (A (m + 1) m : ℚ) = (A m m : ℚ) * (((m + 1 : ℕ) : ℚ)^2) := by
    exact_mod_cast h'
  have hm1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  rw [hm1] at hq
  exact hq

/-- `A(m+2,m)·4 = A(m,m)·(m+2)²·(m+1)²`. -/
lemma A_succ2m_m (m : ℕ) : (A (m + 2) m : ℚ) * 4 = (A m m : ℚ) * ((m : ℚ) + 2)^2 * ((m : ℚ) + 1)^2 := by
  have h := A_double_left m m
  have hsub2 : (m + 2 - m : ℕ) = 2 := by omega
  have hsub1 : (m + 1 - m : ℕ) = 1 := by omega
  have h' : A (m + 2) m * 4 = A m m * (((m + 2 : ℕ) : ℤ)^2) * (((m + 1 : ℕ) : ℤ)^2) := by
    -- A(m+2,m) * (2^2) * (1^2) = ... ; ring to combine 4
    simpa [hsub2, hsub1] using h
  have hq : (A (m + 2) m : ℚ) * 4 = (A m m : ℚ) * (((m + 2 : ℕ) : ℚ)^2) * (((m + 1 : ℕ) : ℚ)^2) := by
    exact_mod_cast h'
  have hm2 : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by norm_num
  have hm1 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by norm_num
  rw [hm2, hm1] at hq
  exact hq

/-- `A(m+2,m+1) = A(m+1,m+1)·(m+2)²`. -/
lemma A_succ2m_succm (m : ℕ) : (A (m + 2) (m + 1) : ℚ) = (A (m + 1) (m + 1) : ℚ) * ((m : ℚ) + 2)^2 := by
  have h := A_succ_left (m + 1) (m + 1)
  have hsub : (m + 1 + 1 - (m + 1) : ℕ) = 1 := by omega
  have h' : A (m + 2) (m + 1) = A (m + 1) (m + 1) * (((m + 2 : ℕ) : ℤ)^2) := by
    -- note (m+1)+1 = m+2
    simpa [hsub, Nat.add_assoc] using h
  have hq : (A (m + 2) (m + 1) : ℚ) = (A (m + 1) (m + 1) : ℚ) * (((m + 2 : ℕ) : ℚ)^2) := by
    exact_mod_cast h'
  have hm2 : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by norm_num
  rw [hm2] at hq
  exact hq


lemma qX_eq (m : ℕ) : qX m = 2 * (2 * (m : ℚ) + 1) * qC m / ((m : ℚ) + 1) := by
  have hm1n : (m : ℚ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  -- from relX : qX·(m+1) = 2(2m+1)·qC ; solve for qX
  calc
    qX m = qX m * ((m : ℚ) + 1) / ((m : ℚ) + 1) := by
          field_simp [hm1n]
    _ = 2 * (2 * (m : ℚ) + 1) * qC m / ((m : ℚ) + 1) := by rw [relX m]

lemma qZ_eq (m : ℕ) : qZ m = 2 * (2 * (m : ℚ) + 3) * qX m / ((m : ℚ) + 2) := by
  have hm2n : (m : ℚ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  calc
    qZ m = qZ m * ((m : ℚ) + 2) / ((m : ℚ) + 2) := by
          field_simp [hm2n]
    _ = 2 * (2 * (m : ℚ) + 3) * qX m / ((m : ℚ) + 2) := by rw [relZ m]

/-- `A(m+2,m) = A(m,m)·(m+2)²·(m+1)²/4`. -/
lemma A_succ2m_m' (m : ℕ) : (A (m + 2) m : ℚ) =
    (A m m : ℚ) * ((m : ℚ) + 2)^2 * ((m : ℚ) + 1)^2 / 4 := by
  have h := A_succ2m_m m
  -- h : A(m+2,m)·4 = A(m,m)(m+2)²(m+1)²
  calc
    (A (m + 2) m : ℚ) = (A (m + 2) m : ℚ) * 4 / 4 := by ring
    _ = (A m m : ℚ) * ((m : ℚ) + 2)^2 * ((m : ℚ) + 1)^2 / 4 := by rw [h]

/-- The three top corner terms of the master sum add up to `GQ(m,m)`. -/
lemma boundary (m : ℕ) :
    masterQ m m + masterQ m (m + 1) + masterQ m (m + 2) = GQ m m := by
  unfold masterQ GQ c0Q c1Q c2Q
  rw [A_of_gt (by omega : m < m + 1)]
  rw [A_of_gt (by omega : m < m + 2)]
  rw [A_of_gt (by omega : m + 1 < m + 2)]
  rw [A_succm_m, A_succ2m_m', A_succ2m_succm]
  rw [A_mm, A_succm_succm, A_succ2m_succ2m]
  rw [qZ_eq, qX_eq]
  have hm1n : (m : ℚ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hm2n : (m : ℚ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  -- expression is now rational in (m : ℚ) and qC m
  field_simp [hm1n, hm2n]
  ring

noncomputable def SQ (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), (A m k : ℚ)

lemma sum_A0 (m : ℕ) : (∑ k ∈ Finset.range (m + 3), (A m k : ℚ)) = SQ m := by
  rw [show m + 3 = (m + 1) + 2 by omega]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  rw [A_of_gt (by omega : m < m + 1)]
  rw [A_of_gt (by omega : m < m + 2)]
  simp [SQ]

lemma sum_A1 (m : ℕ) : (∑ k ∈ Finset.range (m + 3), (A (m + 1) k : ℚ)) = SQ (m + 1) := by
  rw [show m + 3 = (m + 1) + 2 by omega]
  rw [Finset.sum_range_succ]
  rw [A_of_gt (by omega : m + 1 < m + 2)]
  simp [SQ]

lemma sum_A2 (m : ℕ) : (∑ k ∈ Finset.range (m + 3), (A (m + 2) k : ℚ)) = SQ (m + 2) := by
  simp [SQ]

lemma masterSum_eq (m : ℕ) :
    (∑ k ∈ Finset.range (m + 3), masterQ m k) =
      9 * ((m : ℚ) + 1)^2 * SQ m - (10 * (m : ℚ)^2 + 30 * (m : ℚ) + 23) * SQ (m + 1)
        + ((m : ℚ) + 2)^2 * SQ (m + 2) := by
  have hsplit : (∑ k ∈ Finset.range (m + 3), masterQ m k) =
      c0Q m * (∑ k ∈ Finset.range (m + 3), (A m k : ℚ))
        + c1Q m * (∑ k ∈ Finset.range (m + 3), (A (m + 1) k : ℚ))
        + c2Q m * (∑ k ∈ Finset.range (m + 3), (A (m + 2) k : ℚ)) := by
    unfold masterQ
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, sum_A0, sum_A1, sum_A2]
  unfold c0Q c1Q c2Q
  ring

lemma masterSum_zero (m : ℕ) : (∑ k ∈ Finset.range (m + 3), masterQ m k) = 0 := by
  have hs := Finset.sum_range_add (fun k => masterQ m k) m 3
  rw [hs]
  have htail : (∑ x ∈ Finset.range 3, masterQ m (m + x)) = masterQ m m + masterQ m (m + 1) + masterQ m (m + 2) := by
    norm_num [Finset.sum_range_succ]
  rw [htail]
  have htel : (∑ k ∈ Finset.range m, masterQ m k) =
      ∑ k ∈ Finset.range m, (GQ m k - GQ m (k + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    exact tel m k (by omega)
  rw [htel]
  rw [Finset.sum_range_sub' (fun k => GQ m k) m]
  have h0 : GQ m 0 = 0 := by
    unfold GQ
    simp
  rw [h0]
  rw [boundary m]
  ring

lemma SQ_recurrence (m : ℕ) :
    9 * ((m : ℚ) + 1)^2 * SQ m - (10 * (m : ℚ)^2 + 30 * (m : ℚ) + 23) * SQ (m + 1)
        + ((m : ℚ) + 2)^2 * SQ (m + 2) = 0 := by
  have h := masterSum_zero m
  rw [masterSum_eq] at h
  exact h

/-- Casting `S` to `ℚ` gives `SQ`. -/
lemma S_cast (m : ℕ) : ((S m : ℤ) : ℚ) = SQ m := by
  unfold S SQ
  -- (∑ A m k : ℤ) : ℚ = ∑ (A m k : ℚ)
  norm_num

/-- The recurrence for the integer sums (shifted index form). -/
lemma S_recurrence (m : ℕ) :
    9 * (((m + 1 : ℕ) : ℤ)^2) * S m - (10 * ((m : ℕ) : ℤ)^2 + 30 * ((m : ℕ) : ℤ) + 23) * S (m + 1)
        + (((m + 2 : ℕ) : ℤ)^2) * S (m + 2) = 0 := by
  have hQ := SQ_recurrence m
  have hz : ((9 * (((m + 1 : ℕ) : ℤ)^2) * S m - (10 * ((m : ℕ) : ℤ)^2 + 30 * ((m : ℕ) : ℤ) + 23) * S (m + 1)
        + (((m + 2 : ℕ) : ℤ)^2) * S (m + 2)) : ℚ) = 0 := by
    -- push casts and use S_cast
    rw [S_cast m, S_cast (m+1), S_cast (m+2)]
    norm_num
    -- now goal in ℚ with coefficient casts still; push:
    -- ((m+1:ℕ):ℤ):ℚ etc.: norm_num may leave them; use ring with push_cast-like normalization:
    convert hQ using 1 <;> norm_num <;> ring
  exact_mod_cast hz


end ZagierC

open ZagierC

/-- The three-term recurrence of Zagier's sequence `C` (OEIS A002893):
`(n+1)² a(n+1) = (10n²+10n+3) a(n) − 9n² a(n−1)` for `n ≥ 1`, where
`a(m) = ∑ₖ C(m,k)²·C(2k,k)`. -/
theorem zagierC_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℤ) ^ 2 * (∑ k ∈ Finset.range (n + 2), (Nat.choose (n + 1) k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)) =
      ((10 : ℤ) * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) * (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ))
        - (9 : ℤ) * (n : ℤ) ^ 2 * (∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)) := by
  -- the three explicit sums are S(n+1), S(n), S(n-1) (definitionally up to range forms)
  have h1 : (∑ k ∈ Finset.range (n + 2), (Nat.choose (n + 1) k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)) = S (n + 1) := by
    rfl
  have h2 : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)) = S n := by
    rfl
  have h3 : (∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)) = S (n - 1) := by
    unfold S A
    rw [show (n - 1) + 1 = n by omega]
  -- the recurrence in n-form
  have hrec : 9 * ((n : ℕ) : ℤ)^2 * S (n - 1) - (10 * ((n : ℕ) : ℤ)^2 + 10 * ((n : ℕ) : ℤ) + 3) * S n
        + ((n + 1 : ℕ) : ℤ)^2 * S (n + 1) = 0 := by
    have h := S_recurrence (n - 1)
    have hn1 : (n - 1) + 1 = n := by omega
    have hn2 : (n - 1) + 2 = n + 1 := by omega
    rw [hn1, hn2] at h
    -- h: 9*(n:ℤ)^2*S(n-1) - (10*((n-1:ℕ):ℤ)^2 + 30*((n-1:ℕ):ℤ)+23)*S n + ((n+1:ℕ):ℤ)^2*S(n+1) = 0
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ n by exact hn)]
      norm_num
    rw [hcast] at h
    -- coefficient: 10(n-1)²+30(n-1)+23 = 10n²+10n+3 ; ring-normalize h to target shape
    convert h using 1 <;> ring
  -- now assemble: target says (n+1)²·S(n+1) = (10n²+10n+3)·S n − 9n²·S(n−1)
  rw [h1, h2, h3]
  -- hrec: 9n²·S(n-1) − (10n²+10n+3)·S n + (n+1)²·S(n+1) = 0
  nlinarith [hrec]

end Commons.Data.Nat.Choose