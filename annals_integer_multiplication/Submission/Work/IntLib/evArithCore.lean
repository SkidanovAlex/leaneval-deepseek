import Mathlib
import Submission.Work.IntLib.evArith

/-!
# The non-empty arithmetic of the `evalPoly` budget

Fallback (self-contained) proof of `Work.IntLib.evArithNe`, the `hs ≠ []` case of the pure
arithmetic behind the assembled `evalPoly` word.  The statement is exactly the one requested at
`Submission/Work/IntLib/evArithNe.lean`; this copy exists so that the assembly in `chunkEv.lean`
does not have to wait for it.

Contents:

* `arithCoreAlt` — the whole numerical argument, with abstract atoms (no lists involved);
* `sum_coe_map_alt`, `sum_size_le_nat_alt`, `sum_size_le_isz_alt` — the list facts that
  instantiate it;
* `one_le_length_of_ne_nil_alt`, `two_le_isz_alt` — the two elementary side conditions.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.IntLib

open HvdH

/-- Summing a function over the coerced list `(↑l : List ℤ)` is summing `f ∘ (↑·)` over `l`. -/
theorem sum_coe_map_alt (l : List ℕ) :
    (((l : List ℤ).map fun z => HvdH.isz z)).sum
      = ((l.map fun h : ℕ => HvdH.isz (h : ℤ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simpa [List.bind_eq_flatMap] using ih

/-- `Σ h.size ≤ Σ isz h` over a chain of naturals (the `ℕ`-indexed form, no coercion). -/
theorem sum_size_le_nat_alt (l : List ℕ) :
    (l.map fun h => h.size).sum ≤ (l.map fun h : ℕ => HvdH.isz (h : ℤ)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a.size ≤ HvdH.isz (a : ℤ) := by simp [HvdH.isz]
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- `Σ h.size ≤ Σ isz h` in the exact form of the `polyBudget` body. -/
theorem sum_size_le_isz_alt (l : List ℕ) :
    (l.map fun h => h.size).sum ≤ (l.map fun h => HvdH.isz (h : ℤ)).sum := by
  rw [sum_coe_map_alt l]
  exact sum_size_le_nat_alt l

/-- `Σ h.size ≤ Σ isz h` over a chain of naturals. -/
theorem sum_size_le_coe_alt (l : List ℕ) :
    (l.map fun h => h.size).sum ≤ (((l : List ℤ).map fun z => HvdH.isz z)).sum := by
  rw [sum_coe_map_alt]
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a.size ≤ HvdH.isz (a : ℤ) := by simp [HvdH.isz]
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- The length of a non-empty list is positive. -/
theorem one_le_length_of_ne_nil_alt {l : List ℕ} (h : l ≠ []) : 1 ≤ l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

/-- The size of the base is at least two. -/
theorem two_le_isz_alt (b : ℕ) : 2 ≤ HvdH.isz (b : ℤ) := by
  rw [Work.IntLib.isz_nat]
  omega

/-- The numerical core: if the three phases' costs are bounded as stated (`T` is the sum of the
digit sizes, `L` the number of digits, `Z` the size of the base, `S` the budget's sum), and
`1 ≤ L`, `2 ≤ Z`, then their sum fits into `polyK`'s bracket times the budget. -/
theorem arithCoreAlt (S T L Z b Wl LOl n1 n2 n3 KP KCM KR KEP KE KC KA KZ : ℕ)
    (hTS : T ≤ S) (hL : 1 ≤ L) (hZ : 2 ≤ Z)
    (hW : Wl ≤ 3 * b + 1) (hLO : LOl ≤ L * (b + 1))
    (hn1 : n1 ≤ KP * (KCM + KR + 1) * (T + L * (b + 2) + Z + 100))
    (hn2 : n2 ≤ (10 * KR + 10 * KC + 40 * KA + 50) * (T + L * (b + 2) + 1))
    (hn3 : n3 ≤ KEP * (KE + 40) * (Wl + LOl + (L + 1) * (b + 1) + Z + 40)) :
    n1 + n2 + n3 + 2 ≤
      1000 * (KP * (KCM + KR + 1) + KEP * (KE + 40) + (KR + KC + KA + KZ + 20) + 1)
        * (S + L * (b + 1) + Z + 1) := by
  set B : ℕ := S + L * (b + 1) + Z + 1 with hB
  have hSle : S ≤ B := by omega
  have hLle : L * (b + 1) ≤ B := by omega
  have hZle : Z ≤ B := by omega
  have hB1 : 1 ≤ B := by omega
  have hb1 : b + 1 ≤ B := by
    have h : 1 * (b + 1) ≤ L * (b + 1) := Nat.mul_le_mul_right (b + 1) hL
    have h' : 1 * (b + 1) = b + 1 := by ring
    rw [h'] at h
    exact le_trans h hLle
  have hTle : T ≤ B := le_trans hTS hSle
  have hLb2 : L * (b + 2) ≤ 2 * B := by
    have h : L * (b + 2) ≤ L * (2 * (b + 1)) := Nat.mul_le_mul_left L (by omega)
    have h' : L * (2 * (b + 1)) = 2 * (L * (b + 1)) := by ring
    rw [h'] at h
    exact le_trans h (Nat.mul_le_mul_left 2 hLle)
  have hK1 : T + L * (b + 2) + Z + 100 ≤ 104 * B := by
    have h100 : 100 ≤ 100 * B := by
      have h := Nat.mul_le_mul_left 100 hB1
      simpa using h
    omega
  have hK2 : T + L * (b + 2) + 1 ≤ 4 * B := by omega
  have hK3 : Wl + LOl + (L + 1) * (b + 1) + Z + 40 ≤ 47 * B := by
    have hW3 : Wl ≤ 3 * B := by omega
    have hLO3 : LOl ≤ B := le_trans hLO hLle
    have h41 : (L + 1) * (b + 1) ≤ 2 * B := by
      have h : (L + 1) * (b + 1) = L * (b + 1) + (b + 1) := by ring
      omega
    have h40 : 40 ≤ 40 * B := by
      have h := Nat.mul_le_mul_left 40 hB1
      simpa using h
    omega
  have hn1' : n1 ≤ (104 * (KP * (KCM + KR + 1))) * B := by
    have h := Nat.mul_le_mul_left (KP * (KCM + KR + 1)) hK1
    have h2 : (KP * (KCM + KR + 1)) * (104 * B)
        = (104 * (KP * (KCM + KR + 1))) * B := by ring
    rw [h2] at h
    exact le_trans hn1 h
  have hn2' : n2 ≤ (4 * (10 * KR + 10 * KC + 40 * KA + 50)) * B := by
    have h := Nat.mul_le_mul_left (10 * KR + 10 * KC + 40 * KA + 50) hK2
    have h2 : (10 * KR + 10 * KC + 40 * KA + 50) * (4 * B)
        = (4 * (10 * KR + 10 * KC + 40 * KA + 50)) * B := by ring
    rw [h2] at h
    exact le_trans hn2 h
  have hn3' : n3 ≤ (47 * (KEP * (KE + 40))) * B := by
    have h := Nat.mul_le_mul_left (KEP * (KE + 40)) hK3
    have h2 : (KEP * (KE + 40)) * (47 * B) = (47 * (KEP * (KE + 40))) * B := by ring
    rw [h2] at h
    exact le_trans hn3 h
  have hsum : n1 + n2 + n3
      ≤ (104 * (KP * (KCM + KR + 1)) + 4 * (10 * KR + 10 * KC + 40 * KA + 50)
          + 47 * (KEP * (KE + 40))) * B := by
    have h := add_le_add (add_le_add hn1' hn2') hn3'
    have h2 : (104 * (KP * (KCM + KR + 1))) * B
          + (4 * (10 * KR + 10 * KC + 40 * KA + 50)) * B
          + (47 * (KEP * (KE + 40))) * B
        = (104 * (KP * (KCM + KR + 1)) + 4 * (10 * KR + 10 * KC + 40 * KA + 50)
          + 47 * (KEP * (KE + 40))) * B := by ring
    rw [h2] at h
    exact h
  have hC : 104 * (KP * (KCM + KR + 1)) + 4 * (10 * KR + 10 * KC + 40 * KA + 50)
        + 47 * (KEP * (KE + 40)) + 2
      ≤ 1000 * (KP * (KCM + KR + 1) + KEP * (KE + 40) + (KR + KC + KA + KZ + 20) + 1) := by
    omega
  have hfin : n1 + n2 + n3 + 2
      ≤ 1000 * (KP * (KCM + KR + 1) + KEP * (KE + 40) + (KR + KC + KA + KZ + 20) + 1) * B := by
    have h2B : 2 ≤ 2 * B := by
      have h := Nat.mul_le_mul_left 2 hB1
      simpa using h
    have h : n1 + n2 + n3 + 2
        ≤ (104 * (KP * (KCM + KR + 1)) + 4 * (10 * KR + 10 * KC + 40 * KA + 50)
          + 47 * (KEP * (KE + 40))) * B + 2 * B := by omega
    have h2 : (104 * (KP * (KCM + KR + 1)) + 4 * (10 * KR + 10 * KC + 40 * KA + 50)
          + 47 * (KEP * (KE + 40))) * B + 2 * B
        = (104 * (KP * (KCM + KR + 1)) + 4 * (10 * KR + 10 * KC + 40 * KA + 50)
          + 47 * (KEP * (KE + 40)) + 2) * B := by ring
    rw [h2] at h
    exact le_trans h (Nat.mul_le_mul_right B hC)
  rw [hB]
  exact hfin

end Work.IntLib
