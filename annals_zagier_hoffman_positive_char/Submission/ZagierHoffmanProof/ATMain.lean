import Submission.ZagierHoffmanProof.ATPeel
import Submission.ZagierHoffmanProof.DescentGenCor

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Consequences of Chen's Theorem 3.1

Corollaries of `atCoeff_atIndex_eq_atForm` in the classical range of Anderson–Thakur
polynomials, together with concrete regression checks.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The shape with a single `1` in slot `k`. -/
def singleDigit (k : ℕ) : ℕ → ℕ := fun i => if i = k then 1 else 0

@[simp] lemma singleDigit_apply (k i : ℕ) : singleDigit k i = if i = k then 1 else 0 := rfl

lemma singleDigit_sum_range {n k : ℕ} (hk : k < n) :
    (∑ i ∈ Finset.range n, singleDigit k i) ≤ Nat.card F - 1 := by
  have h1 : (∑ i ∈ Finset.range n, singleDigit k i) = 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hi; simp [singleDigit, hi]
    · intro h; exact absurd (Finset.mem_range.mpr hk) h
  rw [h1]
  exact Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num : 1 < 2) (carlitz_card_ge_two F))

lemma atIndex_singleDigit {n k : ℕ} (hk : k < n) :
    atIndex F n (singleDigit k) = Nat.card F ^ n - 1 - Nat.card F ^ k := by
  rw [atIndex, Finset.sum_eq_single k]
  · rw [singleDigit_apply, if_pos rfl, one_mul]
  · intro i _ hi; rw [singleDigit_apply, if_neg hi, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hk) h

lemma atForm_singleDigit_of_lt {n k : ℕ} (hk : k < n - 1) :
    atForm F n (singleDigit k) = atR F (n - 1 - k) ^ (Nat.card F ^ k) := by
  rw [atForm, Finset.prod_eq_single k]
  · rw [singleDigit_apply, if_pos rfl, one_mul]
  · intro i _ hi; rw [singleDigit_apply, if_neg hi, zero_mul, pow_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hk) h

lemma atForm_singleDigit_of_ge {n k : ℕ} (hk : n - 1 ≤ k) :
    atForm F n (singleDigit k) = 1 := by
  refine Finset.prod_eq_one (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [singleDigit_apply, if_neg (by omega), zero_mul, pow_zero]

/-- **The classical case `H_{q^n - q^k - 1} = Γ_{q^n-q^k}`** (`k ≤ n-1`): for `k = n-1` this is
Chen's `H_{q^2-q-1} = Γ_{q^2-q}`. -/
theorem atCoeff_card_pow_sub_card_pow_sub_one (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n - 1) (hk' : k < n) :
    atCoeff F (Nat.card F ^ n - 1 - Nat.card F ^ k) = atR F (n - 1 - k) ^ (Nat.card F ^ k) := by
  rw [← atIndex_singleDigit F hk']
  rcases eq_or_lt_of_le hk with h | h
  · subst h
    rw [atCoeff_atIndex_eq_atForm F n hn (singleDigit (n - 1)) (singleDigit_sum_range F (by omega)),
      atForm_singleDigit_of_ge F (le_refl _), Nat.sub_self, atR_zero, one_pow]
  · rw [atCoeff_atIndex_eq_atForm F n hn (singleDigit k) (singleDigit_sum_range F hk'),
      atForm_singleDigit_of_lt F h]

/-- Chen's `H_{q^2-q-1} = Γ_{q^2-q}`. -/
theorem atCoeff_card_sq_sub_card_sub_one :
    atCoeff F (Nat.card F ^ 2 - Nat.card F - 1) = 1 := by
  have h := atCoeff_card_pow_sub_card_pow_sub_one F 2 1 (by norm_num) (by norm_num) (by norm_num)
  rw [pow_one, show Nat.card F ^ 2 - 1 - Nat.card F = Nat.card F ^ 2 - Nat.card F - 1 from by omega,
    show (2 : ℕ) - 1 - 1 = 0 from rfl, atR_zero, one_pow] at h
  exact h

/-- `H_{q^n-1} = Γ_{q^n}` (the all-zero shape). -/
theorem atCoeff_card_pow_sub_one' (n : ℕ) (hn : 1 ≤ n) :
    atCoeff F (Nat.card F ^ n - 1) = 1 := by
  have h := atCoeff_atIndex_eq_atForm F n hn (fun _ => 0) (by
    rw [Finset.sum_eq_zero (fun i _ => rfl)]
    exact Nat.zero_le _)
  have h1 : atIndex F n (fun _ : ℕ => 0) = Nat.card F ^ n - 1 := by
    rw [atIndex, Finset.sum_eq_zero (fun i _ => by simp), Nat.sub_zero]
  rw [h1] at h
  rw [h, atForm]
  exact Finset.prod_eq_one (fun i _ => by simp)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

-- Regression checks over `ZMod 2`.
example : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]

example : atCoeff (ZMod 2) (Nat.card (ZMod 2) ^ 3 - 1 - Nat.card (ZMod 2) ^ 1)
    = atR (ZMod 2) 1 ^ Nat.card (ZMod 2) := by
  have h := atCoeff_card_pow_sub_card_pow_sub_one (ZMod 2) 3 1 (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (3 : ℕ) - 1 - 1 = 1 from rfl] at h
  simpa using h

example : atCoeff (ZMod 2) (Nat.card (ZMod 2) ^ 2 - Nat.card (ZMod 2) - 1) = 1 :=
  atCoeff_card_sq_sub_card_sub_one (ZMod 2)

example : atCoeff (ZMod 2) (Nat.card (ZMod 2) ^ 4 - 1) = 1 :=
  atCoeff_card_pow_sub_one' (ZMod 2) 4 (by norm_num)

example (N : ℕ → ℕ) (hN : (∑ i ∈ Finset.range 3, N i) ≤ Nat.card (ZMod 2) - 1) :
    atCoeff (ZMod 2) (atIndex (ZMod 2) 3 N) = atForm (ZMod 2) 3 N :=
  atCoeff_atIndex_eq_atForm (ZMod 2) 3 (by norm_num) N hN

-- and over `ZMod 3`
example : atCoeff (ZMod 3) (Nat.card (ZMod 3) ^ 2 - Nat.card (ZMod 3) - 1) = 1 :=
  atCoeff_card_sq_sub_card_sub_one (ZMod 3)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- **Chen's Theorem 3.1 in the product form over `Icc 1 (n-1)`.** -/
theorem atCoeff_atIndex_eq_prod (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    atCoeff F (atIndex F n N)
      = (∏ j ∈ Finset.Icc 1 (n - 1), atR F (n - 1 - j) ^ (N j * Nat.card F ^ j))
        * atR F (n - 1) ^ N 0 := by
  rw [atCoeff_atIndex_eq_atForm F n hn N hN]
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    rw [atForm, Finset.range_zero, Finset.prod_empty,
      show (1 : ℕ) - 1 = 0 from rfl, Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1),
      Finset.prod_empty, atR_zero, one_pow, one_mul]
  · rw [atForm_eq_prod F n h N]

/-- **The Anderson–Thakur polynomial form**: with `m = atIndex n N` the polynomial `α_(m+1)` is the
Carlitz-`Γ` multiple of the closed form. -/
theorem atAlpha_atIndex (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    atAlpha F (atIndex F n N + 1)
      = algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzGamma F (atIndex F n N + 1)))
        * atForm F n N := by
  rw [atAlpha, show atIndex F n N + 1 - 1 = atIndex F n N from Nat.add_sub_cancel _ _,
    atCoeff_atIndex_eq_atForm F n hn N hN]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

omit [Field F] [Finite F] in
lemma card_mul_sq_sub_card_sub_one {q : ℕ} (hq : 2 ≤ q) :
    q * (q ^ 2 - q - 1) + (q - 1) = q ^ 3 - q ^ 2 - 1 := by
  have hq1 : 1 ≤ q := by omega
  have hA : q + 1 ≤ q ^ 2 := by nlinarith
  have hB : q ^ 2 + 1 ≤ q ^ 3 := by nlinarith
  have key : ((q * (q ^ 2 - q - 1) + (q - 1) : ℕ) : ℤ) = ((q ^ 3 - q ^ 2 - 1 : ℕ) : ℤ) := by
    have e1 : ((q ^ 2 - q - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q ^ 2 - q), Nat.cast_sub (by omega : q ≤ q ^ 2)]
      push_cast
      ring
    have e2 : ((q ^ 3 - q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 3 - (q : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q ^ 3 - q ^ 2), Nat.cast_sub (by omega : q ^ 2 ≤ q ^ 3)]
      push_cast
      ring
    rw [Nat.cast_add, Nat.cast_mul, e1, Nat.cast_sub hq1, e2]
    push_cast
    ring
  exact Nat.cast_injective key

/-- `atCoeff` at `q^3 - q^2 - 1` is `1`, via the closed formula (the shape `(0,0,1)`). -/
theorem atCoeff_card_cube_sub_card_sq_sub_one' :
    atCoeff F (Nat.card F ^ 3 - Nat.card F ^ 2 - 1) = 1 := by
  have h := atCoeff_card_pow_sub_card_pow_sub_one F 3 2 (by norm_num) (by norm_num) (by norm_num)
  rw [Nat.sub_right_comm, show (3 : ℕ) - 1 - 2 = 0 from rfl, atR_zero, one_pow] at h
  exact h

/-- The same value, via the **independent** one-residue descent `atCoeff_mul_card_add_pred` and
Chen's `q^2-q-1` case — a cross-check of the closed formula against the descent. -/
theorem atCoeff_card_cube_sub_card_sq_sub_one :
    atCoeff F (Nat.card F ^ 3 - Nat.card F ^ 2 - 1) = 1 := by
  have hq : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have h1 := atCoeff_card_sq_sub_card_sub_one F
  have h := atCoeff_mul_card_add_pred F (Nat.card F ^ 2 - Nat.card F - 1)
  rw [h1, card_mul_sq_sub_card_sub_one hq] at h
  simpa using h

end ZagierHoffmanPositiveChar
