import Submission.ZagierHoffmanProof.ATIncr

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Polynomial
open scoped BigOperators

/-!
# The digit-by-digit recursion for the Anderson–Thakur coefficients

This file proves the *one-digit* increment lemma: for `a + 1 ≤ q - 1`,

  `atCoeff (atIndex n (oneDigit (a+1))) = R_(n-1) * atCoeff (atIndex n (oneDigit a))`,

which is Chen's "Step 1" (the case `N_i = 0` for `i ≥ 1`) and the base of the induction on the
digits.  It uses the defining recursion of the `atCoeff` sequence and Chen's claim `atClaimR`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The shape with a single digit `a` at slot `0`. -/
def oneDigit (a : ℕ) : ℕ → ℕ := fun i => if i = 0 then a else 0

@[simp] lemma oneDigit_apply (a i : ℕ) : oneDigit a i = if i = 0 then a else 0 := rfl

lemma oneDigit_sum (n a : ℕ) (hn : 1 ≤ n) : (∑ i ∈ Finset.range n, oneDigit a i) = a := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hk : k = 0
    · subst hk; simp [oneDigit]
    · rw [oneDigit_apply, if_neg hk, add_zero]
      exact ih (by omega)

lemma oneDigit_weighted (n a : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range n, oneDigit a i * Nat.card F ^ i) = a := by
  induction n with
  | zero => omega
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hk : k = 0
    · subst hk; simp [oneDigit]
    · rw [oneDigit_apply, if_neg hk, zero_mul, add_zero]
      exact ih (by omega)

lemma shiftShape_oneDigit (a : ℕ) : shiftShape (oneDigit a) 0 1 = oneDigit (a + 1) := by
  funext i
  by_cases h0 : i = 0 <;> simp [shiftShape, oneDigit, h0]

lemma oneDigit_shiftShape {j : ℕ} (hj : 1 ≤ j) (a : ℕ) :
    shiftShape (oneDigit a) j 1 = fun i => if i = 0 then a else if i = j then 1 else 0 := by
  have hj0 : ¬ (j = 0) := by omega
  have hj0' : ¬ ((0 : ℕ) = j) := by omega
  funext i
  by_cases h0 : i = 0 <;> simp [shiftShape, oneDigit, h0, hj0, hj0']

/-- `R_0 = 1`. -/
@[simp] lemma atR_zero : atR F 0 = 1 := by
  rw [atR, atPk, atL, carlitzL_zero]
  simp

/-- Every `atIndex`-index is positive for a shape with `∑ N_i ≤ q - 2`, `n ≥ 1`. -/
lemma atIndex_pos (n a : ℕ) (hn : 1 ≤ n) (ha : a ≤ Nat.card F - 2) :
    0 < Nat.card F ^ n - 1 - a := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  have h1 : Nat.card F ≤ Nat.card F ^ n := by
    simpa using pow_le_pow_right₀ hq1 hn
  omega

/-- The recursion for `atCoeff` at the index `q^n - 1 - a`, with the sum over the `n` lowest
`q`-powers. -/
lemma atCoeff_eq_sum_range {n a : ℕ} (hn : 1 ≤ n) (ha : a ≤ Nat.card F - 2) :
    atCoeff F (Nat.card F ^ n - 1 - a)
      = ∑ j ∈ Finset.range n, atE F j
          * atCoeff F (Nat.card F ^ n - 1 - a - Nat.card F ^ j) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hne : Nat.card F ^ n - 1 - a ≠ 0 := ne_of_gt (atIndex_pos F n a hn ha)
  rw [atCoeff_succ F hne]
  have hfilt : (Finset.range (Nat.card F ^ n - 1 - a + 1)).filter
        (fun j => Nat.card F ^ j ≤ Nat.card F ^ n - 1 - a) = Finset.range n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hj⟩
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : Nat.card F ^ n ≤ Nat.card F ^ j := pow_le_pow_right₀ hq1 hcon
      have h2 : Nat.card F ^ n - 1 - a < Nat.card F ^ n := by
        have h3 : Nat.card F ^ n - 1 - a ≤ Nat.card F ^ n - 1 := Nat.sub_le _ _
        have h4 : 1 ≤ Nat.card F ^ n := Nat.one_le_pow n (Nat.card F) (by omega)
        omega
      omega
    · intro hj
      have hjn : j ≤ n - 1 := by omega
      have hkey : Nat.card F ^ (n - 1) + (Nat.card F - 1) ≤ Nat.card F ^ n := by
        have hone : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
        calc Nat.card F ^ (n - 1) + (Nat.card F - 1)
            ≤ Nat.card F ^ (n - 1) + Nat.card F ^ (n - 1) * (Nat.card F - 1) :=
              Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _
          _ = Nat.card F ^ (n - 1) * ((Nat.card F - 1) + 1) := by rw [mul_add, mul_one, add_comm]
          _ = Nat.card F ^ n := by
              rw [show (Nat.card F - 1) + 1 = Nat.card F from by omega]
              rw [← pow_succ, show n - 1 + 1 = n from by omega]
      have hjA : Nat.card F ^ j ≤ Nat.card F ^ n - 1 - a := by
        have h1 : Nat.card F ^ j ≤ Nat.card F ^ (n - 1) := pow_le_pow_right₀ hq1 hjn
        have h2 : 1 + a ≤ Nat.card F ^ n := by
          have h3 : Nat.card F ^ n ≥ Nat.card F := by simpa using pow_le_pow_right₀ hq1 hn
          omega
        rw [Nat.sub_sub]
        refine (Nat.le_sub_iff_add_le h2).mpr ?_
        omega
      have hjle : j ≤ Nat.card F ^ j := by
        have h2 : 2 ^ j ≤ Nat.card F ^ j := Nat.pow_le_pow_left hq2 j
        have h3 : j < 2 ^ j := Nat.lt_two_pow_self (n := j)
        omega
      exact ⟨by omega, hjA⟩
  rw [hfilt]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [← atE_apply F j]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

@[simp] lemma atE_zero : atE F 0 = 1 := by
  rw [atE, atGamma_zero, atD]
  simp

/-- The shape `oneDigit a` shifted in a positive slot stays below `q^n - 1`. -/
lemma oneDigit_shift_le (n a j : ℕ) (hn : 1 ≤ n) (ha : a ≤ Nat.card F - 2) (hj : j ≤ n - 1) :
    (∑ i ∈ Finset.range n, oneDigit a i * Nat.card F ^ i) + Nat.card F ^ j
      ≤ Nat.card F ^ n - 1 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  rw [oneDigit_weighted F n a hn]
  have hkey : Nat.card F ^ (n - 1) + (Nat.card F - 1) ≤ Nat.card F ^ n := by
    have hone : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
    calc Nat.card F ^ (n - 1) + (Nat.card F - 1)
        ≤ Nat.card F ^ (n - 1) + Nat.card F ^ (n - 1) * (Nat.card F - 1) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _
      _ = Nat.card F ^ (n - 1) * ((Nat.card F - 1) + 1) := by rw [mul_add, mul_one, add_comm]
      _ = Nat.card F ^ n := by
          rw [show (Nat.card F - 1) + 1 = Nat.card F from by omega]
          rw [← pow_succ, show n - 1 + 1 = n from by omega]
  have hj' : Nat.card F ^ j ≤ Nat.card F ^ (n - 1) := pow_le_pow_right₀ hq1 hj
  omega

omit [Field F] [Finite F] in
/-- Reindexing `∑_{i ∈ Icc 1 n}` as `∑_{i ∈ range n}` of the shifted function. -/
lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ i ∈ Finset.Icc 1 n, f i) = ∑ i ∈ Finset.range n, f (i + 1) := by
  have hset : Finset.Icc 1 n = (Finset.range n).image (fun i => i + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  have h : a + 1 = b + 1 := hab
  omega

/-- ★ **The one-digit increment**: `atCoeff` at `q^n - 1 - (a+1)` is `R_(n-1)` times `atCoeff` at
`q^n - 1 - a`.  This is Chen's "Step 1". -/
theorem oneDigit_increment (n : ℕ) (hn : 2 ≤ n) (a : ℕ) (ha : a + 1 ≤ Nat.card F - 1)
    (hincr : ∀ (j : ℕ) (M : ℕ → ℕ), (∑ i ∈ Finset.range n, M i ≤ Nat.card F - 2) → 1 ≤ j →
      j ≤ n - 1 →
      atCoeff F (atIndex F n (shiftShape M j 1)) = atR F (n - 1 - j) ^ (Nat.card F ^ j) * atCoeff F (atIndex F n M)) :
    atCoeff F (atIndex F n (oneDigit (a + 1)))
      = atR F (n - 1) * atCoeff F (atIndex F n (oneDigit a)) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hn1 : 1 ≤ n := by omega
  have ha' : a ≤ Nat.card F - 2 := by omega
  have hidxA : atIndex F n (oneDigit a) = Nat.card F ^ n - 1 - a := by
    rw [atIndex, oneDigit_weighted F n a hn1]
  have hsum : atCoeff F (atIndex F n (oneDigit a))
      = ∑ j ∈ Finset.range n,
          atE F j * atCoeff F (atIndex F n (shiftShape (oneDigit a) j 1)) := by
    rw [hidxA, atCoeff_eq_sum_range F hn1 ha']
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hidx : atIndex F n (shiftShape (oneDigit a) j 1)
        = Nat.card F ^ n - 1 - a - Nat.card F ^ j := by
      rw [atIndex_shiftShape_one F n (oneDigit a) j (by omega)
        (oneDigit_shift_le F n a j hn1 ha' (by omega)), hidxA]
    rw [hidx]
  -- the term at `j = 0`
  have hf0 : atE F 0 * atCoeff F (atIndex F n (shiftShape (oneDigit a) 0 1))
      = atCoeff F (atIndex F n (oneDigit (a + 1))) := by
    rw [atE_zero, one_mul, shiftShape_oneDigit]
  -- the tail
  have htail : (∑ j ∈ Finset.Icc 1 (n - 1),
        atE F j * atCoeff F (atIndex F n (shiftShape (oneDigit a) j 1)))
      = (1 - atR F (n - 1)) * atCoeff F (atIndex F n (oneDigit a)) := by
    have hS : (∑ j ∈ Finset.Icc 1 (n - 1), atE F j * atR F (n - 1 - j) ^ (Nat.card F ^ j))
        = 1 - atR F (n - 1) := by
      have := atClaimR F n
      rw [← this]; ring
    rw [show (∑ j ∈ Finset.Icc 1 (n - 1),
          atE F j * atCoeff F (atIndex F n (shiftShape (oneDigit a) j 1)))
        = ∑ j ∈ Finset.Icc 1 (n - 1), (atE F j * atR F (n - 1 - j) ^ (Nat.card F ^ j))
            * atCoeff F (atIndex F n (oneDigit a)) from by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [hincr j (oneDigit a) ?_ hj.1 hj.2]
      · ring
      · rw [oneDigit_sum n a hn1]; exact ha']
    rw [← Finset.sum_mul, hS]
  -- split the sum
  have hsplit : (∑ j ∈ Finset.range n,
        atE F j * atCoeff F (atIndex F n (shiftShape (oneDigit a) j 1)))
      = atCoeff F (atIndex F n (oneDigit (a + 1)))
        + (∑ j ∈ Finset.Icc 1 (n - 1),
            atE F j * atCoeff F (atIndex F n (shiftShape (oneDigit a) j 1))) := by
    rw [show Finset.range n = Finset.range (n - 1 + 1) from by rw [Nat.sub_add_cancel hn1],
      Finset.sum_range_succ', hf0,
      ← sum_Icc_one_eq_sum_range (n - 1)
        (fun j => atE F j * atCoeff F (atIndex F n (shiftShape (oneDigit a) j 1)))]
    ring
  -- conclude
  have hV : atCoeff F (atIndex F n (oneDigit a))
      = atCoeff F (atIndex F n (oneDigit (a + 1)))
        + (1 - atR F (n - 1)) * atCoeff F (atIndex F n (oneDigit a)) := by
    conv_lhs => rw [hsum, hsplit, htail]
  have h2 : atCoeff F (atIndex F n (oneDigit a))
      - (1 - atR F (n - 1)) * atCoeff F (atIndex F n (oneDigit a))
      = atCoeff F (atIndex F n (oneDigit (a + 1))) := (sub_eq_iff_eq_add).mpr hV
  have h3 : atR F (n - 1) * atCoeff F (atIndex F n (oneDigit a))
      = atCoeff F (atIndex F n (oneDigit (a + 1))) := by
    rw [show atCoeff F (atIndex F n (oneDigit a))
        - (1 - atR F (n - 1)) * atCoeff F (atIndex F n (oneDigit a))
        = atR F (n - 1) * atCoeff F (atIndex F n (oneDigit a)) from by ring] at h2
    exact h2
  exact h3.symm

end ZagierHoffmanPositiveChar
