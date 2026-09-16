import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Lucas

namespace Commons.Data.Nat

/-- `k &&& n = k` iff every set bit of `k` is also a set bit of `n`. -/
lemma land_eq_self_iff_testBit (k n : ℕ) :
    k &&& n = k ↔ ∀ i, k.testBit i = true → n.testBit i = true := by
  constructor
  · intro h i hk
    have h1 : (k &&& n).testBit i = k.testBit i := by rw [h]
    rw [Nat.testBit_land, hk] at h1
    simpa using h1.symm
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_land]
    cases hb : k.testBit i with
    | false => simp
    | true => simp [h i hb]

/-- Splitting the "all bits" condition into the lowest bit and the remaining bits. -/
lemma testBit_forall_half_iff (k n : ℕ) :
    (∀ i, k.testBit i = true → n.testBit i = true) ↔
      (∀ i, (k / 2).testBit i = true → (n / 2).testBit i = true) ∧ k % 2 ≤ n % 2 := by
  have hmod : (k % 2 = 1 → n % 2 = 1) ↔ k % 2 ≤ n % 2 := by omega
  rw [← hmod]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun hk => ?_⟩
    · have h1 : k.testBit (i + 1) = true := by rwa [Nat.testBit_add_one]
      have h2 := h (i + 1) h1
      rwa [Nat.testBit_add_one] at h2
    · have h1 : k.testBit 0 = true := by simp [Nat.testBit_zero, hk]
      have h2 := h 0 h1
      simpa [Nat.testBit_zero] using h2
  · rintro ⟨h1, h0⟩ i hi
    rcases i with _ | j
    · have hk : k % 2 = 1 := by simpa [Nat.testBit_zero] using hi
      simp [Nat.testBit_zero, h0 hk]
    · have hk : (k / 2).testBit j = true := by simpa [Nat.testBit_add_one] using hi
      have h2 := h1 j hk
      simpa [Nat.testBit_add_one] using h2

/-- Bitwise recursion: `k` is a submask of `n` iff this holds for their halves and for
the lowest bits. -/
lemma land_eq_self_iff (k n : ℕ) :
    k &&& n = k ↔ (k / 2) &&& (n / 2) = k / 2 ∧ k % 2 ≤ n % 2 := by
  rw [land_eq_self_iff_testBit k n, testBit_forall_half_iff k n,
    ← land_eq_self_iff_testBit (k / 2) (n / 2)]

/-- Lucas mod 2, one binary digit at a time. -/
lemma choose_mod_two_odd (n k : ℕ) :
    Odd (n.choose k) ↔ Odd ((n / 2).choose (k / 2)) ∧ Odd ((n % 2).choose (k % 2)) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
  have key : Odd (n.choose k) ↔ Odd ((n / 2).choose (k / 2) * (n % 2).choose (k % 2)) := by
    rw [Nat.odd_iff, Nat.odd_iff, mul_comm, ← h]
  rw [key, Nat.odd_mul]

/-- The lowest digit: `(n % 2).choose (k % 2)` is odd iff the lowest bit of `k` is a bit of `n`. -/
lemma odd_choose_mod_two_iff (n k : ℕ) : Odd ((n % 2).choose (k % 2)) ↔ k % 2 ≤ n % 2 := by
  have hn := Nat.mod_two_eq_zero_or_one n
  have hk := Nat.mod_two_eq_zero_or_one k
  rcases hn with hn | hn <;> rcases hk with hk | hk <;>
    rw [hn, hk] <;> simp [Nat.odd_iff]

/-- Lucas mod 2: a binomial coefficient is odd iff the bits of `k` are contained in
the bits of `n`.

Proof strategy: `Mathlib/Data/Nat/Choose/Lucas.lean` gives
`Choose.choose_modEq_choose_mul_prod_range_choose` with `p = 2`:
`n.choose k ≡ (n / 2^a).choose (k / 2^a) * ∏ i ∈ range a, ((n / 2^i % 2).choose (k / 2^i % 2)) [ZMOD 2]`.
Reducing mod 2, each factor `(n_i).choose (k_i)` is `1` exactly when `k_i ≤ n_i`
(both digits lie in `{0,1}`), so `Odd (n.choose k) ↔ ∀ i, k / 2^i % 2 ≤ n / 2^i % 2`.
Then translate to `Nat.testBit`/`Nat.land`: `k &&& n = k` iff every bit of `k` is a bit of `n`
(see `Nat.testBit_land`, `Nat.testBit_eq_false_of_lt`, `Nat.zero_of_testBit_eq_false`,
`Nat.lt_of_testBit` in `Mathlib/Data/Nat/Bitwise.lean`). Choosing `a` large
(e.g. `a = n + k + 1`) kills the leftover factor. -/
theorem choose_odd_iff (n k : ℕ) : Odd (n.choose k) ↔ k &&& n = k := by
  revert k
  refine Nat.strong_induction_on n ?_
  intro n ih k
  rcases n with _ | n
  · rcases k with _ | k
    · simp
    · simp
  · rw [choose_mod_two_odd, ih (Nat.succ n / 2) (Nat.div_lt_self (Nat.succ_pos n) one_lt_two),
      odd_choose_mod_two_iff]
    exact (land_eq_self_iff k (Nat.succ n)).symm

end Commons.Data.Nat