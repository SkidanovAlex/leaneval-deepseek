import Mathlib

set_option autoImplicit false
open Finset

/-!
# N2, part 1: the arithmetic core of Step 3 of Ngo Dac §5.3

Ngo Dac's Step 3 (Annals 194 (2021), §5.3) runs the following arithmetic/combinatorial argument
after the analytic input `f_t(θ) ∈ K` has been converted, via the ζ_A ↔ CMPL bridge, into the
statement that `s_{i(k+1)} + ⋯ + s_{iℓ_i}` is divisible by `q-1` for the relevant `k`:

* from `(q-1) ∣ s_{i(k+1)}+⋯+s_{iℓ_i}` for all `k ≥ m_i+1` he concludes `s_{ik} = q-1` for
  `k ≥ m_i+2` (this is `Commons.NumberTheory.MZV.suffix_dvd_eq_pred`, requested from the fleet:
  descending induction, subtracting consecutive suffix divisibilities);
* letting `m = max_i m_i` and picking two tuples `s_1 ≠ s_2` with `m_1 = m_2 = m`, he finds that
  both have all entries `= q-1` from index `m+2` on, that their prefixes up to `m` agree while
  `s_{1(m+1)} ≠ s_{2(m+1)}`, and that they have the same weight.  Writing the weight equality as

    `s_{1(m+1)} + k(q-1) = s_{2(m+1)} + k'(q-1)`   (`k, k'` the numbers of trailing `q-1`'s),

  it follows that `s_{1(m+1)} ≡ s_{2(m+1)} (mod q-1)`, and since both lie in `[1, q-1]` this forces
  `s_{1(m+1)} = s_{2(m+1)}` — a contradiction.

This file records the two arithmetic facts used: the "`dvd` + size bound ⟹ equality" step (used for
both the suffix argument's conclusion and the final congruence step) and the reduction
`a + k(q-1) = a' + k'(q-1)` with `a, a' ≤ q-1` to `a = a'`.
-/

/-- If `q-1` divides `x` and `0 < x ≤ q-1` (with `q ≥ 2`), then `x = q-1`. -/
theorem eq_pred_of_dvd_of_le {q x : ℕ} (hq : 2 ≤ q) (hdvd : (q - 1) ∣ x) (hpos : 0 < x)
    (hle : x ≤ q - 1) : x = q - 1 := by
  obtain ⟨k, hk⟩ := hdvd
  have hq1 : 0 < q - 1 := by omega
  have : k = 1 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · by_contra hk1
      have h2 : 2 ≤ k := by omega
      nlinarith [Nat.mul_le_mul_left (q - 1) h2]
  subst this
  omega

/-- Congruence cancellation: if `a, a' ∈ [1, q-1]` and `a + k·(q-1) = a' + k'·(q-1)` then
`a = a'`.  (This is the final step of Ngo Dac's §5.3 argument: the two weights agree, the tails of
trailing `q-1`'s have possibly different lengths, and the entries at the first differing position
both lie in `[1, q-1]`.) -/
theorem eq_of_add_mul_pred_eq {q a a' k k' : ℕ} (hq : 2 ≤ q) (ha : 1 ≤ a) (ha' : 1 ≤ a')
    (hale : a ≤ q - 1) (ha'le : a' ≤ q - 1)
    (h : a + k * (q - 1) = a' + k' * (q - 1)) : a = a' := by
  have hmod : a % (q - 1) = a' % (q - 1) := by
    rw [← Nat.add_mul_mod_self_right a k (q - 1), h, Nat.add_mul_mod_self_right a' k' (q - 1)]
  by_cases h1 : a < q - 1
  · rw [Nat.mod_eq_of_lt h1] at hmod
    rcases lt_or_eq_of_le ha'le with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hmod
      exact hmod
    · rw [h2, Nat.mod_self] at hmod
      omega
  · have haeq : a = q - 1 := by omega
    have hzero : a' % (q - 1) = 0 := by rw [← hmod, haeq, Nat.mod_self]
    have hdvd : (q - 1) ∣ a' := Nat.dvd_of_mod_eq_zero hzero
    have h' : a' = q - 1 := eq_pred_of_dvd_of_le hq hdvd (by omega) ha'le
    omega
