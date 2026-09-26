import Mathlib

/-!
# Extracting the `i`-th base-`b` digit of a positional sum

For digits `d j < b` with `b ≥ 2`, the number `∑_{j<n} d j * b^j` has base-`b`
expansion `d 0 d 1 … d (n-1)` (little-endian).  Consequently the `i`-th digit,
read off as `(∑_{j<n} d j * b^j) / b^i % b`, is exactly `d i`.

The proof goes through `Nat.ofDigits`, the list encoding of base-`b` numbers:
`∑_{j<n} d j * b^j = Nat.ofDigits b ((List.range n).map d)`, and Mathlib's
`Nat.ofDigits_div_pow_eq_ofDigits_drop` shows that dividing by `b^i` drops the
`i` least significant digits.
-/

namespace Work.PTCert.digits

/-- The `Nat.ofDigits` encoding of `(List.range n).map d` is the positional sum
`∑_{j<n} d j * b^j`. -/
private theorem ofDigits_range_map (b : ℕ) (d : ℕ → ℕ) (n : ℕ) :
    Nat.ofDigits b ((List.range n).map d) = ∑ j ∈ Finset.range n, d j * b ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, Nat.ofDigits_append,
      Nat.ofDigits_singleton, List.length_map, List.length_range, ih, Finset.sum_range_succ]
    ring

/-- The `i`-th base-`b` digit of `Nat.ofDigits b l`, for digits `< b` and `b ≥ 2`. -/
private theorem ofDigits_div_pow_mod_eq_getElem {b : ℕ} (hb : 2 ≤ b) (l : List ℕ)
    (hl : ∀ x ∈ l, x < b) {i : ℕ} (hi : i < l.length) :
    Nat.ofDigits b l / b ^ i % b = l[i] := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i (by omega) l hl, List.drop_eq_getElem_cons hi,
    Nat.ofDigits_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hl _ (List.getElem_mem hi))]

theorem sum_mul_pow_div_mod {b : ℕ} (hb : 2 ≤ b) (d : ℕ → ℕ) (n i : ℕ) (hd : ∀ j < n, d j < b) (hi : i < n) :
    (∑ j ∈ Finset.range n, d j * b ^ j) / b ^ i % b = d i := by
  rw [← ofDigits_range_map b d n]
  have hlen : ((List.range n).map d).length = n := by simp
  have hlt : ∀ x ∈ (List.range n).map d, x < b := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
    exact hd j (List.mem_range.mp hj)
  rw [ofDigits_div_pow_mod_eq_getElem hb _ hlt (by omega)]
  simp

end Work.PTCert.digits
