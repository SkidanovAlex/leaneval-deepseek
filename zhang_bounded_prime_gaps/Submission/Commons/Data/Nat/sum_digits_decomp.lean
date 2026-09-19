import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Digits.Defs
import Submission.Commons.Data.Nat.multinomial_factor_rec

namespace Commons.Data.Nat

/-- `ofDigits` of the list of values `a 0, a 1, …, a (L-1)` (the little-endian list
`(List.range L).map a`) computes the finite sum `∑_{i<L} a i * p^i`. -/
private lemma ofDigits_map_range (a : ℕ → ℕ) (p L : ℕ) :
    Nat.ofDigits p ((List.range L).map a) = ∑ i ∈ Finset.range L, a i * p ^ i := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih, List.length_map,
      List.length_range]
    simp only [List.map_cons, List.map_nil, Nat.ofDigits_singleton]
    rw [Finset.sum_range_succ]
    ring

/-- Peeling off the lowest digit: `a / p ^ (j+1) = (a / p) / p ^ j`. -/
private lemma div_pow_succ_eq (a p j : ℕ) : a / p ^ (j + 1) = (a / p) / p ^ j := by
  rw [pow_succ', Nat.div_div_eq_div_mul]

/-- The `k`-th base-`p` digit of `ofDigits p L` is the `k`-th entry of `L` (or `0` past
the end), provided all entries of `L` are `< p` and `0 < p`. -/
private lemma ofDigits_div_pow_mod {p : ℕ} (hp : 0 < p) (L : List ℕ)
    (hL : ∀ x ∈ L, x < p) (k : ℕ) :
    Nat.ofDigits p L / p ^ k % p = L.getD k 0 := by
  induction k generalizing L with
  | zero =>
    cases L with
    | nil => simp
    | cons x t =>
      rw [Nat.pow_zero, Nat.div_one, Nat.ofDigits_cons, List.getD_cons_zero,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hL x (by simp))]
  | succ k ih =>
    cases L with
    | nil => simp
    | cons x t =>
      rw [div_pow_succ_eq, Nat.ofDigits_div_eq_ofDigits_tail hp (x :: t) hL, List.tail_cons,
        ih t (fun y hy => hL y (List.mem_cons_of_mem x hy)), List.getD_cons_succ]

/-- The `k`-th entry of the little-endian list `[a 0, a 1, …, a (L-1)]` is `a k` for
`k < L` and `0` otherwise. -/
private lemma getD_map_range (a : ℕ → ℕ) (L k : ℕ) :
    ((List.range L).map a).getD k 0 = if k < L then a k else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < L
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega)]; simp [h]

theorem sum_digits_decomp {p L : ℕ} (a : ℕ → ℕ) (ha : ∀ i < L, a i < p) (k : ℕ) :
    (∑ i ∈ Finset.range L, a i * p ^ i) / p ^ k % p = if k < L then a k else 0 := by
  rcases eq_or_ne p 0 with hp0 | hp
  · subst hp0
    rcases eq_or_ne L 0 with hL0 | hL0
    · subst hL0; simp
    · exact absurd (ha 0 (Nat.pos_of_ne_zero hL0)) (Nat.not_lt_zero _)
  · have hp' : 0 < p := Nat.pos_of_ne_zero hp
    have hLt : ∀ x ∈ (List.range L).map a, x < p := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact ha i (List.mem_range.mp hi)
    rw [← ofDigits_map_range a p L]
    rw [ofDigits_div_pow_mod hp' ((List.range L).map a) hLt k]
    exact getD_map_range a L k

end Commons.Data.Nat