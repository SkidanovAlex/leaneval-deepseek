import Mathlib

namespace Work.HP.MDEstimates

open scoped BigOperators

/-- Arithmetic bound behind the dyadic-window sum for `q44_layer_sum`.

For `N = ⌈logb 2 (8 Kmink (Δ+1))⌉₊`, the sum over all monotone triples
`k : Fin 3 → ℕ` with `k 0 + k 1 + k 2 ≤ N` of `2 ^ (25 k 0 + 23 k 1 + 23 k 2)`
is `O((N+1)^3 · 2 ^ (71 N / 3))`.

The point is the pointwise exponential bound: for a monotone triple with
`k 0 + k 1 + k 2 ≤ N` one has `25 k 0 + 23 k 1 + 23 k 2 ≤ 71 N / 3`
(because `25 k 0 + 23 k 1 + 23 k 2 = 23 (k 0 + k 1 + k 2) + 2 k 0 ≤ 23 N + 2 N / 3`,
using `3 k 0 ≤ k 0 + k 1 + k 2 ≤ N`), so each of the at most `(N+1)^3` terms is
`≤ 2 ^ (71 N / 3)`.  The constant `K = 1` therefore suffices, independently of
`Kmink` and `Δ`. -/
theorem q44_arith_sum (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊
          then (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) else 0))
      ≤ K * ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 3
          * (2 : ℝ) ^ (71 * (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) / 3) := by
  refine ⟨1, one_pos, ?_⟩
  intro Δ hΔ
  set N : ℕ := ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ with hN
  -- pointwise exponential bound for every (admissible or not) triple
  have key : ∀ k : Fin 3 → ℕ,
      (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) else 0)
      ≤ (2 : ℝ) ^ (71 * (N : ℝ) / 3) := by
    intro k
    by_cases h : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
    · rw [if_pos h]
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsumnat : k 0 + k 1 + k 2 ≤ N := by
        simpa [Fin.sum_univ_three] using h.2
      have hk01 : k 0 ≤ k 1 := h.1 (by decide)
      have hk02 : k 0 ≤ k 2 := h.1 (by decide)
      have hsumR : (k 0 : ℝ) + (k 1 : ℝ) + (k 2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsumnat
      have h3k0 : 3 * (k 0 : ℝ) ≤ (N : ℝ) := by
        have h' : 3 * k 0 ≤ N := by omega
        exact_mod_cast h'
      push_cast
      nlinarith [hsumR, h3k0]
    · rw [if_neg h]
      exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hcard : (Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1))).card = (N + 1) ^ 3 := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const]
  have h1 : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) else 0))
      ≤ ((Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1))).card : ℝ)
          * (2 : ℝ) ^ (71 * (N : ℝ) / 3) := by
    calc ∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
          (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) else 0)
        ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)), (2 : ℝ) ^ (71 * (N : ℝ) / 3) :=
            Finset.sum_le_sum (fun k _ => key k)
      _ = (Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1))).card • (2 : ℝ) ^ (71 * (N : ℝ) / 3) :=
            Finset.sum_const (b := (2 : ℝ) ^ (71 * (N : ℝ) / 3))
      _ = ((Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1))).card : ℝ) * (2 : ℝ) ^ (71 * (N : ℝ) / 3) :=
            nsmul_eq_mul _ _
  rw [hcard] at h1
  calc ∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) else 0)
      ≤ (((N + 1) ^ 3 : ℕ) : ℝ) * (2 : ℝ) ^ (71 * (N : ℝ) / 3) := h1
    _ = 1 * ((N : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (N : ℝ) / 3) := by push_cast; ring

end Work.HP.MDEstimates
