/-
# The discrete Abel-summation identity for `Tsum` / `Ssum`

For an arbitrary coefficient sequence `a : ℕ → ℝ`,

`Σ_{r ≤ N} a_r·log(N/r) = Σ_{m ≤ N-1} (Σ_{r ≤ m} a_r)·log((m+1)/m)`,

the classical "summation by parts" (Abel) identity in its purely discrete form.  The proof
swaps the triangular double sum and telescopes `Σ_{m=r}^{N-1} log((m+1)/m) = log(N/r)`.

Specialising `a_r` to the summand `μ(r)/κ(r)·[r ⊥ t]` gives the requested identity
`Tsum N t = Σ_{m ≤ N-1} Ssum m t·log((m+1)/m)`.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- Telescoping of `log((m+1)/m)`: for `1 ≤ a ≤ b`,
`Σ_{a ≤ m ≤ b} log((m+1)/m) = log((b+1)/a)`. -/
lemma KMTsum_telescope (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Icc a b, Real.log (((m : ℝ) + 1) / (m : ℝ))
      = Real.log (((b : ℝ) + 1) / (a : ℝ)) := by
  have key : ∀ m ∈ Finset.Icc a b,
      Real.log (((m : ℝ) + 1) / (m : ℝ))
        = Real.log (((m + 1 : ℕ) : ℝ)) - Real.log ((m : ℝ)) := by
    intro m hm
    have hm1 : 1 ≤ m := ha.trans (Finset.mem_Icc.mp hm).1
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hm1' : ((m : ℝ) + 1) ≠ 0 := by positivity
    rw [Real.log_div hm1' hm0]
    norm_num
  rw [Finset.sum_congr rfl key, Finset.sum_Icc_sub hab (fun k => Real.log (k : ℝ))]
  have hb0 : ((b : ℝ) + 1) ≠ 0 := by positivity
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  rw [Real.log_div hb0 ha0]
  norm_num

/-- Triangular reindexing: `Σ_{m ≤ n} Σ_{r ≤ m} f r m = Σ_{r ≤ n} Σ_{r ≤ m ≤ n} f r m`. -/
lemma KMTsum_swap (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, ∑ r ∈ Finset.Icc 1 m, f r m)
      = ∑ r ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc r n, f r m := by
  have step : ∀ m ∈ Finset.Icc 1 n,
      (∑ r ∈ Finset.Icc 1 m, f r m)
        = ∑ r ∈ Finset.Icc 1 n, (if r ≤ m then f r m else 0) := by
    intro m hm
    have hmle : m ≤ n := (Finset.mem_Icc.mp hm).2
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro h; exact ⟨⟨h.1, h.2.trans hmle⟩, h.2⟩
      · intro h; exact ⟨h.1.1, h.2⟩
    · intro x hx; rfl
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨h.2, h.1.2⟩
    · intro h; exact ⟨⟨hr1.trans h.1, h.2⟩, h.1⟩
  · intro x hx; rfl

/-- The Abel identity in "successor" form: with `N = n+1` the endpoint term `r = n+1` contributes
`log 1 = 0`, so the sum reduces to the `N-1` range. -/
lemma KMTsum_abel_succ (a : ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 (n+1), a r * Real.log (((n : ℝ) + 1) / (r : ℝ)))
      = ∑ m ∈ Finset.Icc 1 n,
          (∑ r ∈ Finset.Icc 1 m, a r) * Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hz : a (n + 1) * Real.log (((n : ℝ) + 1) / ((n + 1 : ℕ) : ℝ)) = 0 := by
    have h1 : (((n : ℝ) + 1) / ((n + 1 : ℕ) : ℝ)) = 1 := by
      rw [Nat.cast_add, Nat.cast_one, div_self (by positivity)]
    rw [h1, Real.log_one, mul_zero]
  rw [hz, add_zero]
  simp_rw [Finset.sum_mul]
  rw [KMTsum_swap (fun r m => a r * Real.log (((m : ℝ) + 1) / (m : ℝ))) n]
  simp_rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [KMTsum_telescope r n (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]

/-- **Discrete Abel summation.**  For any `a : ℕ → ℝ` and any `N`,
`Σ_{r ≤ N} a_r·log(N/r) = Σ_{m ≤ N-1} (Σ_{r ≤ m} a_r)·log((m+1)/m)`. -/
lemma KMTsum_abel (a : ℕ → ℝ) (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 N, a r * Real.log ((N : ℝ) / (r : ℝ)))
      = ∑ m ∈ Finset.Icc 1 (N-1),
          (∑ r ∈ Finset.Icc 1 m, a r) * Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
  rcases N with _ | k
  · simp
  · simpa [Nat.add_sub_cancel] using KMTsum_abel_succ a k

theorem KMTsumAbel (N t : ℕ) :
    Tsum N t = ∑ m ∈ Finset.Icc 1 (N - 1), Ssum m t * Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
  rw [Tsum_eq_sum_if]
  have hR : (∑ m ∈ Finset.Icc 1 (N - 1), Ssum m t * Real.log (((m : ℝ) + 1) / (m : ℝ)))
      = ∑ m ∈ Finset.Icc 1 (N - 1),
          (∑ r ∈ Finset.Icc 1 m,
              (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kappa r else 0))
            * Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Ssum_eq_sum_if]
  rw [hR]
  exact KMTsum_abel
    (fun r => if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kappa r else 0) N

end

end Work.ZeroDensity.Jutila
