import Mathlib

set_option linter.unusedVariables false

namespace Work.FITop

/-- The inner sum over `n` (with `m * n ≤ x`) of `g (m * n)` reindexed as a sum over the
multiples `l` of `m` in `[1, x]`.  For `1 ≤ m` the map `n ↦ m * n` is a bijection from
`{n ∈ Icc 1 x : m * n ≤ x}` onto `{l ∈ Icc 1 x : m ∣ l}` with inverse `l ↦ l / m`. -/
lemma TauMulReindex_inner (g : ℕ → ℝ) (x m : ℕ) (hm : m ∈ Finset.Icc 1 x) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x), g (m * n))
      = ∑ l ∈ Finset.Icc 1 x, (if m ∣ l then g l else 0) := by
  obtain ⟨hm1, hmx⟩ := Finset.mem_Icc.mp hm
  have hbij :
      (∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x), g (m * n))
        = ∑ l ∈ (Finset.Icc 1 x).filter (fun l => m ∣ l), g l := by
    refine Finset.sum_bij (fun n _ => m * n) ?_ ?_ ?_ ?_
    · -- the image lands in the multiples of `m` inside `[1, x]`
      intro n hn
      obtain ⟨hnA, hmnx⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, _hnx⟩ := Finset.mem_Icc.mp hnA
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by simpa using Nat.mul_le_mul hm1 hn1, hmnx⟩, ⟨n, rfl⟩⟩
    · -- injectivity of `n ↦ m * n`
      intro n₁ _ n₂ _ heq
      exact Nat.mul_left_cancel (by omega) heq
    · -- surjectivity onto the multiples of `m`
      intro l hl
      obtain ⟨hlA, hml⟩ := Finset.mem_filter.mp hl
      obtain ⟨hl1, hlx⟩ := Finset.mem_Icc.mp hlA
      refine ⟨l / m, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [Nat.one_le_div_iff (by omega)]
          exact Nat.le_of_dvd (by omega) hml
        · exact le_trans (Nat.div_le_self l m) hlx
        · rw [Nat.mul_div_cancel' hml]; exact hlx
      · exact Nat.mul_div_cancel' hml
    · intro n _
      rfl
  rw [hbij, Finset.sum_filter]

/-- `τ l · g l` rewritten as the sum of `g l` over the divisors `m` of `l` lying in `[1, x]`
(automatic for `1 ≤ l ≤ x`). -/
lemma TauMulReindex_rhs (g : ℕ → ℝ) (x l : ℕ) (hl : l ∈ Finset.Icc 1 x) :
    ((l.divisors.card : ℝ)) * g l
      = ∑ m ∈ Finset.Icc 1 x, (if m ∣ l then g l else 0) := by
  obtain ⟨hl1, hlx⟩ := Finset.mem_Icc.mp hl
  have hl0 : l ≠ 0 := by omega
  have hcard : (Finset.Icc 1 x).filter (fun m => m ∣ l) = l.divisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_h1, _h2⟩, h3⟩
      exact ⟨h3, hl0⟩
    · rintro ⟨h3, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h3 (by omega),
        le_trans (Nat.le_of_dvd (by omega) h3) hlx⟩, h3⟩
  rw [← hcard, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **Reindexing the double sum `∑_{m ≤ x} ∑_{n ≤ x, mn ≤ x} g (mn)` by divisors.**
Both sides are *equal*: the LHS counts each `l ∈ [1, x]` with multiplicity
`#{(m, n) : mn = l} = τ l`, exactly as the RHS does. -/
theorem TauMulReindex {g : ℕ → ℝ} (hg : ∀ l, 0 ≤ g l) (x : ℕ) :
    (∑ m ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x), g (m * n))
      ≤ ∑ l ∈ Finset.Icc 1 x, ((l.divisors.card : ℝ)) * g l := by
  have h1 :
      (∑ m ∈ Finset.Icc 1 x,
          ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m * n ≤ x), g (m * n))
        = ∑ m ∈ Finset.Icc 1 x, ∑ l ∈ Finset.Icc 1 x, (if m ∣ l then g l else 0) :=
    Finset.sum_congr rfl (fun m hm => TauMulReindex_inner g x m hm)
  have h2 :
      (∑ l ∈ Finset.Icc 1 x, ((l.divisors.card : ℝ)) * g l)
        = ∑ l ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 x, (if m ∣ l then g l else 0) :=
    Finset.sum_congr rfl (fun l hl => TauMulReindex_rhs g x l hl)
  rw [h1, h2]
  exact le_of_eq (Finset.sum_comm (f := fun m l => if m ∣ l then g l else 0))

end Work.FITop
