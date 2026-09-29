import Mathlib

namespace Work.C17g

open scoped BigOperators

/-- Auxiliary finite identity: the `k`-indexed form of the binomial theorem obtained by
expanding `(r + t) ^ n` and reindexing the sum via `l = n - k`. -/
private lemma sum_antidiag_binom (a : ℕ → ℝ) (r t : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      ((k + (n - k)).choose (n - k) : ℝ) * a (k + (n - k)) * r ^ (n - k) * t ^ k)
    = a n * (r + t) ^ n := by
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))])]
  rw [← add_comm t r, add_pow t r n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.choose_symm hk']
  ring

/-- **Tonelli/binomial rearrangement.** Given nonnegative coefficients `a` and `r, t ≥ 0`,
if for every `k` the series `∑_l C(k+l,l) a(k+l) r^l` converges and the resulting series
in `k`, weighted by `t^k`, converges, then `∑_n a_n (r+t)^n` converges. -/
theorem binomial_tonelli (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hinner : ∀ k, Summable fun l => ((k + l).choose l : ℝ) * a (k + l) * r ^ l)
    (h : Summable fun k => (∑' l, ((k + l).choose l : ℝ) * a (k + l) * r ^ l) * t ^ k) :
    Summable fun n => a n * (r + t) ^ n := by
  -- The individual summands of the double sum are nonnegative.
  have hc : ∀ p : ℕ × ℕ,
      0 ≤ ((p.1 + p.2).choose p.2 : ℝ) * a (p.1 + p.2) * r ^ p.2 * t ^ p.1 := by
    intro p
    have h1 : (0 : ℝ) ≤ ((p.1 + p.2).choose p.2 : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 (ha _)) (pow_nonneg hr _)) (pow_nonneg ht _)
  -- Each `l`-fibre is summable (multiply `hinner` by the constant `t^k`).
  have hS1 : ∀ k, Summable fun l : ℕ =>
      ((k + l).choose l : ℝ) * a (k + l) * r ^ l * t ^ k := by
    intro k
    simpa using (hinner k).mul_right (t ^ k)
  -- The series of `l`-fibre sums is summable (pull the constant `t^k` out of each `tsum`).
  have hS2 : Summable fun k : ℕ =>
      ∑' l : ℕ, ((k + l).choose l : ℝ) * a (k + l) * r ^ l * t ^ k := by
    refine h.congr (fun k => ?_)
    rw [tsum_mul_right]
  -- Tonelli for nonnegative series: the double series converges.
  have hprod : Summable fun p : ℕ × ℕ =>
      ((p.1 + p.2).choose p.2 : ℝ) * a (p.1 + p.2) * r ^ p.2 * t ^ p.1 :=
    (summable_prod_of_nonneg hc).mpr ⟨hS1, hS2⟩
  -- The sets `{(k,l) | k + l = n}` partition `ℕ × ℕ`.
  have hs : ∀ i : ℕ × ℕ,
      ∃! j, i ∈ (fun n : ℕ => (Finset.HasAntidiagonal.antidiagonal n : Set (ℕ × ℕ))) j := by
    intro i
    refine ⟨i.1 + i.2, ?_, ?_⟩
    · simp [Finset.HasAntidiagonal.mem_antidiagonal]
    · intro m hm
      have : i.1 + i.2 = m := by simpa [Finset.HasAntidiagonal.mem_antidiagonal] using hm
      exact this.symm
  -- Regroup the convergent double series along the partition; this is the desired series.
  have hfib := (summable_partition (f := fun p : ℕ × ℕ =>
      ((p.1 + p.2).choose p.2 : ℝ) * a (p.1 + p.2) * r ^ p.2 * t ^ p.1) hc hs).mp hprod
  obtain ⟨_, hfibsum⟩ := hfib
  refine hfibsum.congr (fun n => ?_)
  -- Identify the `n`-th fibre sum with `a n * (r + t) ^ n`.
  change (∑' (i : ↥(Finset.HasAntidiagonal.antidiagonal n)),
      ((i : ℕ × ℕ).1 + (i : ℕ × ℕ).2).choose ((i : ℕ × ℕ).2) * a ((i : ℕ × ℕ).1 + (i : ℕ × ℕ).2)
        * r ^ ((i : ℕ × ℕ).2) * t ^ ((i : ℕ × ℕ).1))
      = a n * (r + t) ^ n
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n)
      (fun y : ℕ × ℕ => ((y.1 + y.2).choose y.2 : ℝ) * a (y.1 + y.2) * r ^ y.2 * t ^ y.1)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_antidiag_binom a r t n

end Work.C17g
