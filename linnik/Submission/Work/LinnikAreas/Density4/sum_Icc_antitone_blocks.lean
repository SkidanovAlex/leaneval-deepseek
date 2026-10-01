import Mathlib

namespace Work.LinnikAreas.Density4

/-- Splitting an interval sum at a point `q`: for `p ≤ q + 1` and `q ≤ r` the interval
`Icc p r` is the disjoint union of `Icc p q` and `Icc (q + 1) r`, hence the sum splits. -/
lemma sum_Icc_split (p q r : ℕ) (hpq : p ≤ q + 1) (hqr : q ≤ r) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc p r, f m
      = ∑ m ∈ Finset.Icc p q, f m + ∑ m ∈ Finset.Icc (q + 1) r, f m := by
  have hunion : Finset.Icc p r = Finset.Icc p q ∪ Finset.Icc (q + 1) r := by
    apply Finset.ext
    intro m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc p q) (Finset.Icc (q + 1) r) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_Icc] at hm1 hm2
    omega
  rw [hunion, Finset.sum_union hdisj]

theorem sum_Icc_antitone_blocks (a : ℕ → ℕ) (ha : Antitone a) (f : ℕ → ℝ) (M : ℕ) (hM : a M = 0) :
    ∑ m ∈ Finset.Icc 1 (a 0), f m
      = ∑ j ∈ Finset.range M, ∑ m ∈ Finset.Icc (a (j + 1) + 1) (a j), f m := by
  -- General form, without the hypothesis `a M = 0`: the blocks `(a (j+1), a j]` for
  -- `j < N` tile the interval `(a N, a 0]`.
  have key : ∀ N : ℕ, ∑ j ∈ Finset.range N, ∑ m ∈ Finset.Icc (a (j + 1) + 1) (a j), f m
      = ∑ m ∈ Finset.Icc (a N + 1) (a 0), f m := by
    intro N
    induction N with
    | zero =>
      rw [Finset.sum_range_zero, Finset.Icc_eq_empty (by omega)]
      simp
    | succ N ih =>
      -- peel off the last block and combine it with the interval `(a N, a 0]`
      rw [Finset.sum_range_succ, ih]
      have hsplit := sum_Icc_split (a (N + 1) + 1) (a N) (a 0)
        (by have h1 : a (N + 1) ≤ a N := ha (Nat.le_succ N); omega)
        (by have h2 : a N ≤ a 0 := ha (Nat.zero_le N); omega) f
      rw [hsplit, add_comm]
  simpa [hM] using (key M).symm

end Work.LinnikAreas.Density4
