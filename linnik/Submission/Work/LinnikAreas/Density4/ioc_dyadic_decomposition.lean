import Mathlib

namespace Work.LinnikAreas.Density4

/-- For natural numbers, `(0, n] = [1, n]`. -/
lemma ioc_zero_eq_icc_one (n : ℕ) : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- Telescoping form of the dyadic decomposition: for a non-increasing sequence `c`,
the disjoint intervals `(c (m+1), c m]` for `m < M` partition `(c M, c 0]`. -/
lemma sum_ioc_chain (c : ℕ → ℕ) (hmono : ∀ m, c (m + 1) ≤ c m) (g : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Finset.range M, ∑ δ ∈ Finset.Ioc (c (m + 1)) (c m), g δ
      = ∑ δ ∈ Finset.Ioc (c M) (c 0), g δ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have hle : c M ≤ c 0 := (antitone_nat_of_succ_le hmono) (Nat.zero_le M)
    have h1 : c (M + 1) ≤ c M := hmono M
    have hunion := Finset.Ioc_union_Ioc_eq_Ioc (a := c (M + 1)) (b := c M) (c := c 0) h1 hle
    have hdisj : Disjoint (Finset.Ioc (c (M + 1)) (c M)) (Finset.Ioc (c M) (c 0)) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [← hunion, Finset.sum_union hdisj]
    ring

theorem ioc_dyadic_decomposition (c : ℕ → ℕ) (M : ℕ) (hcM : c M = 0)
    (hmono : ∀ m, c (m + 1) ≤ c m) (g : ℕ → ℝ) :
    ∑ δ ∈ Finset.Icc 1 (c 0), g δ =
      ∑ m ∈ Finset.range M, ∑ δ ∈ Finset.Ioc (c (m + 1)) (c m), g δ := by
  rw [sum_ioc_chain c hmono g M, hcM, ioc_zero_eq_icc_one]

end Work.LinnikAreas.Density4
