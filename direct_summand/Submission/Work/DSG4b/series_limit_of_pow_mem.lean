import Mathlib

namespace Work.DSG4b

/-- Given an `I`-adically complete ring `A`, a family of "error terms" `a n j` that decay
fast enough (`a n j ∈ I ^ (n - d j)`, with `ℕ`-truncated subtraction, so the bound is vacuous
for `n < d j`), the partial sums `∑_{k < N} a k j` converge to a limit `b j` with the precise
error bound `I ^ (N - d j)`.

The proof shifts the index by `d j`, so that consecutive terms of the shifted sequence
`g n = ∑_{k < n + d j} a k j` differ by `a (n + d j) j ∈ I ^ n`, making it `I`-adically Cauchy;
completeness produces the limit `L`, and the case split `N ≥ d j` / `N < d j` converts the
bound `I ^ n` on `g n - L` into the required bound `I ^ (N - d j)`. -/
theorem series_limit_of_pow_mem {A : Type*} [CommRing A] {I : Ideal A}
    (hI : IsAdicComplete I A) {ι : Type*} (d : ι → ℕ) (a : ℕ → ι → A)
    (ha : ∀ n j, a n j ∈ I ^ (n - d j)) :
    ∃ b : ι → A, ∀ j N, (∑ k ∈ Finset.range N, a k j) - b j ∈ I ^ (N - d j) := by
  classical
  -- For each `j`, the shifted partial sums form an `I`-adically Cauchy sequence with limit `L`.
  have hprec : ∀ j : ι, ∃ L : A, ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + d j), a k j) - L ∈ I ^ n := by
    intro j
    -- The shifted partial sums are Cauchy with the required rate.
    have hc : ∀ {m n : ℕ}, m ≤ n →
        (∑ k ∈ Finset.range (m + d j), a k j) ≡
          (∑ k ∈ Finset.range (n + d j), a k j) [SMOD (I ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
      -- The difference is (minus) the sum over the intermediate range, whose terms lie in `I ^ m`.
      have hIco : ∑ k ∈ Finset.Ico (m + d j) (n + d j), a k j =
          (∑ k ∈ Finset.range (n + d j), a k j) -
            (∑ k ∈ Finset.range (m + d j), a k j) :=
        Finset.sum_Ico_eq_sub (fun k => a k j) (by omega)
      rw [show (∑ k ∈ Finset.range (m + d j), a k j) -
            (∑ k ∈ Finset.range (n + d j), a k j) =
            -(∑ k ∈ Finset.Ico (m + d j) (n + d j), a k j) from by
          rw [hIco]; abel]
      apply neg_mem
      apply Submodule.sum_mem
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact Ideal.pow_le_pow_right
        ((Nat.le_sub_iff_add_le (le_trans (Nat.le_add_left (d j) m) hk.1)).2 hk.1) (ha k j)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (hI.toIsPrecomplete)
      (f := fun n => ∑ k ∈ Finset.range (n + d j), a k j) hc
    exact ⟨L, fun n => by
      have h := (SModEq.sub_mem).1 (hL n)
      rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h⟩
  choose b hb using hprec
  refine ⟨b, fun j N => ?_⟩
  by_cases h : d j ≤ N
  · -- For `N ≥ d j` write `N = (N - d j) + d j`.
    have hkey := hb j (N - d j)
    rwa [Nat.sub_add_cancel h] at hkey
  · -- For `N < d j` the bound `I ^ 0 = ⊤` is vacuous.
    rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h))]
    simp

end Work.DSG4b
