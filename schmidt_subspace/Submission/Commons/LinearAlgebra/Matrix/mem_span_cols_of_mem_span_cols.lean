import Mathlib

namespace Commons.LinearAlgebra.Matrix

open scoped BigOperators

/-- Auxiliary "straightening" lemma.

Let `xs j` (`j : Fin N`) be integer vectors and `ξ` an integer matrix that vanishes for
`j ≤ i` (i.e. `ξ p j = 0` unless `p < j`).  Define the straightened vectors
`v j i = xs j i + ∑ p, xs p i * ξ p j`.  Then, for every `m`, the `ℚ`-span of the `xs j`
with `j.val < m` is contained in the `ℚ`-span of the `v j` with `j.val < m`.

Proof: by the vanishing condition `v j = xs j + ∑_{p < j} ξ p j • xs p`, hence
`xs j = v j - ∑_{p<j} ξ p j • xs p`.  Strong induction on `j.val` gives
`xs j ∈ span {v q : q.val < j.val+1}`; since only the `v q` with `q.val ≤ j.val < m`
are needed, the conclusion follows. -/
theorem span_le_span_straightened {N m : ℕ} (xs : Fin N → Fin N → ℤ) (ξ : Fin N → Fin N → ℤ)
    (hξ : ∀ i j, j ≤ i → ξ i j = 0) :
    Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < m} => fun i => ((xs j.1 i : ℤ) : ℚ)))
      ≤ Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < m} =>
          fun i => ((xs j.1 i : ℤ) : ℚ) + ∑ p, ((xs p i : ℤ) : ℚ) * ((ξ p j.1 : ℤ) : ℚ))) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  set S : Submodule ℚ (Fin N → ℚ) := Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < m} =>
          fun i => ((xs j.1 i : ℤ) : ℚ) + ∑ p, ((xs p i : ℤ) : ℚ) * ((ξ p j.1 : ℤ) : ℚ))) with hS
  have key : ∀ n, n < m → ∀ (j : Fin N), j.val = n →
      (fun i => ((xs j i : ℤ) : ℚ)) ∈ S := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn j hjn
    have hjlt : j.val < m := hjn ▸ hn
    -- The sum in `v j` restricted to the indices `p < j` (all other terms vanish).
    have hsum : ∀ i : Fin N, (∑ p : Fin N, ((xs p i : ℤ) : ℚ) * ((ξ p j : ℤ) : ℚ))
        = ∑ p ∈ (Finset.univ.filter (fun p : Fin N => p.val < j.val)),
            ((ξ p j : ℤ) : ℚ) * ((xs p i : ℤ) : ℚ) := by
      intro i
      have hz : ∀ p ∈ (Finset.univ : Finset (Fin N)),
          p ∉ Finset.univ.filter (fun p : Fin N => p.val < j.val) →
          ((xs p i : ℤ) : ℚ) * ((ξ p j : ℤ) : ℚ) = 0 := by
        intro p _ hp
        have hpv : ¬ p.val < j.val := by
          intro hcon
          exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hcon⟩)
        have hjp : j ≤ p := Fin.le_def.mpr (le_of_not_gt hpv)
        rw [hξ p j hjp, Int.cast_zero, mul_zero]
      have h1 := Finset.sum_subset
        (Finset.filter_subset (fun p : Fin N => p.val < j.val) Finset.univ) hz
      rw [← h1]
      exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    have hW : (fun i => ((xs j i : ℤ) : ℚ) + ∑ p, ((xs p i : ℤ) : ℚ) * ((ξ p j : ℤ) : ℚ)) ∈ S := by
      rw [hS]
      apply Submodule.subset_span
      exact ⟨⟨j, hjlt⟩, rfl⟩
    have hT : (∑ p ∈ (Finset.univ.filter (fun p : Fin N => p.val < j.val)),
        ((ξ p j : ℤ) : ℚ) • (fun i => ((xs p i : ℤ) : ℚ))) ∈ S := by
      apply Submodule.sum_mem
      intro p hp
      apply Submodule.smul_mem
      have hpv : p.val < j.val := (Finset.mem_filter.mp hp).2
      have hpn : p.val < n := by rw [← hjn]; exact hpv
      exact ih p.val hpn (lt_of_lt_of_le hpn (le_of_lt hn)) p rfl
    have hXeq : (fun i => ((xs j i : ℤ) : ℚ)) =
        (fun i => ((xs j i : ℤ) : ℚ) + ∑ p, ((xs p i : ℤ) : ℚ) * ((ξ p j : ℤ) : ℚ))
          - (∑ p ∈ (Finset.univ.filter (fun p : Fin N => p.val < j.val)),
              ((ξ p j : ℤ) : ℚ) • (fun i => ((xs p i : ℤ) : ℚ))) := by
      funext i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum i]
      ring
    rw [hXeq]
    exact Submodule.sub_mem _ hW hT
  exact key j.1.val j.2 j.1 rfl

-- Let `xs j` (`j : Fin N`) be integer vectors, `ξ` an integer matrix vanishing for `j ≤ i`
-- (i.e. strictly upper triangular indexing), and consider the "straightened" vectors
-- `v j i = xs j i + ∑ p, xs p i * ξ p j`.  Then the `ℚ`-span of the first `R` of the `xs`
-- is contained in the `ℚ`-span of the first `k` of the `v`, whenever `R ≤ k ≤ N`.
-- (Reason: `v j = xs j + ∑_{p < j} ξ p j • xs p`, so `xs j = v j - ∑_{p<j} ξ p j • xs p`
-- and one argues by strong induction on `j`, `xs j ∈ span {v q : q ≤ j}`.)
theorem mem_span_cols_of_mem_span_cols {N k R : ℕ} (hkN : k ≤ N) (hRk : R ≤ k)
    (xs : Fin N → Fin N → ℤ) (ξ : Fin N → Fin N → ℤ) (hξ : ∀ i j, j ≤ i → ξ i j = 0)
    (x : Fin N → ℤ)
    (hx : (fun i => ((x i : ℤ) : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun j : {j : Fin N // j.val < R} => fun i => ((xs j.1 i : ℤ) : ℚ)))) :
    (fun i => ((x i : ℤ) : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun j : {j : Fin N // j.val < k} =>
        fun i => ((xs j.1 i : ℤ) : ℚ) + ∑ p : Fin N, ((xs p i : ℤ) : ℚ) * ((ξ p j.1 : ℤ) : ℚ))) := by
  have hRleN : R ≤ N := le_trans hRk hkN
  have h1 := span_le_span_straightened (N := N) (m := R) xs ξ hξ
  have h2 : Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < R} =>
        fun i => ((xs j.1 i : ℤ) : ℚ) + ∑ p : Fin N, ((xs p i : ℤ) : ℚ) * ((ξ p j.1 : ℤ) : ℚ)))
      ≤ Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < k} =>
        fun i => ((xs j.1 i : ℤ) : ℚ) + ∑ p : Fin N, ((xs p i : ℤ) : ℚ) * ((ξ p j.1 : ℤ) : ℚ))) := by
    apply Submodule.span_mono
    rintro g ⟨jj, rfl⟩
    exact ⟨⟨jj.1, lt_of_lt_of_le jj.2 hRk⟩, rfl⟩
  exact h2 (h1 hx)

end Commons.LinearAlgebra.Matrix
