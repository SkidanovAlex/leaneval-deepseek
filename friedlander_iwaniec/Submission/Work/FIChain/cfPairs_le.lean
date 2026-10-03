import Mathlib

namespace Work.FIChain

/-- The fibre-grouping step: the double sum over pairs `(ℓ,d) ∈ Icc 1 x × Icc 1 M` with
`ℓ·d ≤ N` is at most the single sum over `ζ ∈ Icc 1 N` weighted by `Σ_{ℓ ∣ ζ} c ℓ`.  In fact,
when `N ≤ M` and `N ≤ x` the two sides are equal: for `ζ ≤ N` the fibre `{(ℓ,d) : ℓ·d = ζ,
ℓ ∈ Icc 1 x, d ∈ Icc 1 M}` is `{(ℓ, ζ/ℓ) : ℓ ∈ ζ.divisors}` (both constraints being automatic).
Formal route: `Finset.sum_filter` to turn the `if` into a filter, `Finset.sum_fiberwise_of_maps_to`
with `g p = p.1 * p.2` mapping into `Icc 1 N`, then bound each fibre sum by `Σ_{ℓ ∣ ζ} c ℓ` via
`Finset.sum_image` (the first projection is injective on the fibre) and
`Finset.sum_le_sum_of_subset_of_nonneg`. -/
lemma cfPairs_le (x M N : ℕ) (c hh : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hh0 : ∀ n, 0 ≤ hh n)
    (hNM : N ≤ M) (hNx : N ≤ x) :
    (∑ p ∈ (Finset.Icc 1 x) ×ˢ (Finset.Icc 1 M),
        if p.1 * p.2 ≤ N then c p.1 * hh (p.1 * p.2) else 0)
      ≤ ∑ ζ ∈ Finset.Icc 1 N, (∑ ℓ ∈ ζ.divisors, c ℓ) * hh ζ := by
  classical
  set A : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 M)).filter (fun p => p.1 * p.2 ≤ N) with hA
  have hstep1 : (∑ p ∈ (Finset.Icc 1 x) ×ˢ (Finset.Icc 1 M),
        if p.1 * p.2 ≤ N then c p.1 * hh (p.1 * p.2) else 0)
      = ∑ p ∈ A, c p.1 * hh (p.1 * p.2) := by
    rw [← Finset.sum_filter, hA]
  have hmaps : ∀ i ∈ A, i.1 * i.2 ∈ Finset.Icc 1 N := by
    intro i hi
    rw [hA, Finset.mem_filter, Finset.mem_product] at hi
    obtain ⟨⟨hi1, hi2⟩, hile⟩ := hi
    rw [Finset.mem_Icc] at hi1 hi2 ⊢
    exact ⟨one_le_mul_of_one_le_of_one_le hi1.1 hi2.1, hile⟩
  have hstep2 : ∑ p ∈ A, c p.1 * hh (p.1 * p.2)
      = ∑ ζ ∈ Finset.Icc 1 N, ∑ p ∈ A.filter (fun p => p.1 * p.2 = ζ),
          c p.1 * hh (p.1 * p.2) :=
    (Finset.sum_fiberwise_of_maps_to hmaps (fun p => c p.1 * hh (p.1 * p.2))).symm
  rw [hstep1, hstep2]
  apply Finset.sum_le_sum
  intro ζ hζ
  have hζne : ζ ≠ 0 := by
    rw [Finset.mem_Icc] at hζ
    omega
  have hinner : ∑ p ∈ A.filter (fun p => p.1 * p.2 = ζ), c p.1 * hh (p.1 * p.2)
      = (∑ p ∈ A.filter (fun p => p.1 * p.2 = ζ), c p.1) * hh ζ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [hinner]
  apply mul_le_mul_of_nonneg_right _ (hh0 ζ)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1) ↑(A.filter (fun p => p.1 * p.2 = ζ)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    simp only at hpq
    have hpz : p.1 * p.2 = ζ := hp.2
    have hqz : q.1 * q.2 = ζ := hq.2
    have hp1 : p.1 ≠ 0 := by
      have hmem : p ∈ A := hp.1
      rw [hA, Finset.mem_filter, Finset.mem_product] at hmem
      rw [Finset.mem_Icc] at hmem
      omega
    refine Prod.ext hpq ?_
    apply Nat.mul_left_cancel (Nat.pos_of_ne_zero hp1)
    rw [hpz, ← hqz, hpq]
  have himg : ∑ p ∈ A.filter (fun p => p.1 * p.2 = ζ), c p.1
      = ∑ ℓ ∈ (A.filter (fun p => p.1 * p.2 = ζ)).image (fun p : ℕ × ℕ => p.1), c ℓ :=
    (Finset.sum_image hinj).symm
  rw [himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ℓ hℓ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hℓ
    rw [Finset.mem_filter] at hp
    rw [Nat.mem_divisors]
    exact ⟨⟨p.2, hp.2.symm⟩, hζne⟩
  · intro ℓ _ _
    exact hc ℓ

end Work.FIChain
