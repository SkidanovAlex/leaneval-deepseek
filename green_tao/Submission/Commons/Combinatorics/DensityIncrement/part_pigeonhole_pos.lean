import Mathlib

namespace Commons.Combinatorics.DensityIncrement

/-- Pigeonhole-type step for the density increment argument.

If `m ≥ 0` dominates `a` pointwise (`a i ≤ m i`), `∑ m = M`, `∑ a = Ac`, and
`(δ' + ε * card ι) * M ≤ Ac`, then some index `i` satisfies both `ε * M ≤ m i`
and `δ' * m i ≤ a i`. -/
theorem part_pigeonhole_pos {ι : Type*} [Fintype ι] [Nonempty ι] (m a : ι → ℝ) (M Ac δ' ε : ℝ)
    (hm : ∀ i, 0 ≤ m i) (ha : ∀ i, a i ≤ m i)
    (hsum : ∑ i, m i = M) (hsuma : ∑ i, a i = Ac)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ' : 0 ≤ δ')
    (h : (δ' + ε * (Fintype.card ι : ℝ)) * M ≤ Ac) :
    ∃ i, ε * M ≤ m i ∧ δ' * m i ≤ a i := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  set g : ι → ℝ := fun i => if ε * M ≤ m i then δ' * m i else ε * M with hg
  have hpoint : ∀ i, a i < g i := by
    intro i
    by_cases hp : ε * M ≤ m i
    · simp only [hg, hp, if_true]
      exact not_le.mp (hcon i hp)
    · simp only [hg, hp, if_false]
      have hm_lt : m i < ε * M := lt_of_not_ge hp
      linarith [ha i]
  have hstrict : ∑ i, a i < ∑ i, g i :=
    Finset.sum_lt_sum (fun i _ => le_of_lt (hpoint i))
      ⟨Classical.arbitrary ι, Finset.mem_univ _, hpoint _⟩
  have hbound : ∑ i, g i ≤ (δ' + ε * (Fintype.card ι : ℝ)) * M := by
    have hgm : ∀ i, g i ≤ δ' * m i + ε * M := by
      intro i
      by_cases hp : ε * M ≤ m i
      · simp only [hg, hp, if_true]
        have : (0:ℝ) ≤ ε * M := mul_nonneg hε hM
        linarith
      · simp only [hg, hp, if_false]
        have : (0:ℝ) ≤ δ' * m i := mul_nonneg hδ' (hm i)
        linarith
    calc ∑ i, g i ≤ ∑ i, (δ' * m i + ε * M) := Finset.sum_le_sum (fun i _ => hgm i)
      _ = δ' * M + (Fintype.card ι : ℝ) * (ε * M) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
                Finset.card_univ, nsmul_eq_mul]
      _ = (δ' + ε * (Fintype.card ι : ℝ)) * M := by ring
  rw [hsuma] at hstrict
  linarith [h, hbound, hstrict]

end Commons.Combinatorics.DensityIncrement
