import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- For a finset `S` of naturals and `k ∈ S`, the sum over `S` splits as the sum over
the elements greater than `k`, plus the sum over the elements smaller than `k`, plus
the single diagonal term `g k`. -/
lemma sum_filter_split_range {M : Type*} [AddCommMonoid M]
    (S : Finset ℕ) (k : ℕ) (hk : k ∈ S) (g : ℕ → M) :
    (∑ l ∈ S, g l)
      = (∑ l ∈ S.filter (fun l => k < l), g l)
        + (∑ l ∈ S.filter (fun l => l < k), g l) + g k := by
  have hdiag : (∑ l ∈ S, if l = k then g l else 0) = g k := by
    rw [Finset.sum_ite_eq', ite_eq_left hk]
  rw [Finset.sum_filter, Finset.sum_filter, ← hdiag, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rcases lt_trichotomy k l with h | h | h
  · rw [ite_eq_left h, ite_eq_right (by omega : ¬ l < k), ite_eq_right (by omega : ¬ l = k)]
    simp
  · subst h; simp
  · rw [ite_eq_right (by omega : ¬ k < l), ite_eq_left h, ite_eq_right (by omega : ¬ l = k)]
    simp

theorem sum_range_lt_split {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, f k l)
      = (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l), f k l)
        + (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => l < k), f k l)
        + (∑ k ∈ Finset.range n, f k k) := by
  have hinner : ∀ k ∈ Finset.range n,
      (∑ l ∈ Finset.range n, f k l)
        = (∑ l ∈ (Finset.range n).filter (fun l => k < l), f k l)
          + (∑ l ∈ (Finset.range n).filter (fun l => l < k), f k l) + f k k :=
    fun k hk => sum_filter_split_range (Finset.range n) k hk (fun l => f k l)
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

end Work.Higman
