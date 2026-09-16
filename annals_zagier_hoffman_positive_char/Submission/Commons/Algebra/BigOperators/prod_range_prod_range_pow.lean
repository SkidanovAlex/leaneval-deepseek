import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Commons.Algebra.BigOperators

/-- Swapping the order of a nested product over the "triangle" `{(i,s) | i + s < A}`:
`∏ i < A, ∏ s < A-i, g i s = ∏ s < A, ∏ i < A-s, g i s`. -/
theorem prod_range_prod_range_swap {M : Type*} [CommMonoid M] (g : ℕ → ℕ → M) (A : ℕ) :
    (∏ i ∈ Finset.range A, ∏ s ∈ Finset.range (A - i), g i s)
      = ∏ s ∈ Finset.range A, ∏ i ∈ Finset.range (A - s), g i s := by
  rw [Finset.prod_sigma', Finset.prod_sigma']
  refine Finset.prod_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, s⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    exact ⟨by omega, by omega⟩
  · rintro ⟨i, s⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    exact ⟨by omega, by omega⟩
  · rintro ⟨i, s⟩ hx
    rfl
  · rintro ⟨i, s⟩ hx
    rfl
  · rintro ⟨i, s⟩ hx
    rfl

theorem prod_range_prod_range_pow {M : Type*} [CommMonoid M] (f : ℕ → M) (e : ℕ → ℕ)
    (A : ℕ) :
    (∏ i ∈ Finset.range A, (∏ s ∈ Finset.range (A - i), f s) ^ (e i))
      = ∏ s ∈ Finset.range A, (f s) ^ (∑ i ∈ Finset.range (A - s), e i) := by
  have h1 : (∏ i ∈ Finset.range A, (∏ s ∈ Finset.range (A - i), f s) ^ (e i))
          = ∏ i ∈ Finset.range A, ∏ s ∈ Finset.range (A - i), (f s) ^ (e i) :=
    Finset.prod_congr rfl fun i _ => (Finset.prod_pow _ _ _).symm
  have h2 : (∏ s ∈ Finset.range A, (f s) ^ (∑ i ∈ Finset.range (A - s), e i))
          = ∏ s ∈ Finset.range A, ∏ i ∈ Finset.range (A - s), (f s) ^ (e i) :=
    Finset.prod_congr rfl fun s _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
  rw [h1, h2]
  exact prod_range_prod_range_swap (fun i s => (f s) ^ (e i)) A

end Commons.Algebra.BigOperators