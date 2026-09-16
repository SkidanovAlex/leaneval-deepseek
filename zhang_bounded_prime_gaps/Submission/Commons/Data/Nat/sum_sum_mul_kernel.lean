import Mathlib.Algebra.Module.BigOperators

namespace Commons.Data.Nat

theorem sum_sum_mul_kernel {M : Type*} [AddCommMonoid M] {n m : ℕ} (x y : ℕ → ℕ) (K : ℕ → M) :
    (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, (x a * y b) • K (a + b))
      = ∑ k ∈ Finset.range (n + m),
          (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, if a + b = k then x a * y b else 0) • K k := by
  have hmaps : ∀ p ∈ Finset.range n ×ˢ Finset.range m, p.1 + p.2 ∈ Finset.range (n + m) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  have key : ∀ k : ℕ,
      (∑ p ∈ (Finset.range n ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
          (x p.1 * y p.2) • K (p.1 + p.2))
        = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m,
            if a + b = k then x a * y b else 0) • K k := by
    intro k
    calc (∑ p ∈ (Finset.range n ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
            (x p.1 * y p.2) • K (p.1 + p.2))
        = ∑ p ∈ (Finset.range n ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
            (x p.1 * y p.2) • K k := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [hp.2]
      _ = (∑ p ∈ (Finset.range n ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
            x p.1 * y p.2) • K k := Finset.sum_smul.symm
      _ = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m,
            if a + b = k then x a * y b else 0) • K k := by
          congr 1
          rw [Finset.sum_filter, Finset.sum_product]
  calc (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, (x a * y b) • K (a + b))
      = ∑ p ∈ Finset.range n ×ˢ Finset.range m, (x p.1 * y p.2) • K (p.1 + p.2) :=
        (Finset.sum_product (Finset.range n) (Finset.range m)
          (fun p : ℕ × ℕ => (x p.1 * y p.2) • K (p.1 + p.2))).symm
    _ = ∑ k ∈ Finset.range (n + m),
          ∑ p ∈ (Finset.range n ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
            (x p.1 * y p.2) • K (p.1 + p.2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps
          (fun p : ℕ × ℕ => (x p.1 * y p.2) • K (p.1 + p.2))).symm
    _ = ∑ k ∈ Finset.range (n + m),
          (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, if a + b = k then x a * y b else 0) • K k :=
        Finset.sum_congr rfl (fun k _ => key k)

end Commons.Data.Nat