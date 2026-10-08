import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- In a commutative ring of characteristic `2`, the double sum of a symmetric
two-variable function over a finset equals the sum of its diagonal values.

This is the key combinatorial identity used in the Bender–Suzuki argument: an
off-diagonal term `g k l` and its mirror `g l k` are equal, and in
characteristic `2` their sum vanishes, so the off-diagonal contributions cancel
pairwise and only the diagonal survives. -/
theorem double_sum_diag {R : Type*} [CommRing R] [CharP R 2]
    {α : Type*} (s : Finset α) (g : α → α → R)
    (hsym : ∀ k ∈ s, ∀ l ∈ s, g k l = g l k) :
    ∑ k ∈ s, ∑ l ∈ s, g k l = ∑ k ∈ s, g k k := by
  classical
  -- View the double sum as a single sum over the product `s ×ˢ s`.
  rw [← Finset.sum_product s s (fun p : α × α => g p.1 p.2)]
  -- The off-diagonal part vanishes: swapping the coordinates is a fixed-point-free
  -- involution pairing terms that add up to zero.
  have hoff : ∑ x ∈ (s ×ˢ s).filter (fun p => p.1 ≠ p.2), g x.1 x.2 = 0 := by
    exact Finset.sum_involution (fun p _ => (p.2, p.1))
      (fun p hp => by
        have hmem := (Finset.mem_filter.mp hp).1
        have h1 : p.1 ∈ s := (Finset.mem_product.mp hmem).1
        have h2 : p.2 ∈ s := (Finset.mem_product.mp hmem).2
        rw [hsym p.1 h1 p.2 h2]
        exact CharTwo.add_self_eq_zero _)
      (fun p hp _ => by
        have hne' := (Finset.mem_filter.mp hp).2
        intro hcontra
        exact hne' (congrArg Prod.snd hcontra))
      (fun p hp => by
        have hmem := (Finset.mem_filter.mp hp).1
        have hne := (Finset.mem_filter.mp hp).2
        have h1 : p.1 ∈ s := (Finset.mem_product.mp hmem).1
        have h2 : p.2 ∈ s := (Finset.mem_product.mp hmem).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, ?_⟩
        exact fun h => hne h.symm)
      (fun _ _ => Prod.mk.eta)
  -- The diagonal part is exactly the sum of the diagonal values.
  have hdiag : ∑ x ∈ (s ×ˢ s).filter (fun p => p.1 = p.2), g x.1 x.2 = ∑ k ∈ s, g k k := by
    rw [Finset.sum_filter]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_ite_eq]
    rw [ite_eq_left hk]
  -- Combine the two parts.
  rw [← Finset.sum_filter_add_sum_filter_not (s ×ˢ s) (fun p => p.1 = p.2)
        (fun x => g x.1 x.2)]
  rw [hdiag, hoff, add_zero]

end Work.Higman
