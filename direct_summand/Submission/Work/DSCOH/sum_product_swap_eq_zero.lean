import Mathlib

namespace Work.DSCOH

/-- Sum over the full product `s ×ˢ s` of an antisymmetric function `f`
(namely `f p.swap = - f p`) that vanishes on the diagonal is zero.

The argument pairs each off-diagonal point `p` with `p.swap`: the two terms
cancel, and the diagonal terms vanish. Concretely we apply
`Finset.sum_involution` with the fixed-point-free involution `p ↦ p.swap`
on `s ×ˢ s`. -/
theorem sum_product_swap_eq_zero {α : Type*} [DecidableEq α] {X : Type*} [AddCommGroup X]
    (s : Finset α) (f : α × α → X)
    (h : ∀ p ∈ s ×ˢ s, f p.swap = - f p)
    (hdiag : ∀ i ∈ s, f (i, i) = 0) :
    ∑ p ∈ s ×ˢ s, f p = 0 := by
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · -- the two members of a pair cancel
    intro p hp
    rw [h p hp, add_neg_cancel]
  · -- a point whose value is nonzero is not fixed by the involution
    intro p hp hne hfix
    have h12 : p.2 = p.1 := by
      have := congrArg Prod.fst hfix
      simpa using this
    have hp1 : p.1 ∈ s := (Finset.mem_product.mp hp).1
    have hpeq : p = (p.1, p.1) := Prod.ext rfl h12
    have hfz : f p = 0 := by rw [hpeq, hdiag p.1 hp1]
    exact hne hfz
  · -- the involution preserves `s ×ˢ s`
    intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · -- the involution is an involution
    intro p hp
    simp

end Work.DSCOH
