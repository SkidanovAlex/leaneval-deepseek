import Mathlib

/-!
# Auxiliary complement lemma (area BG)

If `N` is normal in `G`, `N ⊓ A = ⊥` and `N ⊔ A = ⊤`, then `N` and `A` are complements of one
another (in the sense of `Subgroup.IsComplement'`), i.e. the product map `N × A → G` is a
bijection.  This is the converse of `Subgroup.IsComplement'.sup_eq_top` +
`Subgroup.IsComplement'.disjoint`, valid when `N` is normal: then the set product `↑N * ↑A` is
the whole of `↑(N ⊔ A)` (`Subgroup.normal_mul`), hence the whole group.

This is used in area `BG` to recognise the kernel/complement pair of a Frobenius group as a
`Subgroup.IsComplement'` pair without any finiteness hypothesis.
-/

namespace Work.BG

/-- If `N` is normal in `G` and `N ⊓ A = ⊥`, `N ⊔ A = ⊤`, then `N` and `A` are complements. -/
theorem isComplement'_of_disjoint_sup_eq_top_of_normal {G : Type*} [Group G] {N A : Subgroup G}
    [N.Normal] (hdisj : Disjoint N A) (hsup : N ⊔ A = ⊤) : N.IsComplement' A := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
  rw [← Subgroup.normal_mul N A, hsup, Subgroup.coe_top]

end Work.BG
