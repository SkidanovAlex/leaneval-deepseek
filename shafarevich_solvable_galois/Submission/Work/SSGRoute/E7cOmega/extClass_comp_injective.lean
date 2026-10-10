import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# C6 infrastructure: injectivity of the connecting map `δ = (·.comp hS.extClass)`

For a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` whose middle term has
`H¹(G, X₂) = Ext¹_G(ℤ, X₂) = 0`, the "cup with the class of `S`" map

  `Ext¹_G(ℤ, X₃) → Ext²_G(ℤ, X₁),   x ↦ x.comp hS.extClass`

is injective.  This is the `δ`-injectivity used by every version of the detecting-class argument
(`⟨φ, c⟩ = δ(μ ∘ c) ≠ 0 ⟸ μ ∘ c ≠ 0`), specialized to the `ℚ/ℤ`-coefficient sequence
`0 → ℤ → ℚ → ℚ/ℤ → 0` of `ratDivDefs.lean`: there `X₂ = ℚ` and `H¹(G,ℚ) = 0` because `ℚ` is
torsion-free and divisible.
-/

namespace Work.SSGRoute.E7cOmega

open CategoryTheory SSGRoute.PTExt

/-- **Injectivity of `x ↦ x.comp hS.extClass`** when the middle term is `H¹`-acyclic. -/
theorem extClass_comp_injective (G : Type) [Group G]
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact)
    (h : Subsingleton (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep G) S.X₂ 1))
    (x y : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep G) S.X₃ 1)
    (hxy : x.comp hS.extClass (by norm_num : 1 + 1 = 2) =
           y.comp hS.extClass (by norm_num : 1 + 1 = 2)) : x = y := by
  -- the difference has vanishing `δ`
  have hz : (x - y).comp hS.extClass (by norm_num : 1 + 1 = 2) = 0 := by
    rw [sub_eq_add_neg, CategoryTheory.Abelian.Ext.add_comp,
      CategoryTheory.Abelian.Ext.neg_comp, hxy, add_neg_cancel]
  -- exactness of the covariant sequence at `Ext¹_G(ℤ, X₃)`
  obtain ⟨x₂, hx₂⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₃
    (SSGRoute.PTExt.unitRep G) hS (x - y) (n₁ := 2) (by norm_num) hz
  -- the source `Ext¹_G(ℤ, X₂)` is trivial by hypothesis
  have hx2zero : x₂ = 0 := @Subsingleton.elim _ h x₂ 0
  rw [hx2zero, CategoryTheory.Abelian.Ext.zero_comp] at hx₂
  exact sub_eq_zero.mp hx₂.symm

end Work.SSGRoute.E7cOmega
