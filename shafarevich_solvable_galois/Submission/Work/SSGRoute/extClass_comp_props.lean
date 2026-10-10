import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute

/-- **The two exactness properties of the connecting map `· ∘ extClass`.**

Let `0 → X₁ → X₂ → X₃ → 0` be a short exact sequence of `G`-modules (over the coefficient
ring `Coeff = ULift ℤ`), and let `δⁿ : Hⁿ(G,X₃) → H^{n+1}(G,X₁)`, `y ↦ y ∘ extClass`, be
composition with the Yoneda class of `S` (the connecting map of the long exact sequence of
`Ext`).

* If `Hⁿ(G,X₂) = 0` then `δⁿ` is injective.
* If `H^{n+1}(G,X₂) = 0` then `δⁿ` is surjective.

Both are immediate from the exactness of the long exact sequence of `Ext`
(`Abelian.Ext.covariant_sequence_exact₃` / `covariant_sequence_exact₁`): the kernel of `δⁿ`
is the image of `Hⁿ(G,X₂) → Hⁿ(G,X₃)`, and the image of `δⁿ` is the kernel of
`H^{n+1}(G,X₁) → H^{n+1}(G,X₂)`. -/
theorem extClass_comp_props (G : Type) [Group G]
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (n : ℕ) :
    (Subsingleton (SSGRoute.PTExt.extH S.X₂ n) →
      ∀ (y : SSGRoute.PTExt.extH S.X₃ n),
        y.comp hS.extClass (rfl : n + 1 = n + 1) = 0 → y = 0) ∧
    (Subsingleton (SSGRoute.PTExt.extH S.X₂ (n + 1)) →
      ∀ (z : SSGRoute.PTExt.extH S.X₁ (n + 1)),
        ∃ (y : SSGRoute.PTExt.extH S.X₃ n), y.comp hS.extClass (rfl : n + 1 = n + 1) = z) := by
  constructor
  · -- injectivity: exactness at `Hⁿ(G,X₃)`
    intro hsub y hy
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (SSGRoute.PTExt.unitRep G) hS y
      (n₁ := n + 1) (rfl : n + 1 = n + 1) hy
    have h0 : x₂ = 0 := hsub.allEq x₂ 0
    rw [h0] at hx₂
    simp at hx₂
    exact hx₂.symm
  · -- surjectivity: exactness at `H^{n+1}(G,X₁)`
    intro hsub z
    have hz : z.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := hsub.allEq _ 0
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ (SSGRoute.PTExt.unitRep G) hS z hz
      (n₀ := n) (rfl : n + 1 = n + 1)
    exact ⟨y, hy⟩

end Work.SSGRoute
