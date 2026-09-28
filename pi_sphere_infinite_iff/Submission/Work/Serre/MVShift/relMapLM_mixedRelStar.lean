import Mathlib
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.exists_relComplexMap

/-!
# Naturality of the mixed (absolute/relative) cup product along a map of pairs

The mixed Alexander–Whitney product `mixedRelStar R X A` cups an absolute cochain on `X` with a
cochain vanishing on `A`, producing a cochain vanishing on `A`.  This file shows that it is
natural with respect to the pullback along a map of pairs `f : (X₁, A₁) → (X₂, A₂)`:

`f*(a ⌣ b) = f*(a) ⌣ f*(b)`,

where `f*` on the relative cochains is `relMapLM` and `f*` on the absolute cochains is the
`m`-th component of the pullback `dualChainMap`.

The proof is a direct comparison of the underlying cochains: both sides are the pullback of the
Alexander–Whitney product `cup`, and the identity is exactly `cupNatural` (naturality of `cup`
for maps of simplicial sets, here `TopCat.toSSet.map f`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology

namespace Work.Serre.MVShift

/-- The `n`-th component of the pullback `dualChainMap` is the transpose of the `n`-th component
of the chain map `SSet.chainComplexMap` induced by `f` on the singular simplicial sets. -/
lemma dualChainMap_f_apply (R : Type) [CommRing R] {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (φ : Work.Cohomology.Cochain R (TopCat.toSSet.obj Y) n) :
    ((Work.Cohomology.dualChainMap R X Y f).f n).hom φ
      = ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f n).hom.dualMap φ :=
  rfl

theorem relMapLM_mixedRelStar {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (m n : ℕ)
    (a : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj X₂) m)
    (b : ↥(Work.Cohomology.relKern ℚ X₂ A₂ n)) :
    Work.Cohomology.relMapLM ℚ A₁ A₂ f h (m+n) ((Work.Cohomology.mixedRelStar ℚ X₂ A₂ m n) a b)
      = (Work.Cohomology.mixedRelStar ℚ X₁ A₁ m n)
          ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f m)) a)
          (Work.Cohomology.relMapLM ℚ A₁ A₂ f h n b) := by
  apply Subtype.ext
  show ((Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f (m+n)).hom
        (Work.Cohomology.cup ℚ (TopCat.toSSet.obj X₂) a b.1)
      = Work.Cohomology.cup ℚ (TopCat.toSSet.obj X₁)
          (((Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f m).hom a)
          (((Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f n).hom b.1)
  rw [dualChainMap_f_apply, dualChainMap_f_apply, dualChainMap_f_apply]
  exact (Work.Cohomology.cupNatural ℚ (TopCat.toSSet.map f) a (b.1)).symm

end Work.Serre.MVShift
