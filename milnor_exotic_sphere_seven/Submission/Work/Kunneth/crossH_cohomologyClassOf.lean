import Mathlib
import Submission.Work.Kunneth.pullbackH_cohomologyClassOf
import Submission.Work.Kunneth.crossCochain_isCocycle
import Submission.Work.Kunneth.CrossHBilin
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cross product on cohomology computed on the classes of cocycles

`Work.Kunneth.crossH X Y p q` is the cross product `Hᵖ(X;ℤ) → H^q(Y;ℤ) → H^{p+q}(X ⊗ Y;ℤ)`,
defined by `a × b = π₁^* a ⌣ π₂^* b` (`Work.Kunneth.crossH_apply`).  This file computes it on the
cohomology classes of two cocycles `α`, `β`: the cross product of their classes is the class of
the cross product of the cochains,

  `[α] × [β] = [α × β]`.

The proof is the expected one: unfold the definition of the cross product, use naturality of the
cohomology class under pullback (`Work.Kunneth.pullbackH_cohomologyClassOf`) on each factor, apply
the computation rule for the cup product on classes of cocycles
(`Work.Cohomology.cupH'_apply'`), and identify the cup product `π₁^*α ⌣ π₂^*β` with the cross
product of cochains by `Work.Kunneth.crossCochain_eq_cup`.  The two cocycle conditions for this
last cochain agree propositionally, so the classes agree by
`Work.Cohomology.cohomologyClassOf_congr`.
-/

namespace Work.Kunneth

/-- **The cross product on the classes of two cocycles is the class of the cross product of the
cochains.** -/
theorem crossH_cohomologyClassOf (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q)
    (hα : Work.Cohomology.cochainDiff ℤ X α = 0) (hβ : Work.Cohomology.cochainDiff ℤ Y β = 0)
    (h : Work.Cohomology.cochainDiff ℤ (Work.Kunneth.sProd X Y)
      (Work.Kunneth.crossCochain X Y p q α β) = 0) :
    Work.Kunneth.crossH X Y p q (Work.Cohomology.cohomologyClassOf ℤ X α hα)
        (Work.Cohomology.cohomologyClassOf ℤ Y β hβ)
      = Work.Cohomology.cohomologyClassOf ℤ (Work.Kunneth.sProd X Y)
          (Work.Kunneth.crossCochain X Y p q α β) h := by
  rw [Work.Kunneth.crossH_apply,
    Work.Kunneth.pullbackH_cohomologyClassOf (Work.Kunneth.sProd X Y) X
      (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p α hα,
    Work.Kunneth.pullbackH_cohomologyClassOf (Work.Kunneth.sProd X Y) Y
      (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q β hβ,
    Work.Cohomology.cupH'_apply']
  exact Work.Cohomology.cohomologyClassOf_congr ℤ (Work.Kunneth.sProd X Y)
    (Work.Kunneth.crossCochain_eq_cup X Y p q α β).symm _ _

end Work.Kunneth
