import Mathlib
import Submission.Work.Kunneth.CrossHBilin
import Submission.Work.Kunneth.pullbackH_cohomologyClassOf
import Submission.Work.Cohomology.cupNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pullback on cohomology is a ring map

The pullback `Work.Kunneth.pullbackH X Y f n : H^n(Y;ℤ) → H^n(X;ℤ)` along a simplicial map
`f : X ⟶ Y` commutes with the cup product:

`f*(a ⌣ b) = f*(a) ⌣ f*(b)`.

This is the cohomology-level form of the cochain-level naturality of the Alexander–Whitney cup
product (`Work.Cohomology.cupNatural`), with `Work.Cohomology.Kunneth.ssetPullback` the explicit
name of the cochain pullback.  It is what makes every multiplicativity statement about the cross
product `crossH X Y p q a b = π₁^*a ⌣ π₂^*b` reduce to a statement about the cup product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [local instance 5000] AddCommGroup.toIntModule

/-- **Multiplicativity of the pullback on cohomology**: `f*(a ⌣ b) = f*(a) ⌣ f*(b)`. -/
theorem pullbackH_cupH (X Y : SSet) (f : X ⟶ Y) (p q : ℕ)
    (a : ↥((Work.Cohomology.cochainC ℤ Y).homology p))
    (b : ↥((Work.Cohomology.cochainC ℤ Y).homology q)) :
    pullbackH X Y f (p + q) (Work.Cohomology.cupH' ℤ Y p q a b)
      = Work.Cohomology.cupH' ℤ X p q (pullbackH X Y f p a) (pullbackH X Y f q b) := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ Y p a
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ Y q b
  rw [Work.Cohomology.cupH'_apply' ℤ Y α β hα hβ]
  rw [pullbackH_cohomologyClassOf X Y f (p + q) (Work.Cohomology.cup ℤ Y α β)
    (Work.Cohomology.cochainDiff_cup_of_cocycles ℤ Y α β hα hβ)]
  rw [pullbackH_cohomologyClassOf X Y f p α hα,
    pullbackH_cohomologyClassOf X Y f q β hβ]
  rw [Work.Cohomology.cupH'_apply' ℤ X
    (Work.Cohomology.Kunneth.ssetPullback X Y f p α)
    (Work.Cohomology.Kunneth.ssetPullback X Y f q β)
    (Work.Cohomology.pxSsetPullback_cocycle X Y f p α hα)
    (Work.Cohomology.pxSsetPullback_cocycle X Y f q β hβ)]
  apply Work.Cohomology.cohomologyClassOf_congr
  exact (Work.Cohomology.cupNatural ℤ f α β).symm

end

end Work.Kunneth
