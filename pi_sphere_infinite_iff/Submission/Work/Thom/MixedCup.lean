import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.sph3DiscMixedDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The mixed cup product and the forgetful map

The relative cohomology `H^*(X,A;R)` is a module over the absolute cohomology `H^*(X;R)`, and the
forgetful map `H^*(X,A;R) → H^*(X;R)` is compatible with this structure:

  `relToAbs (x ⌣ y) = x ⌣ relToAbs y`   for `x ∈ H^m(X;R)`, `y ∈ H^n(X,A;R)`.

This is the mixed analogue of `Work.Cohomology.relIncl_relCupH`, and it is what turns the Thom
isomorphism into multiplication by the Euler class in the Gysin sequence
(`Submission/Work/Thom/Gysin.lean`).
-/

namespace Work.Thom

open CategoryTheory
open Work.TangentClasses

noncomputable section

/-- The `ℤ`-valued mixed cup product of `Submission/Work/Cohomology/sph3DiscMixedDefs.lean` is the
generic one of this chapter. -/
theorem mixedCupC_eq_mixedCup {X : Type} [TopologicalSpace X] (A : Set X) (m n : ℕ) :
    mixedCupC ℤ A m n = Work.Cohomology.mixedCup (TopCat.of X) A m n := rfl

/-- The forgetful map on the class of a relative cocycle. -/
theorem relToAbs_relClassOf {X : Type} [TopologicalSpace X] (A : Set X) {n : ℕ}
    (a : Work.Cohomology.relKern ℤ (TopCat.of X) A n)
    (ha : Work.Cohomology.relDiffLM ℤ (TopCat.of X) A n a = 0) :
    (relToAbs ℤ A n).hom (Work.Cohomology.relClassOf ℤ (TopCat.of X) A a ha) =
      Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) a.1
        (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) A a ha) :=
  Work.Cohomology.relIncl_homologyMap_relClassOf ℤ (TopCat.of X) A a ha

/-- **The mixed cup product is compatible with the forgetful map**:
`relToAbs (x ⌣ y) = x ⌣ relToAbs y`. -/
theorem mixedCup_relToAbs {X : Type} [TopologicalSpace X] (A : Set X) (m n : ℕ)
    (x : Coh ℤ m X) (y : RelCoh ℤ n X A) :
    (relToAbs ℤ A (m + n)).hom ((mixedCupC ℤ A m n) x y) =
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) m n x
        ((relToAbs ℤ A n).hom y) := by
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) m x
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of X) A n y
  obtain ⟨hmem, hd, hcup⟩ := Work.Cohomology.mixedCup_apply (X := TopCat.of X) A m n a b ha hb
  rw [mixedCupC_eq_mixedCup, hcup]
  rw [relToAbs_relClassOf A ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) a b.1, hmem⟩ hd]
  rw [relToAbs_relClassOf A b hb]
  rw [Work.Cohomology.cupH'_apply' ℤ (TopCat.toSSet.obj (TopCat.of X)) a b.1 ha
      (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) A b hb)]

end

end Work.Thom
