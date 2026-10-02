import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.cupNaturalH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cup product, and its compatibility with the absolute one

`Work.Cohomology.relCupH` produces *some* bilinear pairing on the relative cohomology
`H^*(X,A;R)` with the defining computation rule on classes of relative cocycles.  This file fixes a
*chosen* witness `relCupH'` (and records its computation rule), so that statements about "the"
relative cup product can be made without an `∃`, in the same way that `Work.Cohomology.cupH'`
fixes a witness of the absolute cup product `Work.Cohomology.cupH`.

The main theorem (delegated, see `Submission/Work/Cohomology/relIncl_relCupH.lean`) is that the map
`H^*(X,A;R) → H^*(X;R)` induced by the inclusion of complexes `relIncl` (the forgetful map, sending
a class relative to `A` to its absolute class) is a **ring homomorphism** for these products:

  `relIncl_*(x ⌣_rel y) = (relIncl_* x) ⌣ (relIncl_* y)`.

This is what lets one transfer the computation of `x ⌣ x` for the capped manifold `X` to the
relative pair `(X, D⁸) ≅ (Vk (-2), Mk (-2))` (see `Submission/NOTES.md` §12.4).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- **The chosen relative cup product** on `H^*(X,A;R)`: a fixed witness of `Work.Cohomology.relCupH`. -/
noncomputable def relCupH' (X : TopCat) (A : Set X) (n m : ℕ) :
    relCohomology R X A n →ₗ[R] relCohomology R X A m →ₗ[R] relCohomology R X A (n + m) :=
  (Classical.choose (relCupH R X A)) n m

/-- The defining computation rule of the chosen relative cup product, on classes of relative
cocycles. -/
theorem relCupH'_apply (X : TopCat) (A : Set X) {n m : ℕ}
    (a : relKern R X A n) (b : relKern R X A m)
    (ha : relDiffLM R X A n a = 0) (hb : relDiffLM R X A m b = 0) :
    relCupH' R X A n m (relClassOf R X A a ha) (relClassOf R X A b hb) =
      relClassOf R X A (relCup R X A n m a b)
        (relDiffLM_relCup_of_cocycles R X A a b ha hb) :=
  Classical.choose_spec (relCupH R X A) n m a b ha hb

/-- The underlying cochain of a relative cocycle is an absolute cocycle. -/
theorem relClassOf_cochainDiff (X : TopCat) (A : Set X) {n : ℕ} (a : relKern R X A n)
    (ha : relDiffLM R X A n a = 0) :
    cochainDiff R (TopCat.toSSet.obj X) a.1 = 0 := by
  have h := congrArg Subtype.val ha
  simp only [relDiffLM_coe, Submodule.coe_zero] at h
  rw [singularCochain_d_apply R X a.1] at h
  exact h

end

end Work.Cohomology
