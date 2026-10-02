import Submission.Work.Cohomology.relCapHHom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cap product, packaged

`Submission/Work/Cohomology/relCapHHom.lean` proves the existence of the relative cap product
pairing

  `H^n(X,A;ℤ) →ₗ (H_{n+m}(X,A;ℤ) →ₗ H_m(X;ℤ))`

(as an unexplicit `∃`).  This file fixes the pairing once and for all (`relCapPair`, with its
cycle-level partner `relCapPairZ`) and records its computation rules, in the style of
`Submission/Work/Cohomology/CapH.lean`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The relative cap product on cycles**: a choice of the pairing `capZ` whose existence is
`Work.Cohomology.relCapHHom`. -/
noncomputable def relCapPairZ (X : TopCat) (A : Set X) (n m : ℕ) :
    (relComplex ℤ X A).cycles n →ₗ[ℤ]
      ((relChains X A).cycles (n + m) →ₗ[ℤ] (singularChains ℤ X).cycles m) :=
  Classical.choose (relCapHHom X A n m)

/-- **The relative cap product pairing**
`H^n(X,A;ℤ) →ₗ (H_{n+m}(X,A;ℤ) →ₗ H_m(X;ℤ))`, a choice of the pairing whose existence is
`Work.Cohomology.relCapHHom`. -/
noncomputable def relCapPair (X : TopCat) (A : Set X) (n m : ℕ) :
    relCohomology ℤ X A n →ₗ[ℤ]
      ((relChains X A).homology (n + m) →ₗ[ℤ] (singularChains ℤ X).homology m) :=
  Classical.choose (Classical.choose_spec (relCapHHom X A n m))

/-- **The computation rule for `relCapPairZ`**: on a relative cocycle `z` and a relative cycle `c`
the cycle-level cap product is the chain-level relative cap product of the underlying (co)chains. -/
theorem relCapPairZ_iCycles (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) (c : (relChains X A).cycles (n + m)) :
    (singularChains ℤ X).iCycles m (relCapPairZ X A n m z c) =
      relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m
        ((relChains_cokernelIso X A (n + m)).hom (((relChains X A).iCycles (n + m)) c)) :=
  (Classical.choose_spec (Classical.choose_spec (relCapHHom X A n m))).1 z c

/-- **The computation rule for `relCapPair`**: on the classes of a relative cocycle `z` and a
relative cycle `c` the value is the homology class of `relCapPairZ z c`. -/
theorem relCapPair_apply (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) (c : (relChains X A).cycles (n + m)) :
    relCapPair X A n m (((relComplex ℤ X A).homologyπ n).hom z)
        (((relChains X A).homologyπ (n + m)).hom c)
      = ((singularChains ℤ X).homologyπ m).hom (relCapPairZ X A n m z c) :=
  (Classical.choose_spec (Classical.choose_spec (relCapHHom X A n m))).2 z c

end

end Work.Cohomology
