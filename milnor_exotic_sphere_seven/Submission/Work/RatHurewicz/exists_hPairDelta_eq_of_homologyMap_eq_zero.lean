import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The connecting map of a pair is surjective onto the kernel of the inclusion

For a topological space `X`, a subset `A ⊆ X` and `n : ℕ`, the connecting homomorphism

`δ : H_{n+1}(X,A) ⟶ H_n(A)`

of the long exact sequence of the pair `(X,A)` maps onto the kernel of the map
`H_n(A) ⟶ H_n(X)` induced by the inclusion.  This is precisely exactness of the long exact
sequence at `H_n(A)`.

The statement is phrased elementwise: every `z ∈ H_n(A)` whose image in `H_n(X)` vanishes is
`δ a` for some `a ∈ H_{n+1}(X,A)`.  This is the form in which the lemma is used (e.g. by the
rational Hurewicz comparison), where one wants to *lift* a class in the kernel.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

/-- Exactness of the long exact sequence of the pair `(X,A)` at `H_n(A)`, in elementwise form:
a class in `H_n(A)` killed by the inclusion `H_n(A) ⟶ H_n(X)` is the image of the connecting
homomorphism `δ : H_{n+1}(X,A) ⟶ H_n(A)`. -/
theorem exists_hPairDelta_eq_of_homologyMap_eq_zero (X : TopCat) (A : Set X) (n : ℕ)
    (z : ↥((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology n))
    (hz : HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) n z = 0) :
    ∃ a : ↥((Work.Cohomology.relChains X A).homology (n + 1)),
      Work.Cohomology.hPairδ X A n a = z := by
  -- The short complex `H_{n+1}(X,A) --δ--> H_n(A) --i_*--> H_n(X)`, exact at `H_n(A)`.
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (Work.Cohomology.hPairδ X A n)
      (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) n)
      (Work.Cohomology.hPairδ_comp X A n)
  have hex : S.Exact := Work.Cohomology.hPair_exact₁ X A n
  -- In `ModuleCat ℤ` exactness is exactly the elementwise lifting property.
  exact (ShortComplex.moduleCat_exact_iff S).1 hex z hz

end Work.RatHurewicz
