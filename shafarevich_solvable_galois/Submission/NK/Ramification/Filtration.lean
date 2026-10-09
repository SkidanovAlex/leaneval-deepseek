/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The filtration at a finite level of a `p`-adic field

`NK.Ramification.ramificationSubgroup` needs a valuation ring of the top field.  For a finite
extension `E` of a `p`-adic field `κ = 𝔭.adicCompletion K` presented inside a separable closure
`K'`, the classical theory says that the valuation of `κ` extends uniquely to `E`, so `E` carries a
canonical valuation ring.  This file produces *a* valuation ring for such an `E`
(`finiteExtensionIntegers`), by transporting the ring of integers of `q.adicCompletion L` along
the isomorphism `E ≃ₐ[κ] q.adicCompletion L` supplied by
`Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional`,
and records its two structural properties (it is a discrete valuation ring, and it is stabilised by
every `κ`-algebra automorphism — the "Galois-stability" that makes the higher ramification
subgroups subgroups of the full local Galois group).

Classically the valuation ring of `E` is *unique* (the extension of a complete valuation to a
finite extension is unique), so every choice gives the same object; that uniqueness is not proved
here, but the two properties below are exactly what the ramification theory consumes.
-/
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.CommonsBridge
import Submission.NK.Ramification.exists_valuationSubring_finiteDimensional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.Ramification

universe u

noncomputable section

/-- **A valuation ring of a finite extension of a `p`-adic field.**  For `B` a finite extension of
`Q.adicCompletion K`, this is the (classically unique) valuation ring of `B` extending that of
`Q.adicCompletion K`, obtained by transporting `q.adicCompletionIntegers L` along the isomorphism
`B ≃ₐ[Q.adicCompletion K] q.adicCompletion L` of
`exists_algEquiv_adicCompletion_of_finiteDimensional`. -/
def finiteExtensionIntegers {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : Type u) [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] : ValuationSubring B :=
  Classical.choose (exists_valuationSubring_finiteDimensional Q (B := B))

/-- The valuation ring of a finite extension of a `p`-adic field is a discrete valuation ring. -/
theorem finiteExtensionIntegers_isDiscreteValuationRing {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : Type u) [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] :
    IsDiscreteValuationRing (finiteExtensionIntegers Q B) :=
  (Classical.choose_spec (exists_valuationSubring_finiteDimensional Q (B := B))).1

/-- **Galois-stability**: every `Q.adicCompletion K`-algebra automorphism of `B` preserves the
valuation ring of `B`.  This is what makes the higher ramification subgroups subgroups of the
*whole* local Galois group. -/
theorem finiteExtensionIntegers_decompositionSubgroup_eq_top {K : Type u} [Field K]
    [NumberField K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : Type u) [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] :
    (finiteExtensionIntegers Q B).decompositionSubgroup (Q.adicCompletion K) = ⊤ :=
  (Classical.choose_spec (exists_valuationSubring_finiteDimensional Q (B := B))).2

end

end NK.Ramification
