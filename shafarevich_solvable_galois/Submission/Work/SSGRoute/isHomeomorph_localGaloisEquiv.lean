import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.Work.SSGRoute.E7aAux

/-!
# The identification `D_A ≃* Gal(κ̄/κ)` is a homeomorphism

`NK.Mine.localGaloisEquiv` identifies the decomposition group `D_A` of a finite place `A` of `Ω`
over the number field `k` with the absolute Galois group of the local field `κ = k_𝔭`, where `𝔭`
is the prime of `k` below `A`.  This file proves that this identification is a homeomorphism for
the Krull topologies.

The isomorphism is by construction the composite of the two constituent maps whose
homeomorphism property is established in
`Submission/NK/Mine/exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map`:

* `NK.Mine.adjoinLocalEquiv : D_A ≃* Aut_κ(κ·Ω)`, `σ ↦ σ̂|_{κ·Ω}` is a homeomorphism
  (`NK.Mine.isHomeomorph_adjoinLocalEquiv`);
* `AlgEquiv.autCongr e : Aut_κ(κ·Ω) ≃* Gal(κ̄/κ)` for an isomorphism `e` of separable closures is a
  homeomorphism (`NK.Mine.isHomeomorph_autCongr`).

Both live in `NK.Mine` (their proof is the local computation of
`isHomeomorph_adjoinLocalEquiv`, respectively the permutation of the neighbourhood basis at `1` by
conjugation), and they compose by `NK.Mine.isHomeomorph_trans`.
-/

namespace Work.SSGRoute

open scoped Topology

theorem isHomeomorph_localGaloisEquiv (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
    IsHomeomorph (NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
        (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
        (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
          (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))
      : ↥(SSGRoute.decomp k A) →
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA)) := by
  -- the `κ`-algebra structure on `placeCompletion A` prescribed by the statement
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  have hW := NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
  -- `M = κ·Ω` is a separable closure of `κ`, hence `Gal(M/κ)` is a Krull topological group
  haveI : IsSepClosure (Work.SSGRoute.localFieldAt k A hA)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
  -- `localGaloisEquiv = adjoinLocalEquiv.trans (AlgEquiv.autCongr (adjoinSepEquiv _))`
  exact NK.Mine.isHomeomorph_trans
    (NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl) hW)
    (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)))
    (NK.Mine.isHomeomorph_adjoinLocalEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl) hW)
    (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)))

end Work.SSGRoute
