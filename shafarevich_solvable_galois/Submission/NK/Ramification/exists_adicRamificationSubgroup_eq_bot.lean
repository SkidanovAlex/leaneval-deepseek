import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.CommonsBridge
import Submission.NK.Ramification.exists_ramificationSubgroup_eq_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.Ramification

theorem exists_adicRamificationSubgroup_eq_bot {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ N : ℕ, NK.Ramification.ramificationSubgroup (K := Q.adicCompletion K)
        (q.adicCompletionIntegers L) N = ⊥ := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- `L_q` is a finite-dimensional `K_Q`-vector space, so the local Galois group is finite, and
  -- therefore so is the decomposition subgroup of `𝒪_{L_q}`.
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Fintype (Gal(q.adicCompletion L / Q.adicCompletion K)) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  haveI : Finite ((q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K)) :=
    Finite.of_injective
      (fun σ : (q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K) =>
        (σ : Gal(q.adicCompletion L / Q.adicCompletion K)))
      Subtype.val_injective
  -- `𝒪_{L_q}` is a discrete valuation ring, hence Noetherian, so Krull's intersection theorem
  -- applies and the filtration is eventually trivial.
  exact exists_ramificationSubgroup_eq_bot (K := Q.adicCompletion K)
    (L := q.adicCompletion L) (q.adicCompletionIntegers L)

end NK.Ramification
