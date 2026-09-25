import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers

/-!
# Any `K_Q`-algebra automorphism of the `q`-adic completion of `L` is continuous

Let `L / K` be an extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  The inclusion `K → L` induces a ring homomorphism
`adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L` between the corresponding
adic completions, hence makes `q.adicCompletion L` into a `Q.adicCompletion K`-algebra.

The main result of this file is that *every* `Q.adicCompletion K`-algebra automorphism of
`q.adicCompletion L` is continuous for the `q`-adic topology.  This is the analytic input which
guarantees that the Galois action on the local field `L_q` is by homeomorphisms.

The proof avoids any explicit analysis of the valuation: the ring
`Q.adicCompletion K` is a complete (non-trivially) normed field, and `q.adicCompletion L` is a
finite-dimensional topological vector space over it — a finitely generated module by
`Module.Finite` (Mathlib's `HeightOneSpectrum.instModuleFinite`), so every linear map is
automatically continuous (`LinearMap.continuous_of_finiteDimensional`).  In particular the linear
map underlying `τ` is continuous.
-/

open scoped NumberField Valued WithZero

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField

/-- **Every `Q`-adic-algebra automorphism of the `q`-adic completion of `L` is continuous.**

Here `q` is a height-one prime of `𝓞 L` lying over the height-one prime `Q` of `𝓞 K`, and
`q.adicCompletion L` is regarded as a `Q.adicCompletion K`-algebra through the natural map
`adicCompletionMap Q q hq` induced by the inclusion `K → L`. -/
theorem continuous_algEquiv_adicCompletion {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (τ : letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :
    Continuous τ := by
  -- The `Q.adicCompletion K`-algebra structure on `q.adicCompletion L`.
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- The two algebra structures `K → Q.adicCompletion K → q.adicCompletion L` and
  -- `K → L → q.adicCompletion L` agree, i.e. they form a scalar tower.
  haveI : IsScalarTower K (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Q.adicCompletion K) (A := q.adicCompletion L) (by
      intro k
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (S := K) (v := q) (K := L)]
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (S := K) (v := Q) (K := K)]
      exact (Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq k).symm)
  -- The scalar action is continuous because the algebra map `adicCompletionMap` is.
  haveI : ContinuousSMul (Q.adicCompletion K) (q.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    exact Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq
  -- `q.adicCompletion L` is a finitely generated module over the complete field
  -- `Q.adicCompletion K` (Mathlib's `HeightOneSpectrum.instModuleFinite`).
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) := inferInstance
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) := inferInstance
  haveI : CompleteSpace (Q.adicCompletion K) := inferInstance
  haveI : T2Space (q.adicCompletion L) := inferInstance
  -- Any linear map on a finite-dimensional Hausdorff topological vector space over a complete
  -- (non-trivially) normed field is continuous.
  exact LinearMap.continuous_of_finiteDimensional (𝕜 := Q.adicCompletion K) τ.toLinearMap

end Commons.NumberTheory.NumberField