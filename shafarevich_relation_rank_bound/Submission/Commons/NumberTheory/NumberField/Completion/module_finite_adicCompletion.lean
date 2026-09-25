import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

/-- The `q`-adic completion of `L` is a finite module over the `Q`-adic completion of `K`,
when the prime `q` of `𝓞 L` lies over the prime `Q` of `𝓞 K`.

This is the module-finiteness half of the local fundamental identity `[L_q : K_Q] = e·f` for
extensions of number fields: `L_q` is a finite-dimensional vector space over the local field
`K_Q`.  The module structure on `q.adicCompletion L` is the one induced by the continuous
algebra map `Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+*
q.adicCompletion L`.

*Proof sketch.*  Registering this map as a local `Algebra` instance, the canonical
`K_Q`-linear map `K_Q ⊗[K] L → L_q` given by `x ⊗ l ↦ iF x · l` is continuous; its range is
dense because `L` is dense in `L_q`, and it is closed because it is finite-dimensional over the
field `K_Q` (`Submodule.closed_of_finiteDimensional`).  Hence that map is surjective, making
`L_q` a quotient -- and therefore a finitely generated module -- of the finite-dimensional
vector space `K_Q ⊗[K] L` (a finite `K_Q`-module because `L` is a finite extension of `K`).
This is exactly Mathlib's instance `NumberField.HeightOneSpectrum.Module.Finite` (in
`NumberTheory/NumberField/Completion/FinitePlace.lean`), which we instantiate after supplying
the `Algebra`, `ContinuousSMul` and `IsScalarTower` typeclass data. -/
theorem module_finite_adicCompletion
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    @Module.Finite (Q.adicCompletion K) (q.adicCompletion L) _ _
      (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hcont : Continuous (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) := by
    change Continuous (Commons.RingTheory.Henselian.adicCompletionMap Q q hq :
      Q.adicCompletion K → q.adicCompletion L)
    exact Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq
  haveI : ContinuousSMul (Q.adicCompletion K) (q.adicCompletion L) :=
    continuousSMul_of_algebraMap (Q.adicCompletion K) (q.adicCompletion L) hcont
  haveI : IsScalarTower K (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Q.adicCompletion K) (A := q.adicCompletion L) (by
      intro k
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (S := K) (v := q) (K := L)]
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (S := K) (v := Q) (K := K)]
      exact (Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq k).symm)
  exact (inferInstance : Module.Finite (Q.adicCompletion K) (q.adicCompletion L))

end Commons.NumberTheory.NumberField.Completion