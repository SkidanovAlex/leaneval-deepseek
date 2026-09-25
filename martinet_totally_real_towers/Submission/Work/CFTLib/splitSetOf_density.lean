import Mathlib
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.NK.BauerGeneral.hasDirichletDensity_of_symmDiff_finite

namespace Work.CFTLib

open NumberField

/-- In a finite Galois extension `L / K` of number fields, only finitely many primes of `K` have
ramification index `≠ 1` in `L`.  (A prime of `𝓞 K` is ramified in `L` iff every — equivalently,
some — prime of `𝓞 L` above it has ramification index `≠ 1`.) -/
theorem finite_setOf_ramificationIdxIn_ne_one {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      v.asIdeal.ramificationIdxIn (𝓞 L) ≠ 1}.Finite := by
  classical
  have hA : {q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      q.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
  refine (hA.image (fun q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) =>
    IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) q)).subset ?_
  intro v hv
  obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  refine ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot P.2⟩, ?_, ?_⟩
  · intro h
    exact hv ((Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 (Gal(L/K))).trans h)
  · exact IsDedekindDomain.HeightOneSpectrum.ext (by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact P.2.2.over.symm)

/-- The set of primes of `K` whose inertia degree in a finite Galois extension `L` is `1` has
Dirichlet density `1 / [L : K]`.

(The proof needs `Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`,
which gives density `1/[L:K]` for the completely split primes; the two sets differ only in the
finitely many primes ramifying in `L`, using
`Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one` and
`hasDirichletDensity_zero_of_finite`.) -/
theorem splitSetOf_density {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    NumberField.Set.HasDirichletDensity
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1}
      (1 / (Module.finrank K L : ℝ)) := by
  classical
  have hsplit : NumberField.Set.HasDirichletDensity
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L}
      (1 / (Module.finrank K L : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
      (K := K) (L := L)
  refine NK.BauerGeneral.hasDirichletDensity_of_symmDiff_finite ?_ ?_ hsplit
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro v ⟨hvA, hvB⟩
    have hiff := Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := L) v
    exact hvB (hiff.mp hvA).2
  · refine (finite_setOf_ramificationIdxIn_ne_one (K := K) (L := L)).subset ?_
    rintro v ⟨hvB, hvA⟩
    intro he
    have hiff := Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := L) v
    exact hvA (hiff.mpr ⟨he, hvB⟩)

end Work.CFTLib
