import Mathlib
import Submission.Work.CFTLib.splitsCompletelySet
import Submission.Work.CFTLib.dirichletDensity_utils
import Submission.Work.CFTLib.finite_sdiff_inertiaDegIn_splitsCompletelySet

set_option linter.style.haveILetI false

namespace Work.CFTLib

open NumberField

/-- Universe-polymorphic form of `Work.CFTLib.splitSetOf_density`: the primes of `K` whose inertia
degree in the finite Galois extension `L` is `1` have Dirichlet density `1 / [L : K]`.

(`Work.CFTLib.splitSetOf_density` is the same statement with `K` and `L` restricted to `Type 0`,
which is not enough for the `Type*`-polymorphic target of this file, so the short proof is
repeated here.) -/
theorem inertiaDegIn_one_density {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
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

/-- If `v` splits completely in the finite Galois extension `↥L / K`, then its inertia degree in
`↥L` is `1`.  Indeed some prime `P` of `𝓞 ↥L` lies over `v`, and complete splitting forces
`e(P/v) = f(P/v) = 1`. -/
theorem inertiaDegIn_eq_one_of_splitsCompletelyIn {K A : Type*} [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] (L : IntermediateField K A) [FiniteDimensional K L]
    [IsGalois K ↥L] {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    (h : Work.Tower.SplitsCompletelyIn K ↥L v.asIdeal) :
    Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L) = 1 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 ↥L)))
  haveI := P.2.1
  haveI := P.2.2
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := 𝓞 K) (B := 𝓞 ↥L) v.asIdeal P.1
    Gal(↥L/K)]
  exact (Work.Tower.Unramified.ef_eq_one_of_splitsCompletelyIn v.ne_bot h P).2

/-- The completely split primes differ from the inertia-degree-`1` primes only in a finite set, in
the direction `splitsCompletelySet ⊆ {f = 1}`: in fact the difference is empty. -/
theorem finite_sdiff_splitsCompletelySet_inertiaDegIn {K A : Type*} [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] (L : IntermediateField K A) [FiniteDimensional K L]
    [IsGalois K ↥L] :
    (splitsCompletelySet L \
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L) = 1}).Finite := by
  refine Set.Finite.subset Set.finite_empty ?_
  rintro v ⟨hv, hne⟩
  exact hne (inertiaDegIn_eq_one_of_splitsCompletelyIn L ((mem_splitsCompletelySet L v).mp hv))

/-- **Dirichlet density of the completely split primes.**  In a finite Galois extension `↥L / K`
of number fields the set of primes of `K` splitting completely in `L` has Dirichlet density
`1 / [L : K]`.

The set `Work.CFTLib.splitsCompletelySet L` differs from `{v | inertiaDegIn v (𝓞 ↥L) = 1}` —
whose density is `1 / [L : K]` by `Work.CFTLib.inertiaDegIn_one_density` — only in the finite set of
primes of `K` that ramify in `L`; the two inclusions are
`Work.CFTLib.finite_sdiff_inertiaDegIn_splitsCompletelySet` and
`Work.CFTLib.finite_sdiff_splitsCompletelySet_inertiaDegIn`, and the density is insensitive to a
finite symmetric difference by `NK.BauerGeneral.hasDirichletDensity_of_symmDiff_finite`. -/
theorem hasDirichletDensity_splitsCompletelySet {K A : Type*} [Field K] [NumberField K] [Field A]
    [NumberField A] [Algebra K A] (L : IntermediateField K A) [FiniteDimensional K L]
    [IsGalois K ↥L] :
    NumberField.Set.HasDirichletDensity (splitsCompletelySet L)
      (1 / (Module.finrank K ↥L : ℝ)) := by
  have hAB : ({v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L) = 1} \ splitsCompletelySet L).Finite :=
    finite_sdiff_inertiaDegIn_splitsCompletelySet L
  have hBA : (splitsCompletelySet L \
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L) = 1}).Finite :=
    finite_sdiff_splitsCompletelySet_inertiaDegIn L
  have hA : NumberField.Set.HasDirichletDensity
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L) = 1}
      (1 / (Module.finrank K ↥L : ℝ)) :=
    inertiaDegIn_one_density (K := K) (L := ↥L)
  exact NK.BauerGeneral.hasDirichletDensity_of_symmDiff_finite hAB hBA hA

end Work.CFTLib
