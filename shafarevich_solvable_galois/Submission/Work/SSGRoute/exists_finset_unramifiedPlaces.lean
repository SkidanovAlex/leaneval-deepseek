import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.finite_not_isUnramifiedAt_primes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped NumberField

/-- **All but finitely many places of a finite Galois extension are unramified, lie over a place of
the base, and have ramification index `1`.**

For a finite Galois extension `L/k` of number fields there is a finite set `T` of places of `L`
such that every place `w ∉ T` is finite, `w = ofFinite q` for a prime `q` of `𝓞 L` lying over a
prime `Q` of `𝓞 k`, and `q` has ramification index `1` over `k`.

The set `T` is the union of the (finitely many) archimedean places of `L` and of the finitely many
finite primes of `L` with `ramificationIdx ≠ 1`, which are finite in number by
`Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one`. -/
theorem exists_finset_unramifiedPlaces (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] :
    ∃ T : Finset (NK.GlobalCFT.Place L), ∀ w ∉ T,
      ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
        (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)),
        w = NK.GlobalCFT.Place.ofFinite q ∧ q.asIdeal.LiesOver Q.asIdeal ∧
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
  classical
  -- The finite primes of `L` that ramify over `k` are finite in number.
  have hbad : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) ≠ 1} : Set _).Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
  refine ⟨hbad.toFinset.image NK.GlobalCFT.Place.ofFinite ∪
      (Finset.univ.image (NK.GlobalCFT.Place.ofInfinite (K := L))), ?_⟩
  intro w hw
  cases w with
  | inl w' =>
    -- an archimedean place lies in `T`
    exact absurd (Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ w')))) hw
  | inr q =>
    -- a nonarchimedean place: its prime does not ramify over `k`
    have hq : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
      by_contra h
      refine hw (Finset.mem_union.mpr (Or.inl ?_))
      exact Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset hbad).mpr h)
    exact ⟨q, ⟨q.asIdeal.under (𝓞 k), inferInstance, Ideal.under_ne_bot _ q.ne_bot⟩,
      rfl, inferInstance, hq⟩

end Work.SSGRoute
