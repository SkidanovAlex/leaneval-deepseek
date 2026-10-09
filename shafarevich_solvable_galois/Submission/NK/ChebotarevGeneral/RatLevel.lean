/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# The rational level: from the density theorem to `NK.WeakNU.ChebotarevFrobeniusInput`

This file converts the Dirichlet-density form of Čebotarev's theorem (`ChebotarevDensity`) into the
existence form consumed by the Neukirch–Uchida development
(`NK.WeakNU.ChebotarevFrobeniusInput`), and draws the consequences of the reduction of the
general case to the abelian case.

The conversion uses that the finite places of `ℚ` are in bijection with the rational primes via the
absolute norm of the contraction to `ℤ` (`ratPrimeOf`), so that an infinite set of prime ideals of
`𝓞 ℚ` gives infinitely many rational primes.
-/
import Submission.NK.ChebotarevGeneral.Basic
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
import Submission.NK.WeakNU.primeCountAbove_under_eq_primesOverRat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.ChebotarevGeneral

noncomputable section

open NK.Chebotarev

/-! ## Finite places of `ℚ` and rational primes -/

/-- **The rational prime below a finite place of `ℚ`**: the absolute norm of the contraction of
`𝔭` to `ℤ`.  This is a bijection from the finite places of `ℚ` to the rational primes. -/
def ratPrimeOf (𝔭 : PrimeIdeal ℚ) : ℕ := Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)

theorem ratPrimeOf_prime (𝔭 : PrimeIdeal ℚ) : (ratPrimeOf 𝔭).Prime := by
  haveI : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
  exact Nat.absNorm_under_prime 𝔭.asIdeal

theorem ideal_span_ratPrimeOf (𝔭 : PrimeIdeal ℚ) :
    Ideal.span {((ratPrimeOf 𝔭 : ℕ) : ℤ)} = Ideal.under ℤ 𝔭.asIdeal :=
  Int.ideal_span_absNorm_eq_self _

theorem ratPrimeOf_injective : Function.Injective ratPrimeOf := by
  intro 𝔭 𝔮 h
  have h' : Ideal.under ℤ 𝔭.asIdeal = Ideal.under ℤ 𝔮.asIdeal := by
    rw [← ideal_span_ratPrimeOf 𝔭, ← ideal_span_ratPrimeOf 𝔮, h]
  rw [Ideal.under_def] at h'
  refine IsDedekindDomain.HeightOneSpectrum.ext ?_
  exact Ideal.comap_injective_of_surjective (algebraMap ℤ (NumberField.RingOfIntegers ℚ))
    (Rat.int_algebraMap_surjective (NumberField.RingOfIntegers ℚ)) h'

/-- **`LiesOver` the rational prime `p` is `LiesOver` the finite place of `ℚ` whose norm is
`p`.** -/
theorem liesOver_span_ratPrimeOf_iff {N : Type} [Field N] [NumberField N] [Algebra ℚ N]
    (𝔭 : PrimeIdeal ℚ) (P : PrimeIdeal N) :
    P.asIdeal.LiesOver (Ideal.span {((ratPrimeOf 𝔭 : ℕ) : ℤ)}) ↔
      P.asIdeal.LiesOver 𝔭.asIdeal := by
  rw [ideal_span_ratPrimeOf 𝔭, Ideal.under_def]
  exact (NK.WeakNU.liesOver_iff_liesOver_comap_of_surjective
    (A := ℤ) (B := NumberField.RingOfIntegers ℚ) (C := NumberField.RingOfIntegers N)
    (Rat.int_algebraMap_surjective (NumberField.RingOfIntegers ℚ)) P.asIdeal 𝔭.asIdeal).symm

/-! ## From the density form to the existence form -/

/-- **Čebotarev's density theorem implies `NK.WeakNU.ChebotarevFrobeniusInput`.** -/
theorem chebotarevFrobeniusInput_of_density (h : ChebotarevDensity) :
    NK.WeakNU.ChebotarevFrobeniusInput := by
  classical
  intro N _ _ _ _ σ T
  -- the Čebotarev density of the Frobenius set of `σ` over `ℚ`
  have hd : NumberField.Set.HasDirichletDensity (frobSet (K := ℚ) (N := N) σ)
      (frobDensity (K := ℚ) (N := N) σ) := h ℚ N σ
  have hpos : 0 < frobDensity (K := ℚ) (N := N) σ := frobDensity_pos σ
  -- discard the ramified primes
  have hdiff : ((frobSet (K := ℚ) (N := N) σ \
        (frobSet (K := ℚ) (N := N) σ ∩ {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭})) ∪
      ((frobSet (K := ℚ) (N := N) σ ∩ {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭}) \
        frobSet (K := ℚ) (N := N) σ)).Finite := by
    refine (finite_setOf_not_isUnramified (K := ℚ) (N := N)).subset ?_
    rintro 𝔭 (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact fun hU => h2 ⟨h1, hU⟩
    · exact absurd h1.1 h2
  have hdU : NumberField.Set.HasDirichletDensity
      (frobSet (K := ℚ) (N := N) σ ∩ {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭})
      (frobDensity (K := ℚ) (N := N) σ) :=
    HasDirichletDensitySensitivity (S := frobSet (K := ℚ) (N := N) σ) hdiff hd
  have hinf : (frobSet (K := ℚ) (N := N) σ ∩
      {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭}).Infinite :=
    NK.Chebotarev.infinite_of_hasDirichletDensity_pos hdU hpos
  -- pass to rational primes
  have hPinf : (ratPrimeOf '' (frobSet (K := ℚ) (N := N) σ ∩
      {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭})).Infinite :=
    Set.Infinite.image (fun _ _ _ _ hxy => ratPrimeOf_injective hxy) hinf
  have hnotT : ∃ 𝔭 ∈ (frobSet (K := ℚ) (N := N) σ ∩
      {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭}), ratPrimeOf 𝔭 ∉ (T : Set ℕ) := by
    obtain ⟨q, hqimg, hqT⟩ := (hPinf.sdiff T.finite_toSet).nonempty
    obtain ⟨𝔮, h𝔮mem, h𝔮q⟩ := hqimg
    exact ⟨𝔮, h𝔮mem, by rwa [← h𝔮q] at hqT⟩
  obtain ⟨𝔭, h𝔭mem, h𝔭T⟩ := hnotT
  refine ⟨ratPrimeOf 𝔭, ratPrimeOf_prime 𝔭, h𝔭T, ?_, ?_⟩
  · intro P hP
    exact h𝔭mem.2 P ((liesOver_span_ratPrimeOf_iff 𝔭 P).mp hP)
  · obtain ⟨P, hP, hσ⟩ := h𝔭mem.1
    exact ⟨P, (liesOver_span_ratPrimeOf_iff 𝔭 P).mpr hP, hσ⟩

end

end NK.ChebotarevGeneral
