import Mathlib
import Submission.Work.SSGRoute.overK
import Submission.Work.SSGRoute.ramifiedPlaces_finite
import Submission.Work.SSGRoute.local_transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the ramified places of `ℚ̄` over a number field `K`

This is the `↥K`-form of `Work.SSGRoute.ramifiedPlaces_finite`: for a finite Galois extension
`N/ℚ` and a subfield `K ≤ N`, only finitely many `Gal(ℚ̄/K)`-classes of finite places of `ℚ̄`
are ramified in `N/K` or lie over the prime `p`.

## The mathematical content

For a finite place `B` of `ℚ̄` over `K` (i.e. `B.comap (algebraMap ↥K ℚ̄) ≠ ⊤`), the
`Gal(ℚ̄/K)`-conjugacy class of `B` is determined by the prime `𝔭 = primeOf B hB` of `𝓞 K` below it
(`isConjPlace_over_K_iff_comap_eq`, `Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'`).
Hence it suffices to exhibit a *finite* set of primes of `𝓞 K` containing the prime below every
relevant `B`.  Those primes are

* the primes above `p` (finitely many, since `p ≠ 0`), and
* the primes ramified in `N/K`, which are among the primes above the rational primes dividing
  the (absolute) discriminant `disc(N)` -- because ramification in `N/K` implies ramification in
  `N/ℚ` (`local_transport_isRamifiedIn` plus `restrictScalars ℚ (overK K N hKN) = N`), and a
  ramified rational prime divides `disc(N)` (`Work.SSGRoute.dvd_discr_of_isRamifiedIn`).

So we take the primes of `𝓞 K` lying above the finite set `{p} ∪ primeFactors (disc N)`, i.e. the
finite set `IsDedekindDomain.primesOverFinset (ℓ)` for `ℓ` in that set, and choose one place over
each of them via `Submission.NeukirchUchida.placeOver`.

The two membership statements are `primeOf_liesOver_span_of_val_lt_one` (case "above `p`") and
`primeOf_liesOver_of_isRamifiedIn_overK` (case "ramified"), both using the description
`primeOf_mem_asIdeal_iff_k` of the prime below a place by a valuation inequality and the
"maximality" of the rational prime ideals in `ℤ`.
-/

open SSGRoute
open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **The `↥K`-classes of finite places are the traces on `↥K`.**

For a finite place `A` of `ℚ̄` over `↥K`, a place `B` is `Gal(ℚ̄/↥K)`-conjugate to `A` precisely
when it has the same restriction to `K`.  This is the `↥K`-form of
`Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'` together with
`Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap`. -/
theorem isConjPlace_over_K_iff_comap_eq (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K]
    (A B : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ↥K A) :
    SSGRoute.IsConjPlace ↥K A B ↔
      A.comap (algebraMap ↥K SSGRoute.QBar) = B.comap (algebraMap ↥K SSGRoute.QBar) := by
  haveI : NumberField ↥K := Work.SSGRoute.numberField_K K
  haveI : IsAlgClosure ↥K SSGRoute.QBar := Work.SSGRoute.isAlgClosure_qbar_over_K K
  haveI : IsSepClosure ↥K SSGRoute.QBar :=
    IsSepClosure.of_isAlgClosure_of_perfectField ↥K SSGRoute.QBar
  constructor
  · rintro ⟨σ, hσ⟩
    rw [← hσ]
    exact (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A σ).symm
  · intro h
    exact Submission.NeukirchUchida.exists_smul_eq_of_comap_eq' hA h

/-- **Description of the prime of `𝓞 k` below a finite place of `Ω` by a valuation inequality.**

Let `k` be a number field, `Ω/k` a separable closure of `k` and `B` a finite place of `Ω`.  Then
for `x ∈ 𝓞 k` one has `x ∈ primeOf B hB` if and only if the `B`-adic value of the image of `x`
in `Ω` is `< 1`.  This is the "level `k`" form of `Work.SSGRoute.primeOfLevel_mem_iff`. -/
theorem primeOf_mem_asIdeal_iff_k (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (x : NumberField.RingOfIntegers k) :
    x ∈ (Submission.NeukirchUchida.primeOf B hB).asIdeal ↔
      B.valuation (algebraMap (NumberField.RingOfIntegers k) Ω x) < 1 := by
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Submission.NeukirchUchida.primeOf B hB with hPdef
  have hspec : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P :=
    Submission.NeukirchUchida.primeOf_spec B hB
  show x ∈ P.asIdeal ↔ _
  haveI : IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P) P.asIdeal :=
    inferInstanceAs (IsLocalization P.asIdeal.primeCompl _)
  have h1 : x ∈ P.asIdeal ↔
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P).valuation
        (algebraMap (NumberField.RingOfIntegers k) k x) < 1 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P) P.asIdeal x]
    exact ValuationSubring.valuation_lt_one_iff _ _
  rw [h1, ← hspec, comap_valuation_lt_one_iff]
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers k) k Ω]

/-- **The prime below a place lies over the rational prime `ℓ`** whenever `ℓ ∈ P` is a rational
prime.  The only input is the maximality of the prime ideal `(ℓ) ⊆ ℤ`. -/
theorem liesOver_span_of_natPrime_mem {R : Type*} [CommRing R] [Algebra ℤ R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (h : ((ℓ : ℕ) : R) ∈ P.asIdeal) :
    P.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  rw [Ideal.liesOver_iff]
  have hmem : (ℓ : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    rw [Ideal.mem_under]
    simpa using h
  have hne : Ideal.under ℤ P.asIdeal ≠ ⊤ := by
    rw [Ideal.under_def]
    exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top P.isPrime)
  exact (Int.ideal_span_isMaximal_of_prime ℓ).eq_of_le hne
    ((Ideal.span_singleton_le_iff_mem _).mpr hmem)

/-- **A place above `p` has its `𝓞 K`-prime above `p`.** -/
theorem primeOf_liesOver_span_of_val_lt_one (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ↥K B)
    (hval : B.valuation (p : SSGRoute.QBar) < 1) :
    (Submission.NeukirchUchida.primeOf B hB).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI : NumberField ↥K := Work.SSGRoute.numberField_K K
  haveI : IsAlgClosure ↥K SSGRoute.QBar := Work.SSGRoute.isAlgClosure_qbar_over_K K
  haveI : IsSepClosure ↥K SSGRoute.QBar :=
    IsSepClosure.of_isAlgClosure_of_perfectField ↥K SSGRoute.QBar
  refine liesOver_span_of_natPrime_mem (Submission.NeukirchUchida.primeOf B hB) p Fact.out ?_
  rw [primeOf_mem_asIdeal_iff_k ↥K SSGRoute.QBar B hB]
  simpa using hval

/-- **The `𝓞 K`-prime of a place ramified in `N/K` lies above a rational prime dividing
`disc(N)`.** -/
theorem primeOf_liesOver_of_isRamifiedIn_overK
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [NumberField ↥K]
    [IsSepClosure ↥K SSGRoute.QBar]
    (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N] [IsGalois ℚ N]
    [NumberField ↥N]
    (hKN : K ≤ N) (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ↥K B)
    (hram : SSGRoute.IsRamifiedIn ↥K (overK K N hKN) B) :
    ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ℓ ∣ (NumberField.discr ↥N).natAbs ∧
      (Submission.NeukirchUchida.primeOf B hB).asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
  have hBℚ : SSGRoute.IsFinPlace ℚ B := (local_transport_isFinPlace K B).mp hB
  -- ramification over `↥K` implies ramification over `ℚ`
  obtain ⟨σ, _hσK, hσI, hσN⟩ := (local_transport_isRamifiedIn K (overK K N hKN) B).mp hram
  have hrestrict : IntermediateField.restrictScalars ℚ (overK K N hKN) = N := by
    ext x
    rw [IntermediateField.mem_restrictScalars]
    rfl
  have hramℚ : SSGRoute.IsRamifiedIn ℚ N B := by
    refine ⟨σ, hσI, ?_⟩
    rw [hrestrict] at hσN
    exact hσN
  -- hence the rational prime below `B` divides the discriminant of `N`
  have hdvd : (placePrime B hBℚ).1 ∣ (NumberField.discr ↥N).natAbs :=
    dvd_discr_of_isRamifiedIn N B hBℚ hramℚ
  refine ⟨(placePrime B hBℚ).1, (placePrime B hBℚ).2, hdvd, ?_⟩
  -- the rational prime already lands in `primeOf B hBℚ ⊆ 𝓞 ℚ`, then transports to `𝓞 K`
  have hℓmem : ((placePrime B hBℚ).1 : NumberField.RingOfIntegers ℚ) ∈
      (Submission.NeukirchUchida.primeOf B hBℚ).asIdeal := by
    refine Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq
      (Submission.NeukirchUchida.primeOf B hBℚ) (placePrime B hBℚ).1 (placePrime B hBℚ).2 ?_
    show Rat.HeightOneSpectrum.primesEquiv (Submission.NeukirchUchida.primeOf B hBℚ) =
      ⟨(placePrime B hBℚ).1, (placePrime B hBℚ).2⟩
    rw [show Rat.HeightOneSpectrum.primesEquiv (Submission.NeukirchUchida.primeOf B hBℚ)
      = placePrime B hBℚ from rfl]
    exact Subtype.ext rfl
  have hvalℚ : B.valuation ((placePrime B hBℚ).1 : SSGRoute.QBar) < 1 := by
    have h1 := (primeOf_mem_asIdeal_iff_k ℚ SSGRoute.QBar B hBℚ
      ((placePrime B hBℚ).1 : NumberField.RingOfIntegers ℚ)).mp hℓmem
    simpa using h1
  have hmemK : ((placePrime B hBℚ).1 : NumberField.RingOfIntegers ↥K) ∈
      (Submission.NeukirchUchida.primeOf B hB).asIdeal := by
    rw [primeOf_mem_asIdeal_iff_k ↥K SSGRoute.QBar B hB]
    simpa using hvalℚ
  exact liesOver_span_of_natPrime_mem (Submission.NeukirchUchida.primeOf B hB)
    (placePrime B hBℚ).1 (placePrime B hBℚ).2 hmemK

theorem ramifiedPlaces_finite_over_K (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N] [IsGalois ℚ N]
    (hKN : K ≤ N) :
    ∃ S : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ S, SSGRoute.IsFinPlace ↥K A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ↥K A B → A = B) ∧
      ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (SSGRoute.IsRamifiedIn ↥K (overK K N hKN) B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace ↥K A B := by
  classical
  haveI : NumberField ↥K := Work.SSGRoute.numberField_K K
  haveI : IsAlgClosure ↥K SSGRoute.QBar := Work.SSGRoute.isAlgClosure_qbar_over_K K
  haveI : IsSepClosure ↥K SSGRoute.QBar :=
    IsSepClosure.of_isAlgClosure_of_perfectField ↥K SSGRoute.QBar
  haveI : NumberField ↥N := NumberField.of_module_finite ℚ ↥N
  have hdisc : (NumberField.discr ↥N).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero ↥N)
  -- the finitely many relevant rational primes
  let Q : Finset ℕ := insert p (NumberField.discr ↥N).natAbs.primeFactors
  have hQprime : ∀ ℓ ∈ Q, Nat.Prime ℓ := by
    intro ℓ hℓ
    rcases Finset.mem_insert.mp hℓ with h | h
    · rw [h]; exact Fact.out
    · exact Nat.prime_of_mem_primeFactors h
  -- the primes of `𝓞 K` above them
  let Sprime : Finset (Ideal (NumberField.RingOfIntegers ↥K)) :=
    Q.biUnion (fun ℓ => IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)})
      (NumberField.RingOfIntegers ↥K))
  have hdata : ∀ P ∈ Sprime, P.IsPrime ∧ P ≠ ⊥ := by
    intro P hP
    obtain ⟨ℓ, hℓQ, hPℓ⟩ := Finset.mem_biUnion.mp hP
    have hℓ := hQprime ℓ hℓQ
    haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
    haveI : (Ideal.span {(ℓ : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
    have hpb : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      simp [hℓ.ne_zero]
    have hmem : P ∈ (Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers ↥K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff hpb _).mp hPℓ
    exact ⟨hmem.1, Ideal.ne_bot_of_mem_primesOver hpb hmem⟩
  -- one place of `ℚ̄` over each of these primes
  let place : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) →
      ValuationSubring SSGRoute.QBar :=
    fun q => (Submission.NeukirchUchida.placeOver (K₁ := ↥K) (K₁' := SSGRoute.QBar) q).1
  have hplace_fin : ∀ q, SSGRoute.IsFinPlace ↥K (place q) := fun q =>
    (Submission.NeukirchUchida.placeOver (K₁ := ↥K) (K₁' := SSGRoute.QBar) q).2
  have hplace_comap : ∀ q, (place q).comap (algebraMap ↥K SSGRoute.QBar) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q := fun q =>
    Submission.NeukirchUchida.placeOver_spec q
  let S : Finset (ValuationSubring SSGRoute.QBar) :=
    Sprime.attach.image (fun P => place ⟨P.1, (hdata P.1 P.2).1, (hdata P.1 P.2).2⟩)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hA
    exact hplace_fin _
  · intro A hA B hB hconj
    obtain ⟨PA, -, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨PB, -, rfl⟩ := Finset.mem_image.mp hB
    -- both places determine the same prime of `𝓞 K`, hence are equal
    have hcomap := (isConjPlace_over_K_iff_comap_eq K _ _
      (hplace_fin ⟨PA.1, (hdata PA.1 PA.2).1, (hdata PA.1 PA.2).2⟩)).mp hconj
    rw [hplace_comap ⟨PA.1, (hdata PA.1 PA.2).1, (hdata PA.1 PA.2).2⟩,
      hplace_comap ⟨PB.1, (hdata PB.1 PB.2).1, (hdata PB.1 PB.2).2⟩] at hcomap
    have heq : (⟨PA.1, (hdata PA.1 PA.2).1, (hdata PA.1 PA.2).2⟩ :
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) =
        ⟨PB.1, (hdata PB.1 PB.2).1, (hdata PB.1 PB.2).2⟩ :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K) hcomap
    rw [heq]
  · intro B hBfin hrel
    -- the prime of `𝓞 K` below `B` lies above an element of `Q`
    have hmemQ : ∃ ℓ ∈ Q, (Submission.NeukirchUchida.primeOf B hBfin).asIdeal ∈
        IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)})
          (NumberField.RingOfIntegers ↥K) := by
      rcases hrel with hram | hval
      · obtain ⟨ℓ, hℓprime, hℓdvd, hlies⟩ :=
          primeOf_liesOver_of_isRamifiedIn_overK p K N hKN B hBfin hram
        refine ⟨ℓ, ?_, ?_⟩
        · rw [Finset.mem_insert]
          exact Or.inr (Nat.mem_primeFactors.mpr ⟨hℓprime, hℓdvd, hdisc⟩)
        · haveI : Fact (Nat.Prime ℓ) := ⟨hℓprime⟩
          haveI : (Ideal.span {(ℓ : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
          have hpb : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
            simp [hℓprime.ne_zero]
          exact (IsDedekindDomain.mem_primesOverFinset_iff hpb _).mpr
            ⟨(Submission.NeukirchUchida.primeOf B hBfin).isPrime, hlies⟩
      · refine ⟨p, Finset.mem_insert_self p _, ?_⟩
        haveI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
        have hpb : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
          simp [(Fact.out : Nat.Prime p).ne_zero]
        exact (IsDedekindDomain.mem_primesOverFinset_iff hpb _).mpr
          ⟨(Submission.NeukirchUchida.primeOf B hBfin).isPrime,
            primeOf_liesOver_span_of_val_lt_one p K B hBfin hval⟩
    obtain ⟨ℓ, hℓQ, hPℓ⟩ := hmemQ
    have hPS : (Submission.NeukirchUchida.primeOf B hBfin).asIdeal ∈ Sprime :=
      Finset.mem_biUnion.mpr ⟨ℓ, hℓQ, hPℓ⟩
    -- the place over that prime is `Gal(ℚ̄/↥K)`-conjugate to `B`
    refine ⟨place ⟨(Submission.NeukirchUchida.primeOf B hBfin).asIdeal,
        (hdata _ hPS).1, (hdata _ hPS).2⟩,
      Finset.mem_image.mpr ⟨⟨(Submission.NeukirchUchida.primeOf B hBfin).asIdeal, hPS⟩,
        Finset.mem_attach _ _, rfl⟩, ?_⟩
    refine (isConjPlace_over_K_iff_comap_eq K _ B (hplace_fin _)).mpr ?_
    rw [hplace_comap _, Submission.NeukirchUchida.primeOf_spec B hBfin]

end Work.SSGRoute
