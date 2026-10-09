import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PT.vanishingInertia_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place set `S' = S ∪ Ram(N|k)` of the induction step of Schmidt--Wingberg §4

This file proves `Work.SSGRoute.ZConstruction.exists_finset_ramifiedPlaces`.  The enlargement
`S ↦ S'` of a finite set of pairwise non-conjugate finite places is built from a finite set
`P` of primes of `𝓞 k`, namely

* the primes of `𝓞 k` below the places of `S` (`PS`),
* the finitely many primes of `𝓞 k` over which some prime of `N` ramifies (`Pram`, obtained
  from `Work.SSGRoute.PT.ramifiedPlaces_finite_k_aux`),
* the finitely many primes of `𝓞 k` above `p` (`PpSpec`, via
  `IsDedekindDomain.primesOverFinset`);

the places of `S'` are the representatives `placeOver q` (`q ∈ P`) of the local
correspondence, and the facts that they are pairwise non-conjugate and that they cover every
finite place whose prime of `𝓞 k` lies in `P` are `places_of_primes_gen` below.
-/

namespace Work.SSGRoute.ZConstruction

/-- **The prime of `𝓞 k` below a finite place of `Ω` described by a valuation inequality.**

General-number-field form of `Work.SSGRoute.primeOf_mem_asIdeal_iff_k`: for `x ∈ 𝓞 k` one has
`x ∈ primeOf B hB` if and only if the `B`-adic value of the image of `x` in `Ω` is `< 1`. -/
theorem mem_primeOf_asIdeal_iff_gen (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
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
  rw [h1, ← hspec, Work.SSGRoute.comap_valuation_lt_one_iff]
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers k) k Ω]

/-- **A prime ideal containing a rational prime lies over it** (general form of the
corresponding statement of `Work.SSGRoute.ramifiedPlaces_finite_over_K`). -/
theorem liesOver_span_of_natPrime_mem_gen {R : Type*} [CommRing R] [Algebra ℤ R]
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

/-- **A finite place of `Ω` over `k` with `B.valuation (p : Ω) < 1` lies over the prime `(p)`.**

General-number-field form of `Work.SSGRoute.primeOf_liesOver_span_of_val_lt_one`. -/
theorem primeBelow_val_lt_one_gen (p : ℕ) (hp : p.Prime) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (B : ValuationSubring Ω)
    (hB : SSGRoute.IsFinPlace k B) (hval : B.valuation (p : Ω) < 1) :
    (Submission.NeukirchUchida.primeOf B hB).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine liesOver_span_of_natPrime_mem_gen (Submission.NeukirchUchida.primeOf B hB) p hp ?_
  rw [mem_primeOf_asIdeal_iff_gen k Ω B hB]
  simpa using hval

/-- **The places of `Ω` over a finite set of primes of `𝓞 k`, as a finite set of pairwise
non-conjugate representatives.**

Let `k` be a number field, `Ω/k` a separable closure and `P` a finite set of primes of `𝓞 k`.
Then there is a finite set `S` of pairwise non-conjugate finite places of `Ω` such that every
finite place `B` of `Ω` over `k` whose prime of `𝓞 k` below it belongs to `P` is `k`-conjugate to
an element of `S`.  The representatives are the places `placeOver q` for `q ∈ P`. -/
theorem places_of_primes_gen (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω]
    (P : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))) :
    ∃ S : Finset (ValuationSubring Ω),
      (∀ A ∈ S, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) ∧
      (∀ (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B),
        Submission.NeukirchUchida.primeOf B hB ∈ P → ∃ A ∈ S, SSGRoute.IsConjPlace k A B) := by
  classical
  refine ⟨P.image (fun q => (Submission.NeukirchUchida.placeOver
      (K₁ := k) (K₁' := Ω) q).1), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hA
    exact (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) q).2
  · intro A hA B hB hconj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨σ, hσ⟩ := hconj
    have hcomap : (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) q).1.comap
          (algebraMap k Ω) =
        (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) q').1.comap
          (algebraMap k Ω) := by
      rw [← hσ]
      exact (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap
        (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω) q).1 σ).symm
    rw [Submission.NeukirchUchida.placeOver_spec,
      Submission.NeukirchUchida.placeOver_spec] at hcomap
    obtain rfl : q = q' :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective hcomap
    rfl
  · intro B hBfin hmem
    refine ⟨(Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω)
      (Submission.NeukirchUchida.primeOf B hBfin)).1, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨Submission.NeukirchUchida.primeOf B hBfin, hmem, rfl⟩
    · refine Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'
        (Submission.NeukirchUchida.placeOver (K₁ := k) (K₁' := Ω)
          (Submission.NeukirchUchida.primeOf B hBfin)).2 ?_
      rw [Submission.NeukirchUchida.placeOver_spec,
        Submission.NeukirchUchida.primeOf_spec B hBfin]

/-- **The place set `S' = S ∪ Ram(N|k)` of the induction step of Schmidt--Wingberg §4.**

For a finite Galois `N` over the number field `k`, a prime `p` and a finite set `S` of pairwise
non-conjugate finite places of an algebraic closure `Ω` of `k`, there is a finite set `S' ⊇ cs(S)`
of pairwise non-conjugate finite places containing, up to conjugacy, every place ramified in `N`
and every place over `p`.  This is the enlargement of the place set `S ↦ S'` used by the induction
step of `Work.SSGRoute.hasZData_sum_of_level_data`: the places of `cs(S') ∖ cs(S)` are exactly the
places over `Ram(N|k) ∖ S|_k`.

The intended proof: `Work.LocalFields.finite_ramified_primes_extension` (finitely many primes of
`k` ramify in `N`, general `k`), `Submission.NeukirchUchida.placeOver` (a place of `Ω` over a given
prime of `𝓞 k`), and the bridge between `SSGRoute.IsRamifiedIn k N B` (inertia formulation) and
`¬ Work.LocalFields.IsUnramifiedAt k w` for the prime `w` of `𝓞 N` below `B`. -/
theorem exists_finset_ramifiedPlaces (p : ℕ) (hp : p.Prime)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) :
    ∃ S' : Finset (ValuationSubring Ω),
      (∀ A ∈ S', SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) ∧
      (∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∃ A' ∈ S', SSGRoute.IsConjPlace k A' B) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S', SSGRoute.IsConjPlace k A B) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hSep : IsSepClosure k Ω := inferInstance
  -- (1) the finitely many primes of `𝓞 k` below a place of `Ω` ramified in `N`
  obtain ⟨Sram, hSramfin, -, hSramcov⟩ := Work.SSGRoute.PT.ramifiedPlaces_finite_k_aux k Ω N
  let Pram : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
    Sram.attach.image (fun (A : ↥Sram) => Submission.NeukirchUchida.primeOf
      (K₁ := k) (K₁' := Ω) A.1 (hSramfin A.1 A.2))
  -- (2) the finitely many primes of `𝓞 k` above `p`
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by simp [hp.ne_zero]
  let Pp : Finset (Ideal (NumberField.RingOfIntegers k)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers k)
  have hPpdata : ∀ Q ∈ Pp, Q.IsPrime ∧ Q ≠ ⊥ := by
    intro Q hQ
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ
    exact ⟨hmem.1, Ideal.ne_bot_of_mem_primesOver hp0 hmem⟩
  let PpSpec : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
    Pp.attach.image (fun Q => ⟨Q.1, (hPpdata Q.1 Q.2).1, (hPpdata Q.1 Q.2).2⟩)
  -- (3) the primes of `𝓞 k` below the places of `S`
  let PS : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
    S.attach.image (fun (A : ↥S) => Submission.NeukirchUchida.primeOf
      (K₁ := k) (K₁' := Ω) A.1 (hSfin A.1 A.2))
  let P : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
    (Pram ∪ PS) ∪ PpSpec
  obtain ⟨S', hS'fin, hS'disj, hS'cov⟩ := places_of_primes_gen k Ω P
  refine ⟨S', hS'fin, hS'disj, ?_, ?_⟩
  · -- every place of `S` is `k`-conjugate to an element of `S'`
    rintro B ⟨A, hA, hc⟩
    have hAfin : SSGRoute.IsFinPlace k A := hSfin A hA
    obtain ⟨σ, hσ⟩ := hc
    have hcomapAB : B.comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
      rw [← hσ, Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap]
    have hBfin : SSGRoute.IsFinPlace k B := by
      unfold SSGRoute.IsFinPlace
      rw [hcomapAB]
      exact hAfin
    have hmemP : Submission.NeukirchUchida.primeOf B hBfin ∈ P := by
      have h2 : Submission.NeukirchUchida.primeOf B hBfin =
          Submission.NeukirchUchida.primeOf A hAfin :=
        Submission.NeukirchUchida.primeOf_eq_of_comap_eq hBfin hAfin hcomapAB
      rw [h2]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩))))
    exact hS'cov B hBfin hmemP
  · -- every place ramified in `N` or above `p` is `k`-conjugate to an element of `S'`
    intro B hBfin hrel
    have hmemP : Submission.NeukirchUchida.primeOf B hBfin ∈ P := by
      rcases hrel with hram | hval
      · obtain ⟨A, hA, hc⟩ := hSramcov B hBfin hram
        have hAfin : SSGRoute.IsFinPlace k A := hSramfin A hA
        obtain ⟨σ, hσ⟩ := hc
        have hcomapAB : B.comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
          rw [← hσ, Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap]
        have h2 : Submission.NeukirchUchida.primeOf B hBfin =
            Submission.NeukirchUchida.primeOf A hAfin :=
          Submission.NeukirchUchida.primeOf_eq_of_comap_eq hBfin hAfin hcomapAB
        rw [h2]
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩))))
      · have hlies : (Submission.NeukirchUchida.primeOf B hBfin).asIdeal.LiesOver
            (Ideal.span {(p : ℤ)}) := primeBelow_val_lt_one_gen p hp k Ω B hBfin hval
        have hmemPp : (Submission.NeukirchUchida.primeOf B hBfin).asIdeal ∈ Pp :=
          (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr
            ⟨(Submission.NeukirchUchida.primeOf B hBfin).isPrime, hlies⟩
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨⟨_, hmemPp⟩,
          Finset.mem_attach _ _, rfl⟩))
    exact hS'cov B hBfin hmemP

end Work.SSGRoute.ZConstruction
