import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Submission.Work.SSGRoute.dvd_discr_of_isRamifiedIn
import Submission.Work.SSGRoute.placePrime_eq_of_val_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the relevant ramified places of `ℚ̄`

For a finite Galois extension `Λ/ℚ` and a prime `p`, only finitely many conjugacy classes of finite
places of `ℚ̄` are ramified in `Λ` or lie over `p`.  The representatives are chosen as the places
over the (finitely many) primes dividing `disc(Λ)` or equal to `p`, using the local correspondence
`Submission.NeukirchUchida.placeOver` and the transitivity of the Galois action on the places over
a fixed prime.
-/

open SSGRoute
open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute

theorem ramifiedPlaces_finite (p : ℕ) [Fact p.Prime] (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ] :
    ∃ S : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B) ∧
      ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  have hd : (NumberField.discr Λ).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero Λ)
  -- the finite set of primes of `ℤ` that are relevant
  let Q : Finset Nat.Primes :=
    (insert p (NumberField.discr Λ).natAbs.primeFactors).attach.image
      (fun q => ⟨q.1, (by
        rcases Finset.mem_insert.mp q.2 with h | h
        · rw [h]; exact Fact.out
        · exact Nat.prime_of_mem_primeFactors h)⟩)
  -- one place of `ℚ̄` over each of them
  let f : Nat.Primes → ValuationSubring SSGRoute.QBar := fun q =>
    (Submission.NeukirchUchida.placeOver (K₁ := ℚ) (K₁' := SSGRoute.QBar)
      ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q)).1
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 : (f q).comap (algebraMap ℚ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
          ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q) :=
      Submission.NeukirchUchida.placeOver_spec _
    have h2 : (f q').comap (algebraMap ℚ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
          ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q') :=
      Submission.NeukirchUchida.placeOver_spec _
    refine (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm.injective ?_
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ℚ) (K := ℚ)
      (h1.symm.trans (by rw [h]) |>.trans h2)
  refine ⟨Q.map ⟨f, hinj⟩, ?_, ?_, ?_⟩
  · -- every element is a finite place
    intro A hA
    rw [Finset.mem_map] at hA
    obtain ⟨q, -, rfl⟩ := hA
    show (f q).comap (algebraMap ℚ SSGRoute.QBar) ≠ ⊤
    rw [show f q = (Submission.NeukirchUchida.placeOver (K₁ := ℚ) (K₁' := SSGRoute.QBar)
      ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q)).1 from rfl,
      Submission.NeukirchUchida.placeOver_spec]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _
  · -- pairwise non-conjugate
    intro A hA B hB hconj
    rw [Finset.mem_map] at hA hB
    obtain ⟨q, -, rfl⟩ := hA
    obtain ⟨q', -, rfl⟩ := hB
    obtain ⟨σ, hσ⟩ := hconj
    have hσ' : σ • f q = f q' := hσ
    have hcomap : (f q).comap (algebraMap ℚ SSGRoute.QBar) =
        (f q').comap (algebraMap ℚ SSGRoute.QBar) := by
      rw [← hσ']
      exact (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap (f q) σ).symm
    have h1 : (f q).comap (algebraMap ℚ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
          ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q) :=
      Submission.NeukirchUchida.placeOver_spec _
    have h2 : (f q').comap (algebraMap ℚ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
          ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q') :=
      Submission.NeukirchUchida.placeOver_spec _
    have hqq : q = q' := (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm.injective
      (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (R := NumberField.RingOfIntegers ℚ) (K := ℚ)
        (h1.symm.trans (hcomap.trans h2)))
    rw [hqq]
  · -- every relevant place is conjugate to one in the set
    intro B hB hrel
    have hqmem : placePrime B hB ∈ Q := by
      rcases hrel with hram | hval
      · have hdvd := dvd_discr_of_isRamifiedIn Λ B hB hram
        have hmem : (placePrime B hB).1 ∈
            insert p (NumberField.discr Λ).natAbs.primeFactors :=
          Finset.mem_insert.mpr (Or.inr (Nat.mem_primeFactors.mpr
            ⟨(placePrime B hB).2, hdvd, hd⟩))
        exact Finset.mem_image.mpr ⟨⟨(placePrime B hB).1, hmem⟩, Finset.mem_attach _ _, rfl⟩
      · have hq : placePrime B hB = ⟨p, Fact.out⟩ := placePrime_eq_of_val_lt_one p B hB hval
        have hmem : (placePrime B hB).1 ∈
            insert p (NumberField.discr Λ).natAbs.primeFactors := by
          rw [hq]; exact Finset.mem_insert_self _ _
        exact Finset.mem_image.mpr ⟨⟨(placePrime B hB).1, hmem⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨f (placePrime B hB), Finset.mem_map.mpr ⟨placePrime B hB, hqmem, rfl⟩, ?_⟩
    have h1 : (f (placePrime B hB)).comap (algebraMap ℚ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
          ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
            (placePrime B hB)) :=
      Submission.NeukirchUchida.placeOver_spec _
    have h2 : (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
        (placePrime B hB) = Submission.NeukirchUchida.primeOf B hB := by
      rw [Work.SSGRoute.placePrime]
      exact (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm_apply_apply _
    have hAfin : (f (placePrime B hB)).comap (algebraMap ℚ SSGRoute.QBar) ≠ ⊤ := by
      rw [h1]
      exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _
    have h3 : (f (placePrime B hB)).comap (algebraMap ℚ SSGRoute.QBar) =
        B.comap (algebraMap ℚ SSGRoute.QBar) := by
      rw [h1, h2, ← Submission.NeukirchUchida.primeOf_spec B hB]
    exact Submission.NeukirchUchida.exists_smul_eq_of_comap_eq' hAfin h3

end Work.SSGRoute
