import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary material for `Work.SSGRoute.ramifiedPlaces_finite`

Plumbing used in the proof that the finite places of `ℚ̄` that are ramified in a finite Galois
extension `Λ/ℚ`, or that lie over `p`, form finitely many conjugacy classes.
-/

open SSGRoute
open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute

instance (priority := 100) instIsAlgClosureQBarAux : IsAlgClosure ℚ SSGRoute.QBar :=
  AlgebraicClosure.instIsAlgClosure ℚ

instance (priority := 100) instIsSepClosureQBarAux : IsSepClosure ℚ SSGRoute.QBar :=
  IsSepClosure.of_isAlgClosure_of_perfectField ℚ SSGRoute.QBar

/-- **The rational prime below a finite place of `ℚ̄`.** -/
noncomputable def placePrime (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B) :
    Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (Submission.NeukirchUchida.primeOf B hB)

/-- A place of `ℚ̄` over a finite prime of `ℚ` restricts to a proper place of every intermediate
field. -/
theorem comap_level_ne_top' (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B)
    (Λ : IntermediateField ℚ SSGRoute.QBar) :
    B.comap (algebraMap Λ SSGRoute.QBar) ≠ ⊤ :=
  NK.Reconstruct.comap_level_ne_top hB Λ

/-- **Comparison of the `(-).valuation (·) < 1` condition along a `comap`.** -/
theorem comap_valuation_lt_one_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (B : ValuationSubring L) (x : K) :
    (B.comap (algebraMap K L)).valuation x < 1 ↔ B.valuation (algebraMap K L x) < 1 := by
  have hsub : (B.comap (algebraMap K L)).valuation.valuationSubring =
      (B.valuation.comap (algebraMap K L)).valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext y
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
  have heq : (B.comap (algebraMap K L)).valuation.IsEquiv
      (B.valuation.comap (algebraMap K L)) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  rw [Valuation.IsEquiv.lt_one_iff_lt_one heq]
  rfl

/-- The ring of integers of a finite intermediate field is contained in every finite place of `ℚ̄`
above `ℚ`. -/
theorem ringOfIntegers_mem_of_isFinPlace (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ]
    (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B)
    (x : NumberField.RingOfIntegers Λ) :
    algebraMap (NumberField.RingOfIntegers Λ) SSGRoute.QBar x ∈ B := by
  have hA : B.comap (algebraMap Λ SSGRoute.QBar) ≠ ⊤ := comap_level_ne_top' B hB Λ
  have h1 := Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
    (B.comap (algebraMap Λ SSGRoute.QBar)) hA x
  rw [ValuationSubring.mem_comap] at h1
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers Λ) Λ SSGRoute.QBar]
  exact h1

/-- **The prime of `𝓞 Λ` below a finite place of `ℚ̄` lies over the prime of `𝓞 ℚ` below it.** -/
theorem primeOfLevel_liesOver' (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ]
    (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B) :
    (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf B hB).asIdeal := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers Λ) :=
    NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ) with hP
  set q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Submission.NeukirchUchida.primeOf B hB with hq
  have hspecP : B.comap (algebraMap Λ SSGRoute.QBar) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P :=
    NK.Reconstruct.primeOfLevel_spec B Λ (comap_level_ne_top' B hB Λ)
  have hspecQ : B.comap (algebraMap ℚ SSGRoute.QBar) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ q :=
    Submission.NeukirchUchida.primeOf_spec B hB
  set qu : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P with hqu
  have hqu_ideal : qu.asIdeal = P.asIdeal.under (NumberField.RingOfIntegers ℚ) := rfl
  have hcomap : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P).comap
        (algebraMap ℚ Λ) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ qu :=
    Commons.RingTheory.Valuation.comap_valuationSubringAtPrime qu P ⟨hqu_ideal⟩
  have hcomap2 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P).comap
        (algebraMap ℚ Λ) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ q := by
    rw [← hspecP, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq ℚ Λ SSGRoute.QBar]
    exact hspecQ
  have hquq : qu = q :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (hcomap.symm.trans hcomap2)
  refine ⟨?_⟩
  show q.asIdeal = P.asIdeal.under (NumberField.RingOfIntegers ℚ)
  rw [← hquq]
  exact hqu_ideal

/-- **Description of the prime below a finite place by a valuation inequality.** -/
theorem primeOfLevel_mem_iff (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ]
    (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B)
    (x : NumberField.RingOfIntegers Λ) :
    x ∈ (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal ↔
      B.valuation (algebraMap (NumberField.RingOfIntegers Λ) SSGRoute.QBar x) < 1 := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers Λ) :=
    NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ) with hPdef
  have hspec : B.comap (algebraMap Λ SSGRoute.QBar) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P :=
    NK.Reconstruct.primeOfLevel_spec B Λ (comap_level_ne_top' B hB Λ)
  show x ∈ P.asIdeal ↔ _
  haveI : IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P) P.asIdeal :=
    inferInstanceAs (IsLocalization P.asIdeal.primeCompl _)
  have h1 : x ∈ P.asIdeal ↔
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P).valuation
        (algebraMap (NumberField.RingOfIntegers Λ) Λ x) < 1 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Λ P) P.asIdeal x]
    exact ValuationSubring.valuation_lt_one_iff _ _
  rw [h1, ← hspec, comap_valuation_lt_one_iff]
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers Λ) Λ SSGRoute.QBar]


/-- **The image of an element of `𝓞 Λ` under a restricted automorphism.** -/
theorem restrictNormalHom_smul_coe (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ]
    [hN : Normal ℚ Λ] (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)
    (x : NumberField.RingOfIntegers Λ) :
    ((AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ • x :
        NumberField.RingOfIntegers Λ) : SSGRoute.QBar) = σ (x : SSGRoute.QBar) := by
  have h1 : ((AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ • x :
        NumberField.RingOfIntegers Λ) : Λ)
      = (AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ) (x : Λ) := rfl
  rw [h1]
  rw [show (AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ) (x : Λ)
      = AlgEquiv.restrictNormal σ Λ (x : Λ) from rfl]
  exact @AlgEquiv.restrictNormal_apply ℚ _ SSGRoute.QBar _ _ Λ hN σ (x : Λ)

/-- **The inertia condition passes to the prime below.**  If `σ` acts trivially on the residue
field of the finite place `B` of `ℚ̄`, then its restriction to `Λ` lies in the inertia subgroup of
the prime of `𝓞 Λ` below `B`. -/
theorem mem_inertia_of_isInertia (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ]
    [hN : Normal ℚ Λ] (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B)
    {σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar} (hσ : SSGRoute.IsInertia ℚ B σ) :
    AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ ∈
      Ideal.inertia (Λ ≃ₐ[ℚ] Λ)
        (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal := by
  rw [AddSubgroup.mem_inertia]
  intro x
  change (AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ • x - x) ∈
    (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal
  rw [primeOfLevel_mem_iff Λ B hB]
  have h2 : algebraMap (NumberField.RingOfIntegers Λ) SSGRoute.QBar
      (AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ • x)
      = σ (x : SSGRoute.QBar) := by
    change ((AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ • x :
      NumberField.RingOfIntegers Λ) : SSGRoute.QBar) = σ (x : SSGRoute.QBar)
    exact restrictNormalHom_smul_coe Λ σ x
  rw [map_sub, h2]
  exact hσ.2 _ (ringOfIntegers_mem_of_isFinPlace Λ B hB x)


/-- **A rational prime that ramifies in `Λ` divides the discriminant of `Λ`.**  (Fallback proof,
kept alongside the auxiliary lemmas; a separate module states the same result for the main file.) -/
theorem dvd_discr_of_isRamifiedIn_aux (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ] (B : ValuationSubring SSGRoute.QBar)
    (hB : SSGRoute.IsFinPlace ℚ B) (h : SSGRoute.IsRamifiedIn ℚ Λ B) :
    (placePrime B hB).1 ∣ (NumberField.discr Λ).natAbs := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  haveI hN : Normal ℚ Λ := (inferInstance : IsGalois ℚ Λ).to_normal
  set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers Λ) :=
    NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ) with hP
  set q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Submission.NeukirchUchida.primeOf B hB with hq
  have hlie : P.asIdeal.LiesOver q.asIdeal := primeOfLevel_liesOver' Λ B hB
  haveI : P.asIdeal.LiesOver q.asIdeal := hlie
  have hram : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) ≠ 1 := by
    obtain ⟨σ, hσin, hσfix⟩ := h
    have hg : AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ ∈
        Ideal.inertia (Λ ≃ₐ[ℚ] Λ) P.asIdeal := mem_inertia_of_isInertia Λ B hB hσin
    have hg1 : AlgEquiv.restrictNormalHom Λ (F := ℚ) (K₁ := SSGRoute.QBar) σ ≠ 1 := by
      intro h1
      have h1' : AlgEquiv.restrictNormal σ Λ = 1 := h1
      have h2 := @AlgEquiv.restrictNormal_eq_one_iff ℚ _ SSGRoute.QBar _ _ Λ hN σ
      exact hσfix (by rw [IntermediateField.mem_fixingSubgroup_iff]; exact h2.mp h1')
    intro h1
    have hbot : Ideal.inertia (Λ ≃ₐ[ℚ] Λ) P.asIdeal = ⊥ :=
      (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
        q.asIdeal P.asIdeal).mpr h1
    rw [hbot] at hg
    exact hg1 (Subgroup.mem_bot.mp hg)
  have hnotunr : ¬ Algebra.IsUnramifiedAt ℤ P.asIdeal := by
    intro hU
    have hU' : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers ℚ) P.asIdeal :=
      Algebra.IsUnramifiedAt.of_restrictScalars ℤ P.asIdeal
    exact hram (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R := NumberField.RingOfIntegers ℚ) (S := NumberField.RingOfIntegers Λ))
  have hmem : ((placePrime B hB).1 : NumberField.RingOfIntegers Λ) ∈ P.asIdeal := by
    have hmemq : ((placePrime B hB).1 : NumberField.RingOfIntegers ℚ) ∈ q.asIdeal := by
      refine Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq q (placePrime B hB).1
        (placePrime B hB).2 ?_
      show Rat.HeightOneSpectrum.primesEquiv q =
        ⟨(placePrime B hB).1, (placePrime B hB).2⟩
      rw [show Rat.HeightOneSpectrum.primesEquiv q = placePrime B hB from rfl]
      exact Subtype.ext rfl
    have := (Ideal.mem_of_liesOver (P := P.asIdeal) (p := q.asIdeal)
      (placePrime B hB).1).mp hmemq
    rwa [map_natCast] at this
  have hdivZ : ((placePrime B hB).1 : ℤ) ∣ NumberField.discr Λ := by
    by_contra hcon
    rw [NumberField.not_dvd_discr_iff_forall_mem Λ (NumberField.RingOfIntegers Λ)
      (Nat.prime_iff_prime_int.mp (placePrime B hB).2)] at hcon
    exact hnotunr (hcon P.asIdeal P.isPrime hmem)
  simpa using (Int.natAbs_dvd_natAbs (a := ((placePrime B hB).1 : ℤ))
    (b := NumberField.discr Λ)).mpr hdivZ

end Work.SSGRoute
