import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Submission.Work.LocalFields.finite_ramified_primes_extension
import Submission.Work.LocalFields.unramifiedAt_iff_inertia_eq_bot
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Ramified places divide the discriminant

If a finite place `B` of `ℚ̄` lies over the rational prime `p` and the extension `Λ/ℚ` (finite,
Galois) ramifies at `B`, then `p` divides the discriminant of `Λ`.

The mathematical content: the inertia group `I_B ≤ Gal(ℚ̄/ℚ)` of the place `B` surjects onto the
inertia group `I_P ≤ Gal(Λ/ℚ)` of the prime `P` of `𝓞 Λ` cut out by `B`.  A witness
`σ ∈ I_B \ Gal(ℚ̄/Λ)` (which is what `IsRamifiedIn` produces) therefore has nontrivial image
`σ|_Λ ∈ I_P`, so the prime `P` — which lies over `(p)` — is ramified over `ℚ`, and hence `p`
divides `disc(Λ)`.
-/

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section Helpers

variable (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ]

/-- The action of `Gal(Λ/ℚ)` on the ring of integers of `Λ` is compatible with the embedding
into `ℚ̄`: the embedding intertwines `σ` with the restriction of `σ` to `Λ`. -/
theorem algEquiv_smul_algebraMap_ringOfIntegers (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)
    (x : NumberField.RingOfIntegers Λ) :
    (algebraMap (NumberField.RingOfIntegers Λ) SSGRoute.QBar)
        (AlgEquiv.restrictNormalHom Λ σ • x)
      = σ (algebraMap (NumberField.RingOfIntegers Λ) SSGRoute.QBar x) := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥Λ) ↥Λ SSGRoute.QBar,
      IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥Λ) ↥Λ SSGRoute.QBar]
  rw [show (algebraMap (NumberField.RingOfIntegers ↥Λ) ↥Λ)
        (AlgEquiv.restrictNormalHom ↥Λ σ • x)
        = (AlgEquiv.restrictNormalHom ↥Λ σ) •
            (algebraMap (NumberField.RingOfIntegers ↥Λ) ↥Λ x) from rfl]
  rw [AlgEquiv.smul_def]
  exact AlgEquiv.restrictNormal_commutes σ ↥Λ
    (algebraMap (NumberField.RingOfIntegers ↥Λ) ↥Λ x)

/-- If `σ` lies in the inertia group of the place `B`, then its restriction to `Λ` lies in the
ideal-theoretic inertia group of the prime of `𝓞 Λ` cut out by `B`. -/
theorem restrictNormalHom_mem_inertia (B : ValuationSubring SSGRoute.QBar)
    (hB : SSGRoute.IsFinPlace ℚ B) (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)
    (hσ : SSGRoute.IsInertia ℚ B σ) :
    AlgEquiv.restrictNormalHom Λ σ ∈
      Ideal.inertia (Λ ≃ₐ[ℚ] Λ)
        (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  intro x
  change (AlgEquiv.restrictNormalHom Λ σ • x - x) ∈
    (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal
  rw [primeOfLevel_mem_iff Λ B hB, map_sub, algEquiv_smul_algebraMap_ringOfIntegers Λ σ x]
  exact hσ.2 _ (ringOfIntegers_mem_of_isFinPlace Λ B hB x)

/-- An element of `Gal(ℚ̄/ℚ)` which does not fix `Λ` pointwise restricts to a nontrivial element
of `Gal(Λ/ℚ)`. -/
theorem restrictNormalHom_ne_one (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)
    (h : σ ∉ Λ.fixingSubgroup) : AlgEquiv.restrictNormalHom Λ σ ≠ 1 := by
  intro h1
  apply h
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1' : σ.restrictNormal ↥Λ = 1 := h1
  have key := AlgEquiv.restrictNormal_commutes σ ↥Λ (⟨x, hx⟩ : ↥Λ)
  rw [h1'] at key
  exact key.symm

end Helpers

/-- The rational prime below a finite place of `ℚ̄` has value `< 1` at that place. -/
theorem placePrime_val_lt_one (B : ValuationSubring SSGRoute.QBar) (hB : SSGRoute.IsFinPlace ℚ B) :
    B.valuation ((placePrime B hB).1 : SSGRoute.QBar) < 1 := by
  set v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Submission.NeukirchUchida.primeOf B hB with hv
  have hgen : (placePrime B hB).1 = Rat.HeightOneSpectrum.natGenerator v := rfl
  rw [hgen]
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpad : Rat.padicValuation (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.natGenerator v : ℚ) < 1 := by
    rw [show (Rat.HeightOneSpectrum.natGenerator v : ℚ) =
      ((Rat.HeightOneSpectrum.natGenerator v : ℤ) : ℚ) by push_cast; ring]
    rw [Rat.padicValuation_cast, Int.padicValuation_lt_one_iff]
  have hvlt : v.valuation ℚ (Rat.HeightOneSpectrum.natGenerator v : ℚ) < 1 :=
    (Valuation.IsEquiv.lt_one_iff_lt_one
      (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v)).mpr hpad
  have heq : ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ v).valuation).IsEquiv
      (v.valuation ℚ) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr (by
      rw [ValuationSubring.valuationSubring_valuation,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring])
  have h1 : (B.comap (algebraMap ℚ SSGRoute.QBar)).valuation
      (Rat.HeightOneSpectrum.natGenerator v : ℚ) < 1 := by
    rw [show B.comap (algebraMap ℚ SSGRoute.QBar) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ v from
      Submission.NeukirchUchida.primeOf_spec B hB]
    exact (Valuation.IsEquiv.lt_one_iff_lt_one heq).mpr hvlt
  have h2 : B.valuation (algebraMap ℚ SSGRoute.QBar
      (Rat.HeightOneSpectrum.natGenerator v : ℚ)) < 1 :=
    (comap_valuation_lt_one_iff B (Rat.HeightOneSpectrum.natGenerator v : ℚ)).mp h1
  rwa [map_natCast] at h2

theorem dvd_discr_of_isRamifiedIn (Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ] (B : ValuationSubring SSGRoute.QBar)
    (hB : SSGRoute.IsFinPlace ℚ B) (h : SSGRoute.IsRamifiedIn ℚ Λ B) :
    (Work.SSGRoute.placePrime B hB).1 ∣ (NumberField.discr Λ).natAbs := by
  haveI : NumberField Λ := NumberField.of_module_finite ℚ Λ
  obtain ⟨σ, hσ, hσne⟩ := h
  -- the prime of `𝓞 Λ` determined by `B`
  have hmem : AlgEquiv.restrictNormalHom Λ σ ∈
      Ideal.inertia (Λ ≃ₐ[ℚ] Λ)
        (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal :=
    restrictNormalHom_mem_inertia Λ B hB σ hσ
  have hne : AlgEquiv.restrictNormalHom Λ σ ≠ 1 := restrictNormalHom_ne_one Λ σ hσne
  -- the inertia group of `P` is nontrivial
  have hI : Ideal.inertia (Λ ≃ₐ[ℚ] Λ)
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmem
    exact hne (Subgroup.mem_bot.mp hmem)
  -- hence `P` is ramified over `ℚ`
  have hunram : ¬ Work.LocalFields.IsUnramifiedAt ℚ
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)) := by
    rw [Work.LocalFields.unramifiedAt_iff_inertia_eq_bot (K := ℚ) (L := ↥Λ)]
    exact hI
  -- and therefore ramified over `ℤ`
  have hramZ : ¬ Algebra.IsUnramifiedAt ℤ
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal := by
    haveI : (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal.IsPrime :=
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).isPrime
    haveI : (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal.LiesOver
        (Submission.NeukirchUchida.primeOf B hB).asIdeal :=
      primeOfLevel_liesOver' Λ B hB
    exact Work.LocalFields.not_isUnramifiedAt_int_of_not_isUnramifiedAt (K := ℚ) (L := ↥Λ)
      (Submission.NeukirchUchida.primeOf B hB)
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)) hunram
  -- the prime `P` lies over `(p)`, i.e. contains `p`
  have hmemP : ((placePrime B hB).1 : NumberField.RingOfIntegers Λ) ∈
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).asIdeal := by
    rw [primeOfLevel_mem_iff Λ B hB]
    rw [show (algebraMap (NumberField.RingOfIntegers ↥Λ) SSGRoute.QBar)
          (Nat.cast (placePrime B hB).1) = (Nat.cast (placePrime B hB).1 : SSGRoute.QBar) from
      map_natCast _ _]
    exact placePrime_val_lt_one B hB
  -- conclude
  have hp : Prime ((placePrime B hB).1 : ℤ) :=
    Nat.prime_iff_prime_int.mp (placePrime B hB).2
  have hkey : ((placePrime B hB).1 : ℤ) ∣ NumberField.discr Λ := by
    by_contra hnd
    rw [NumberField.not_dvd_discr_iff_forall_mem Λ (NumberField.RingOfIntegers Λ) hp] at hnd
    refine hramZ (hnd (NK.Reconstruct.primeOfLevel B Λ
      (comap_level_ne_top' B hB Λ)).asIdeal
      (NK.Reconstruct.primeOfLevel B Λ (comap_level_ne_top' B hB Λ)).isPrime ?_)
    simpa only [Int.cast_natCast] using hmemP
  have hfin := (Int.natAbs_dvd_natAbs (a := ((placePrime B hB).1 : ℤ))
    (b := NumberField.discr Λ)).mpr hkey
  rwa [Int.natAbs_natCast] at hfin

end Work.SSGRoute
