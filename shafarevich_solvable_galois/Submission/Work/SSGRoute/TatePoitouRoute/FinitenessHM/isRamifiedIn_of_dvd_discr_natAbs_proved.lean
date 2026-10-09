import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.dvd_discr_of_isRamifiedIn
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZPlace
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.Work.SSGRoute.H2locAux.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise NumberField
open _root_.SSGRoute

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- A rational prime dividing the absolute discriminant of a number field is ramified at some finite place: the converse of `Work.SSGRoute.dvd_discr_of_isRamifiedIn` (and, unlike that sibling, without any Galois hypothesis on `K/ℚ`).  Together with Mathlib's `not_dvd_discr_iff_isUnramifiedIn` this pins the support of the discriminant to the ramified primes; it is the second arithmetic input of the Hermite–Minkowski discriminant bound (`Submission/Work/SSGRoute/Finiteness/NOTE_different_exponent_bound.md` §3).  Route: Mathlib's `NumberField.not_dvd_discr_iff_forall_mem` (contrapositive) gives a prime `P ∋ q` of `𝓞 K` that is *not* unramified; a place `B` of `ℚ̄` above `P` (e.g. via `RamifiedPlacesAux`/`NK.Reconstruct.PlaceCorrespondence`) has `B.valuation (q : ℚ̄) < 1` and nontrivial local inertia, i.e. `I_B ⊄ K.fixingSubgroup`. -/
theorem isRamifiedIn_of_dvd_discr_natAbs_proved (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] :
    haveI : NumberField K := NumberField.of_module_finite ℚ K
    ∀ (q : ℕ), q.Prime → q ∣ (NumberField.discr K).natAbs →
      ∃ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B ∧
        B.valuation (q : SSGRoute.QBar) < 1 ∧ SSGRoute.IsRamifiedIn ℚ K B := by
  haveI : NumberField K := NumberField.of_module_finite ℚ K
  haveI : NumberField ℚ := NumberField.of_module_finite ℚ ℚ
  intro q hq hdvd
  -- ## Step 1: a prime `P` of `𝓞 K` above `q` that is not unramified
  have hqZ : (q : ℤ) ∣ NumberField.discr K := by
    refine (Int.natAbs_dvd_natAbs (a := (q : ℤ)) (b := NumberField.discr K)).mp ?_
    simpa using hdvd
  have hpZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  obtain ⟨P, hPprime, hqP, hPnotunr⟩ : ∃ P : Ideal (𝓞 K), ∃ (hPr : P.IsPrime),
      ((q : ℤ) : 𝓞 K) ∈ P ∧ ¬ @Algebra.IsUnramifiedAt ℤ (𝓞 K) _ _ _ P hPr := by
    by_contra h
    push Not at h
    exact ((NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpZ).mpr
      (fun P hPr hmem => h P hPr hmem)) hqZ
  haveI : P.IsPrime := hPprime
  have hqK_ne : ((q : ℤ) : 𝓞 K) ≠ 0 := by
    simpa using (Int.cast_ne_zero (α := 𝓞 K)).mpr hpZ.ne_zero
  have hPne : P ≠ ⊥ := by
    intro hbot; rw [hbot] at hqP; exact hqK_ne (by simpa using hqP)
  let P₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hPprime, hPne⟩
  haveI : P₀.asIdeal.IsPrime := P₀.isPrime
  -- ## Step 2: the normal closure `Λ` of `K` and a place `A` of `ℚ̄` above `P`
  let Λ : IntermediateField ℚ SSGRoute.QBar := IntermediateField.normalClosure ℚ K SSGRoute.QBar
  haveI hΛfd : FiniteDimensional ℚ Λ := normalClosure.is_finiteDimensional ℚ K SSGRoute.QBar
  haveI hΛgal : IsGalois ℚ Λ := IsGalois.normalClosure ℚ K SSGRoute.QBar
  haveI hΛnf : NumberField Λ := NumberField.of_module_finite ℚ Λ
  have hKΛ : K ≤ Λ := IntermediateField.le_normalClosure K
  obtain ⟨A, hAspec⟩ :=
    NK.Reconstruct.exists_place_of_prime_level (k := ℚ) (K' := SSGRoute.QBar) K P₀
  haveI hA : SSGRoute.IsFinPlace ℚ A :=
    Work.SSGRoute.isFinPlace_of_comap_valuationSubringAtPrime K A P₀ hAspec
  -- ## Step 3: the ring tower `𝓞 K → 𝓞 Λ`
  letI : Algebra ↥K ↥Λ := (IntermediateField.inclusion hKΛ).toRingHom.toAlgebra
  haveI hST : IsScalarTower ℚ ↥K ↥Λ :=
    IsScalarTower.of_algebraMap_eq (fun x => (IntermediateField.inclusion hKΛ).commutes x)
  haveI : Module.Finite ↥K ↥Λ := Module.Finite.of_restrictScalars_finite ℚ ↥K ↥Λ
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 Λ)) := by
    intro x y h
    have h2 := congrArg (fun z : 𝓞 Λ => (z : ↥Λ)) h
    change algebraMap ↥K ↥Λ (x : ↥K) = algebraMap ↥K ↥Λ (y : ↥K) at h2
    have h3 := congrArg (fun z : ↥Λ => (z : SSGRoute.QBar)) h2
    change ((IntermediateField.inclusion hKΛ) (x : ↥K) : SSGRoute.QBar) =
      ((IntermediateField.inclusion hKΛ) (y : ↥K) : SSGRoute.QBar) at h3
    rw [IntermediateField.coe_inclusion, IntermediateField.coe_inclusion] at h3
    have h4 : (x : ↥K) = (y : ↥K) := Subtype.coe_injective h3
    exact NumberField.RingOfIntegers.coe_injective h4
  haveI : Module.IsTorsionFree (𝓞 K) (𝓞 Λ) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m h => by
      rw [Algebra.smul_def] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact Or.inl (hinj h1)
      · exact Or.inr h1)
  haveI : Module.Flat (𝓞 K) (𝓞 Λ) := inferInstance
  -- ## Step 4: the prime `P'` of `𝓞 Λ` below `A` lies over `P` and is ramified over `ℤ`
  set P' := Work.SSGRoute.levelPrime ℚ SSGRoute.QBar A hA Λ with hP'def
  haveI hP'p : P'.asIdeal.IsPrime := P'.isPrime
  have hspecP' : A.comap (algebraMap ↥Λ SSGRoute.QBar) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ P' := by
    rw [hP'def]
    exact NK.Reconstruct.primeOfLevel_spec A Λ (NK.Reconstruct.comap_level_ne_top hA Λ)
  have hquq : IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) P' = P₀ := by
    have h1 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ P').comap
        (algebraMap ↥K ↥Λ) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
          (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) P') :=
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime _ P'
        (Ideal.LiesOver.mk (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]))
    have h2 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Λ P').comap
        (algebraMap ↥K ↥Λ) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K P₀ := by
      rw [← hspecP', ValuationSubring.comap_comap A (algebraMap ↥Λ SSGRoute.QBar)
        (algebraMap ↥K ↥Λ)]
      have hcomp : (algebraMap ↥Λ SSGRoute.QBar).comp (algebraMap ↥K ↥Λ) =
          algebraMap ↥K SSGRoute.QBar := by
        ext x; rfl
      rw [hcomp, hAspec]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (h1.symm.trans h2)
  haveI hlies : P'.asIdeal.LiesOver P₀.asIdeal :=
    Ideal.LiesOver.mk (by rw [← hquq, IsDedekindDomain.HeightOneSpectrum.under_asIdeal])
  have hP'notunr : ¬ Algebra.IsUnramifiedAt ℤ P'.asIdeal := by
    intro hU
    haveI := hU
    exact hPnotunr (Algebra.IsUnramifiedAt.of_liesOver ℤ P₀.asIdeal P'.asIdeal)
  have hP'ram : P'.asIdeal.ramificationIdx ℤ ≠ 1 := by
    intro h1
    exact hP'notunr ((Ideal.ramificationIdx_eq_one_iff (R := ℤ) (S := 𝓞 Λ)
      (q := P'.asIdeal)).mp h1)
  -- ## Step 5: the inertia subgroup of the place `A` in `Gal(Λ/ℚ)` has cardinality `e(P'/ℚ)`
  have hcardΛ : Nat.card ↥(Ideal.inertia (↥Λ ≃ₐ[ℚ] ↥Λ) P'.asIdeal) =
      P'.asIdeal.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := ↥Λ ≃ₐ[ℚ] ↥Λ)
          (p := P'.asIdeal.under ℤ) (P := P'.asIdeal)]
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P'.asIdeal.under ℤ) P'.asIdeal (↥Λ ≃ₐ[ℚ] ↥Λ)]
  have himage := @Work.SSGRoute.inertiaSub_image_eq_levelInertia ℚ SSGRoute.QBar _ _ _ _ _ A hA Λ
    _ (inferInstance : Normal ℚ ↥Λ) _
  have hH : (Work.SSGRoute.inertiaSub ℚ SSGRoute.QBar A).map (AlgEquiv.restrictNormalHom ↥Λ) =
      Ideal.inertia (↥Λ ≃ₐ[ℚ] ↥Λ) P'.asIdeal := by
    rw [hP'def]
    exact himage
  -- ## Step 6: `A` ramifies in `K/ℚ`
  --
  -- If the inertia subgroup of `A` fixed `K` pointwise, then (with `Stab ≤ Gal(Λ/ℚ)` the subgroup
  -- fixing `K`) the level inertia of `Λ` over `K` would coincide with the level inertia of `Λ`
  -- over `ℚ`: both have the same cardinality by `subgroupOfEquivOfLe`.  Hence
  -- `e(P'/K) = e(P'/ℚ)`, and the tower formula `e(P'/ℚ) = e(P/ℚ) · e(P'/K)` forces `e(P/ℚ) = 1`,
  -- contradicting `hPnotunr`.
  have hramK : SSGRoute.IsRamifiedIn ℚ K A := by
    by_contra hcon
    have hle : Work.SSGRoute.inertiaSub ℚ SSGRoute.QBar A ≤ K.fixingSubgroup := by
      intro σ hσ
      by_contra hfix
      exact hcon ⟨σ, (Work.SSGRoute.mem_inertiaSub ℚ SSGRoute.QBar A σ).mp hσ, hfix⟩
    -- the subgroup of `Gal(Λ/ℚ)` fixing `K` pointwise
    let Stab : Subgroup (↥Λ ≃ₐ[ℚ] ↥Λ) :=
      fixingSubgroup (↥Λ ≃ₐ[ℚ] ↥Λ) (Set.range (algebraMap ↥K ↥Λ))
    haveI hSG : IsGaloisGroup Stab ↥K ↥Λ :=
      IsGaloisGroup.of_isScalarTower (↥Λ ≃ₐ[ℚ] ↥Λ) ℚ ↥Λ ↥K
    haveI : IsGaloisGroup Stab (𝓞 K) (𝓞 Λ) :=
      IsGaloisGroup.of_isFractionRing Stab (𝓞 K) (𝓞 Λ) ↥K ↥Λ
    -- the ℚ-level level inertia is contained in `Stab`
    have hHle : (Work.SSGRoute.inertiaSub ℚ SSGRoute.QBar A).map (AlgEquiv.restrictNormalHom ↥Λ) ≤
        Stab := by
      rintro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
      rw [show Stab = fixingSubgroup (↥Λ ≃ₐ[ℚ] ↥Λ) (Set.range (algebraMap ↥K ↥Λ)) from rfl,
        mem_fixingSubgroup_iff]
      rintro y ⟨x, rfl⟩
      rw [AlgEquiv.smul_def]
      apply Subtype.coe_injective
      have h2 : (↑((AlgEquiv.restrictNormalHom ↥Λ σ) (algebraMap ↥K ↥Λ x)) : SSGRoute.QBar)
          = σ (↑(algebraMap ↥K ↥Λ x) : SSGRoute.QBar) :=
        @AlgEquiv.restrictNormal_apply ℚ _ SSGRoute.QBar _ _ Λ (inferInstance : Normal ℚ Λ) σ
          (algebraMap ↥K ↥Λ x)
      have h3 : σ (↑(algebraMap ↥K ↥Λ x) : SSGRoute.QBar) = ↑(algebraMap ↥K ↥Λ x) :=
        (IntermediateField.mem_fixingSubgroup_iff K σ).mp (hle hσ) _ x.2
      exact h2.trans h3
    rw [hH] at hHle
    -- the level inertia of `Λ` over `K` has cardinality `e(P'/K)`
    have hcardK : Nat.card ↥(Ideal.inertia Stab P'.asIdeal) =
        P'.asIdeal.ramificationIdx (𝓞 K) := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Stab)
            (p := P'.asIdeal.under (𝓞 K)) (P := P'.asIdeal)]
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P'.asIdeal.under (𝓞 K)) P'.asIdeal Stab]
    -- it is the `subgroupOf`-image of the ℚ-level level inertia
    have hsub : (Ideal.inertia (↥Λ ≃ₐ[ℚ] ↥Λ) P'.asIdeal).subgroupOf Stab =
        Ideal.inertia Stab P'.asIdeal :=
      AddSubgroup.subgroupOf_inertia (I := P'.asIdeal.toAddSubgroup) Stab
    -- hence the two level inertia subgroups have the same cardinality
    have hcard : Nat.card ↥(Ideal.inertia (↥Λ ≃ₐ[ℚ] ↥Λ) P'.asIdeal) =
        P'.asIdeal.ramificationIdx (𝓞 K) := by
      rw [← hcardK, ← hsub]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv.symm
    have heq : P'.asIdeal.ramificationIdx (𝓞 K) = P'.asIdeal.ramificationIdx ℤ := by
      rw [← hcard, hcardΛ]
    -- the tower formula of ramification indices
    have htower : P'.asIdeal.ramificationIdx ℤ =
        P₀.asIdeal.ramificationIdx ℤ * P'.asIdeal.ramificationIdx (𝓞 K) :=
      Ideal.ramificationIdx_tower (R := ℤ) (S := 𝓞 K) (T := 𝓞 Λ) P₀.asIdeal P'.asIdeal
    have hpos : 0 < P'.asIdeal.ramificationIdx ℤ :=
      Ideal.ramificationIdx_pos (R := ℤ) P'.asIdeal
    have heq2 : P'.asIdeal.ramificationIdx ℤ =
        P₀.asIdeal.ramificationIdx ℤ * P'.asIdeal.ramificationIdx ℤ :=
      calc P'.asIdeal.ramificationIdx ℤ
          = P₀.asIdeal.ramificationIdx ℤ * P'.asIdeal.ramificationIdx (𝓞 K) := htower
        _ = P₀.asIdeal.ramificationIdx ℤ * P'.asIdeal.ramificationIdx ℤ := by rw [heq]
    have hone : P₀.asIdeal.ramificationIdx ℤ = 1 := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [one_mul]
      exact heq2.symm
    exact hPnotunr ((Ideal.ramificationIdx_eq_one_iff (R := ℤ) (S := 𝓞 K)
      (q := P₀.asIdeal)).mp hone)
  -- ## Step 7: `A` has `A.valuation q < 1`
  have hval : A.valuation ((q : ℕ) : SSGRoute.QBar) < 1 := by
    have h1 : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K P₀).valuation
        (algebraMap (𝓞 K) ↥K ((q : ℤ) : 𝓞 K)) < 1 :=
      (Work.SSGRoute.valuationSubringAtPrime_valuation_lt_one_iff_mem P₀
        ((q : ℤ) : 𝓞 K)).mpr hqP
    rw [← hAspec, Work.SSGRoute.comap_valuation_lt_one_iff] at h1
    simpa using h1
  exact ⟨A, hA, hval, hramK⟩

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
