import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHomType
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi
import Submission.NK.Reconstruct.frobUniquenessAwayFromL
import Submission.NK.Reconstruct.isFrobElementAt_restrictScalars
import Submission.NK.ReconstructField.levelPrimeMap_localDegree_eq
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen_gen
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.NK.UchidaKummer.API.localDeg_tower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

namespace NK.Reconstruct

/-- **The correspondence of levels preserves the degree**: the degree of a finite level of
`Ω/K₁` over `K₁` equals the degree of its image under `ψ`-correspondence over `K₂`.  (The proof
routes through the index of the fixing subgroup, so normality of `L` is not needed.) -/
theorem finrank_levelMap {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] :
    Module.finrank K₁ ↥L = Module.finrank K₂ ↥(NK.Reconstruct.levelMap ψ L) := by
  haveI : IsGalois K₁ Ω := IsSepClosure.isGalois
  haveI : IsGalois K₂ Ω := IsSepClosure.isGalois
  haveI : FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L) :=
    NK.Reconstruct.finiteDimensional_levelMap hψ L
  rw [IntermediateField.finrank_eq_fixingSubgroup_index Ω L,
    ← Subgroup.index_map_equiv L.fixingSubgroup ψ,
    ← NK.Reconstruct.fixingSubgroup_levelMap hψ L]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω
    (NK.Reconstruct.levelMap ψ L)).symm

/-- **The residue prime of the corresponding level has the same residue characteristic.** -/
theorem charP_levelPrimeMapGen {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : NK.Reconstruct.LocalCorrespondence ψ)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ψ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L) (p : ℕ)
    (hres : CharP (NumberField.RingOfIntegers ↥L ⧸ 𝔭.asIdeal) p) :
    CharP (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L) ⧸
      (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal) p := by
  have h1 : CharP (NumberField.RingOfIntegers ↥L ⧸ 𝔭.asIdeal)
      (NK.LocalInputs.primeBelowNat ↥L 𝔭) :=
    NK.ReconstructField.charP_of_liesOver 𝔭 (NK.LocalInputs.primeBelow ↥L 𝔭)
      (NK.LocalInputs.primeBelow_liesOver ↥L 𝔭)
  have hp : NK.LocalInputs.primeBelowNat ↥L 𝔭 = p := CharP.eq _ h1 hres
  have h2 : CharP (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L) ⧸
      (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal)
      (NK.LocalInputs.primeBelowNat ↥(NK.Reconstruct.levelMap ψ L)
        (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭)) :=
    NK.ReconstructField.charP_of_liesOver (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭)
      (NK.LocalInputs.primeBelow ↥(NK.Reconstruct.levelMap ψ L)
        (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭))
      (NK.LocalInputs.primeBelow_liesOver ↥(NK.Reconstruct.levelMap ψ L)
        (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭))
  rw [NK.ReconstructField.primeBelowNat_levelPrimeMapGen ψ hψ a L 𝔭, hp] at h2
  exact h2

set_option maxHeartbeats 1000000 in
theorem inertiaDeg_levelPrimeMapGen_splitCompletely {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : NK.Reconstruct.LocalCorrespondence ψ)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ψ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L)
    (hsplit : NK.Reconstruct.SplitsCompletelyOverRat 𝔭) :
    (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K₂) = 1 := by
  -- ## Step 0: `localDeg 𝔭 (𝔭 ∩ K₁) = 1`
  set p₀ : NK.Chebotarev.PrimeIdeal ℚ := NK.LocalInputs.primeBelow ↥L 𝔭 with hp₀
  set P₀ : NK.Chebotarev.PrimeIdeal K₁ := 𝔭.under (NumberField.RingOfIntegers K₁) with hP₀
  have hC : NK.UchidaKummer.localDeg 𝔭 p₀ = 1 := by
    rw [NK.UchidaKummer.localDeg, hsplit.2, hsplit.1, one_mul]
  haveI hTOW : IsScalarTower ℚ K₁ ↥L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hlies₀ : P₀.asIdeal.LiesOver p₀.asIdeal :=
    Ideal.LiesOver.mk (by
      rw [NK.LocalInputs.primeBelow_asIdeal]
      exact (Ideal.under_under (A := NumberField.RingOfIntegers ℚ)
        (B := NumberField.RingOfIntegers K₁) (C := NumberField.RingOfIntegers ↥L)
        𝔭.asIdeal).symm)
  have hlies₁ : 𝔭.asIdeal.LiesOver P₀.asIdeal := Ideal.over_under 𝔭.asIdeal
  have htower : NK.UchidaKummer.localDeg 𝔭 p₀ =
      NK.UchidaKummer.localDeg 𝔭 P₀ * NK.UchidaKummer.localDeg P₀ p₀ :=
    NK.UchidaKummer.API.localDeg_tower (K := ℚ) (L := K₁) (M := ↥L) p₀ P₀ 𝔭 hlies₀ hlies₁
  have hC1 : NK.UchidaKummer.localDeg 𝔭 P₀ = 1 :=
    Nat.eq_one_of_mul_eq_one_right (htower.symm.trans hC)
  -- ## Step 1: a finite normal level `L'` over `K₁` containing `L`
  obtain ⟨L', hLL', hL'fd, hL'norm, hL'nf⟩ :
      ∃ L' : IntermediateField K₁ Ω,
        L ≤ L' ∧ FiniteDimensional K₁ L' ∧ Normal K₁ L' ∧ NumberField ↥L' := by
    haveI : Normal K₁ Ω := IsSepClosure.isGalois.to_normal
    exact ⟨IntermediateField.normalClosure K₁ ↥L Ω, IntermediateField.le_normalClosure L,
      inferInstance, (isNormalClosure_normalClosure K₁ ↥L Ω).normal, inferInstance⟩
  haveI := hL'fd
  haveI := hL'norm
  haveI := hL'nf
  haveI hNfd : FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L') :=
    NK.Reconstruct.finiteDimensional_levelMap hψ L'
  haveI hNnorm : Normal K₂ (NK.Reconstruct.levelMap ψ L') :=
    NK.Reconstruct.normal_levelMap hψ L'
  haveI hNnf : NumberField ↥(NK.Reconstruct.levelMap ψ L') :=
    NK.Reconstruct.numberField_levelMap hψ L'
  -- ## Step 2: the algebra structures
  letI hAlgL : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra
  have hAlgL_apply : ∀ x : ↥L, (algebraMap ↥L ↥L') x = (⟨(x : Ω), hLL' x.2⟩ : ↥L') :=
    fun x => rfl
  haveI hTowerL : IsScalarTower K₁ ↥L ↥L' :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  letI hAlgM : Algebra ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L') :=
    (IntermediateField.inclusion (NK.ReconstructField.levelMap_monotone ψ hLL')).toRingHom.toAlgebra
  have hAlgM_apply : ∀ y : ↥(NK.Reconstruct.levelMap ψ L),
      (algebraMap ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L')) y =
        (⟨(y : Ω), NK.ReconstructField.levelMap_monotone ψ hLL' y.2⟩ :
          ↥(NK.Reconstruct.levelMap ψ L')) := fun y => rfl
  haveI hTowerM : IsScalarTower K₂ ↥(NK.Reconstruct.levelMap ψ L)
      ↥(NK.Reconstruct.levelMap ψ L') :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  -- ## Step 3: the fiber count
  have hcount : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard =
      ((NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal.primesOver
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))).ncard :=
    NK.ReconstructField.ncard_primesOver_levelPrimeMapGen_gen ψ hψ a L L' hLL'
      hAlgL_apply hAlgM_apply 𝔭
  -- ## Step 4: primes `P | 𝔭` in `L'` and `Q | 𝔮` in `N`
  set 𝔮 : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ψ L) :=
    NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭 with h𝔮
  obtain ⟨P, hP⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥L) (L := ↥L') 𝔭
  obtain ⟨Q, hQ⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥(NK.Reconstruct.levelMap ψ L)) (L := ↥(NK.Reconstruct.levelMap ψ L')) 𝔮
  -- ## Step 5: the fundamental identities
  haveI hNormL : Normal ↥L ↥L' := Normal.tower_top_of_normal K₁ ↥L ↥L'
  haveI hNormM : Normal ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L') :=
    Normal.tower_top_of_normal K₂ ↥(NK.Reconstruct.levelMap ψ L)
      ↥(NK.Reconstruct.levelMap ψ L')
  haveI hGalL : IsGalois ↥L ↥L' :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L') :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hPL₀ : P.asIdeal.LiesOver P₀.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    show Ideal.under (NumberField.RingOfIntegers K₁) 𝔭.asIdeal =
      Ideal.under (NumberField.RingOfIntegers K₁) P.asIdeal
    rw [hP.over]
    exact Ideal.under_under (A := NumberField.RingOfIntegers K₁)
      (B := NumberField.RingOfIntegers ↥L) (C := NumberField.RingOfIntegers ↥L') P.asIdeal
  have h𝔮lies : 𝔮.asIdeal.LiesOver (a.primeMap P₀).asIdeal :=
    NK.ReconstructField.levelPrimeMapGen_liesOver ψ hψ a L P₀ 𝔭 hlies₁
  haveI hQP₀ : Q.asIdeal.LiesOver (a.primeMap P₀).asIdeal := by
    refine Ideal.LiesOver.mk ?_
    show (a.primeMap P₀).asIdeal = Ideal.under (NumberField.RingOfIntegers K₂) Q.asIdeal
    rw [← Ideal.under_under (A := NumberField.RingOfIntegers K₂)
        (B := NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L))
        (C := NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) Q.asIdeal,
      ← hQ.over]
    exact h𝔮lies.over
  -- ## Step 6: the four instance packages for the ramification/inertia-in identities
  letI hActL : MulSemiringAction Gal(↥L'/↥L) (NumberField.RingOfIntegers ↥L') :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers ↥L) ↥L ↥L'
      (NumberField.RingOfIntegers ↥L')
  haveI hGrpL : IsGaloisGroup Gal(↥L'/↥L) (NumberField.RingOfIntegers ↥L)
      (NumberField.RingOfIntegers ↥L') :=
    IsGaloisGroup.of_isFractionRing Gal(↥L'/↥L) (NumberField.RingOfIntegers ↥L)
      (NumberField.RingOfIntegers ↥L') ↥L ↥L'
  letI hActL₁ : MulSemiringAction Gal(↥L'/K₁) (NumberField.RingOfIntegers ↥L') :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K₁) K₁ ↥L'
      (NumberField.RingOfIntegers ↥L')
  haveI hGrpL₁ : IsGaloisGroup Gal(↥L'/K₁) (NumberField.RingOfIntegers K₁)
      (NumberField.RingOfIntegers ↥L') :=
    IsGaloisGroup.of_isFractionRing Gal(↥L'/K₁) (NumberField.RingOfIntegers K₁)
      (NumberField.RingOfIntegers ↥L') K₁ ↥L'
  letI hActM₁ : MulSemiringAction
      Gal(↥(NK.Reconstruct.levelMap ψ L')/K₂)
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K₂) K₂
      ↥(NK.Reconstruct.levelMap ψ L') (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))
  haveI hGrpM₁ : IsGaloisGroup Gal(↥(NK.Reconstruct.levelMap ψ L')/K₂)
      (NumberField.RingOfIntegers K₂)
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) :=
    IsGaloisGroup.of_isFractionRing Gal(↥(NK.Reconstruct.levelMap ψ L')/K₂)
      (NumberField.RingOfIntegers K₂)
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) K₂
      ↥(NK.Reconstruct.levelMap ψ L')
  letI hActM : MulSemiringAction
      Gal(↥(NK.Reconstruct.levelMap ψ L')/↥(NK.Reconstruct.levelMap ψ L))
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L))
      ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L')
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))
  haveI hGrpM : IsGaloisGroup
      Gal(↥(NK.Reconstruct.levelMap ψ L')/↥(NK.Reconstruct.levelMap ψ L))
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L))
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) :=
    IsGaloisGroup.of_isFractionRing
      Gal(↥(NK.Reconstruct.levelMap ψ L')/↥(NK.Reconstruct.levelMap ψ L))
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L))
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))
      ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L')
  -- ## Step 7: the two fundamental identities
  have hfund1 : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard *
      (𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L') *
       𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L')) =
      Module.finrank ↥L ↥L' := by
    rw [Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal
      (NumberField.RingOfIntegers ↥L') Gal(↥L'/↥L)]
    exact IsGalois.card_aut_eq_finrank ↥L ↥L'
  have hfund2 : (𝔮.asIdeal.primesOver (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))).ncard *
      (𝔮.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) *
       𝔮.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))) =
      Module.finrank ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L') := by
    rw [Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔮.asIdeal
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))
      Gal(↥(NK.Reconstruct.levelMap ψ L')/↥(NK.Reconstruct.levelMap ψ L))]
    exact IsGalois.card_aut_eq_finrank ↥(NK.Reconstruct.levelMap ψ L)
      ↥(NK.Reconstruct.levelMap ψ L')
  -- ## Step 8: the local degree at the intermediate primes
  have hBB : NK.UchidaKummer.localDeg P 𝔭 = NK.UchidaKummer.localDeg Q 𝔮 := by
    have hB : NK.UchidaKummer.localDeg P 𝔭 =
        𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L') *
        𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L') := by
      rw [NK.UchidaKummer.localDeg,
        Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P.asIdeal Gal(↥L'/↥L),
        Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal Gal(↥L'/↥L)]
    have hB' : NK.UchidaKummer.localDeg Q 𝔮 =
        𝔮.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) *
        𝔮.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) := by
      rw [NK.UchidaKummer.localDeg,
        Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮.asIdeal Q.asIdeal
          Gal(↥(NK.Reconstruct.levelMap ψ L')/↥(NK.Reconstruct.levelMap ψ L)),
        Ideal.inertiaDegIn_eq_inertiaDeg 𝔮.asIdeal Q.asIdeal
          Gal(↥(NK.Reconstruct.levelMap ψ L')/↥(NK.Reconstruct.levelMap ψ L))]
    have hfin : Module.finrank ↥L ↥L' =
        Module.finrank ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L') := by
      haveI hGal₁ : IsGalois K₁ ↥L' :=
        Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
      haveI hGal₂ : IsGalois K₂ ↥(NK.Reconstruct.levelMap ψ L') :=
        Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
      have h1 := Module.finrank_mul_finrank K₁ ↥L ↥L'
      have h2 := Module.finrank_mul_finrank K₂ ↥(NK.Reconstruct.levelMap ψ L)
        ↥(NK.Reconstruct.levelMap ψ L')
      have h3 : Module.finrank K₁ ↥L' = Module.finrank K₂ ↥(NK.Reconstruct.levelMap ψ L') := by
        rw [← IsGalois.card_aut_eq_finrank K₁ ↥L',
          ← IsGalois.card_aut_eq_finrank K₂ ↥(NK.Reconstruct.levelMap ψ L')]
        exact Nat.card_congr (NK.Reconstruct.levelMapEquiv hψ L').toEquiv
      have h4 : Module.finrank K₁ ↥L = Module.finrank K₂ ↥(NK.Reconstruct.levelMap ψ L) :=
        finrank_levelMap ψ hψ L
      have hpos : 0 < Module.finrank K₁ ↥L := Module.finrank_pos
      have key : Module.finrank K₁ ↥L * Module.finrank ↥L ↥L' =
          Module.finrank K₁ ↥L *
            Module.finrank ↥(NK.Reconstruct.levelMap ψ L) ↥(NK.Reconstruct.levelMap ψ L') := by
        rw [h1, h3, ← h2, ← h4]
      exact Nat.mul_left_cancel hpos key
    have hne : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard ≠ 0 := by
      obtain ⟨P', hP'⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
        (K := ↥L) (L := ↥L') 𝔭
      have hmemP : P'.asIdeal ∈ 𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L') :=
        ⟨P'.isPrime, hP'⟩
      exact Set.ncard_ne_zero_of_mem hmemP
    have hkey : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard *
        (𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L') *
         𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L')) =
        (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L')).ncard *
        (𝔮.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) *
         𝔮.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L'))) := by
      rw [hfund1, hfin, ← hfund2, hcount]
    have hBBraw : 𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L') *
        𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L') =
        𝔮.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) *
        𝔮.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) :=
      Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) hkey
    rw [hB, hB', hBBraw]
  -- ## Step 9: the local degrees over the base primes agree (`levelPrimeMap_localDegree_eq`)
  have hAA : NK.UchidaKummer.localDeg P P₀ =
      NK.UchidaKummer.localDeg Q (Q.under (NumberField.RingOfIntegers K₂)) := by
    have hL : NK.UchidaKummer.localDeg P P₀ =
        P₀.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L') *
        P₀.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L') := by
      rw [NK.UchidaKummer.localDeg,
        ← Ideal.ramificationIdxIn_eq_ramificationIdx P₀.asIdeal P.asIdeal Gal(↥L'/K₁),
        ← Ideal.inertiaDegIn_eq_inertiaDeg P₀.asIdeal P.asIdeal Gal(↥L'/K₁)]
    have hR : NK.UchidaKummer.localDeg Q (Q.under (NumberField.RingOfIntegers K₂)) =
        (a.primeMap P₀).asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) *
        (a.primeMap P₀).asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ψ L')) := by
      rw [NK.UchidaKummer.localDeg,
        ← Ideal.ramificationIdxIn_eq_ramificationIdx (a.primeMap P₀).asIdeal Q.asIdeal
          Gal(↥(NK.Reconstruct.levelMap ψ L')/K₂),
        ← Ideal.inertiaDegIn_eq_inertiaDeg (a.primeMap P₀).asIdeal Q.asIdeal
          Gal(↥(NK.Reconstruct.levelMap ψ L')/K₂)]
    rw [hL, hR]
    exact NK.ReconstructField.levelPrimeMap_localDegree_eq ψ hψ a L' P₀
  -- ## Step 10: the two towers
  have hABC : NK.UchidaKummer.localDeg P P₀ =
      NK.UchidaKummer.localDeg P 𝔭 * NK.UchidaKummer.localDeg 𝔭 P₀ :=
    NK.UchidaKummer.API.localDeg_tower (K := K₁) (L := ↥L) (M := ↥L') P₀ 𝔭 P hlies₁ hP
  have hQu : Q.under (NumberField.RingOfIntegers K₂) = 𝔮.under (NumberField.RingOfIntegers K₂) :=
    IsDedekindDomain.HeightOneSpectrum.ext (by
      show Ideal.under (NumberField.RingOfIntegers K₂) Q.asIdeal =
        Ideal.under (NumberField.RingOfIntegers K₂) 𝔮.asIdeal
      rw [← hQP₀.over, ← h𝔮lies.over])
  have h𝔮Q₂ : 𝔮.asIdeal.LiesOver (Q.under (NumberField.RingOfIntegers K₂)).asIdeal := by
    refine Ideal.LiesOver.mk ?_
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    rw [← hQP₀.over, ← h𝔮lies.over]
  have hA'B'C' : NK.UchidaKummer.localDeg Q (Q.under (NumberField.RingOfIntegers K₂)) =
      NK.UchidaKummer.localDeg Q 𝔮 *
        NK.UchidaKummer.localDeg 𝔮 (Q.under (NumberField.RingOfIntegers K₂)) :=
    NK.UchidaKummer.API.localDeg_tower (K := K₂)
      (L := ↥(NK.Reconstruct.levelMap ψ L)) (M := ↥(NK.Reconstruct.levelMap ψ L'))
      (Q.under (NumberField.RingOfIntegers K₂)) 𝔮 Q h𝔮Q₂ hQ
  -- ## Step 11: cancel
  have hCC : NK.UchidaKummer.localDeg 𝔮 (Q.under (NumberField.RingOfIntegers K₂)) =
      NK.UchidaKummer.localDeg 𝔭 P₀ := by
    have hpos : 0 < NK.UchidaKummer.localDeg P 𝔭 := by
      rw [NK.UchidaKummer.localDeg]
      exact Nat.mul_pos (Ideal.ramificationIdx_pos (NumberField.RingOfIntegers ↥L) P.asIdeal)
        (Ideal.inertiaDeg_pos P.asIdeal (NumberField.RingOfIntegers ↥L))
    have key : NK.UchidaKummer.localDeg P 𝔭 * NK.UchidaKummer.localDeg 𝔭 P₀ =
        NK.UchidaKummer.localDeg P 𝔭 *
          NK.UchidaKummer.localDeg 𝔮 (Q.under (NumberField.RingOfIntegers K₂)) := by
      rw [← hABC, hAA, hA'B'C', hBB]
    exact (Nat.mul_left_cancel hpos key).symm
  -- ## Step 12: conclude
  have hfinal : NK.UchidaKummer.localDeg 𝔮 (Q.under (NumberField.RingOfIntegers K₂)) = 1 :=
    hCC.trans hC1
  rw [hQu] at hfinal
  rw [NK.UchidaKummer.localDeg] at hfinal
  exact Nat.eq_one_of_mul_eq_one_left hfinal

/-! ## The transfer of the Frobenius property along the level correspondence

The main auxiliary step of the proof of `frobCorrespondenceGammaHaus_levelSplit`: if `g` is a
Frobenius element at the prime `𝔭` of `↥L` over the base `↥L`, and `𝔮` is the prime of
`↥(levelMap ψ L)` corresponding to `𝔭`, then the element of `Gal(Ω/↥(levelMap ψ L))` corresponding
to `g` under the level isomorphism `levelGalEquiv` is a Frobenius element at `𝔮`.

This is the point at which the hypothesis `SplitsCompletelyOverRat 𝔭` is used: the two residue
degrees `f(𝔭/K₁)` and `f(𝔮/K₂)` are one, so that the Frobenius conditions over the intermediate
base fields `↥L`, `↥(levelMap ψ L)` agree with those over `K₁`, `K₂`. -/

theorem levelGalEquiv_apply_eq_levelSplit {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] (g : Gal(Ω/↥L)) (x : Ω) :
    (NK.ReconstructField.levelGalEquiv ψ hψ L g) x = ψ (g.restrictScalars K₁) x := by
  have h : ((NK.ReconstructField.levelGalEquiv ψ hψ L g :
        Gal(Ω/↥(NK.Reconstruct.levelMap ψ L))) : Ω ≃+* Ω) =
      ((ψ (g.restrictScalars K₁) : Gal(Ω/K₂)) : Ω ≃+* Ω) := by
    rw [NK.ReconstructField.levelGalEquiv]
    simp only [MulEquiv.trans_apply]
    simp [IntermediateField.fixingSubgroupEquiv, MulEquiv.subgroupCongr_apply]
  exact congrFun (congrArg DFunLike.coe h) x

theorem levelGalEquiv_restrictScalars_levelSplit {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] (g : Gal(Ω/↥L)) :
    AlgEquiv.restrictScalars K₂ (NK.ReconstructField.levelGalEquiv ψ hψ L g)
      = ψ (AlgEquiv.restrictScalars K₁ g) := by
  rw [NK.ReconstructField.levelGalEquiv]
  rfl

theorem restrictNormalHom_restrictScalars_eq_levelSplit {F L M Ω : Type*} [Field F] [Field L] [Field M]
    [Field Ω] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
    [Algebra L Ω] [Algebra F Ω] [IsScalarTower F L Ω] [Algebra M Ω]
    [IsScalarTower F M Ω] [IsScalarTower L M Ω] [Normal F M] [Normal L M]
    (ρ : Gal(Ω/L)) :
    (AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) M ρ).restrictScalars F
      = AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M (ρ.restrictScalars F) := by
  ext x
  apply FaithfulSMul.algebraMap_injective M Ω
  rw [AlgEquiv.restrictScalars_apply]
  rw [show (AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) M ρ) = ρ.restrictNormal M from rfl]
  rw [show (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M (ρ.restrictScalars F))
      = (ρ.restrictScalars F).restrictNormal M from rfl]
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes]
  rfl

theorem isFrobElementAt_levelGalEquiv_levelSplit {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : NK.Reconstruct.LocalCorrespondence ψ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ψ hψ a)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ψ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L)
    (h𝔭 : 𝔭.asIdeal.inertiaDeg (NumberField.RingOfIntegers K₁) = 1)
    (h𝔮 : (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K₂) = 1)
    (g : Gal(Ω/↥L)) (hg : NK.Reconstruct.IsFrobElementAt 𝔭 g) :
    NK.Reconstruct.IsFrobElementAt (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭)
      (NK.ReconstructField.levelGalEquiv ψ hψ L g) := by
  classical
  have hσid : ∀ x : Ω,
      (NK.ReconstructField.levelGalEquiv ψ hψ L g) x = ψ (g.restrictScalars K₁) x :=
    fun x => levelGalEquiv_apply_eq_levelSplit ψ hψ L g x
  rw [NK.Reconstruct.IsFrobElementAt]
  intro M hMfd hMnorm hMnf
  let L₂ : IntermediateField K₂ Ω := NK.Reconstruct.levelMap ψ L
  -- ## Step 1: `M` viewed over `K₂`
  let M₂ : IntermediateField K₂ Ω := IntermediateField.restrictScalars K₂ M
  haveI hM₂fd : FiniteDimensional K₂ M₂ := by
    haveI h1 : Module.Finite ↥L₂ M := hMfd
    have h2 : Module.Finite K₂ ↥M := Module.Finite.trans ↥L₂ ↥M
    exact h2
  have hM₂eq : (M₂ : Set Ω) = (M : Set Ω) := IntermediateField.coe_restrictScalars K₂
  -- ## Step 2: the normal level `M'` over `K₁`
  let P₀ : IntermediateField K₁ Ω := NK.Reconstruct.levelMap ψ.symm M₂
  haveI hP₀fd : FiniteDimensional K₁ P₀ :=
    NK.Reconstruct.finiteDimensional_levelMap (Submission.NeukirchUchida.isHomeomorph_symm ψ hψ) M₂
  haveI hP₀nf : NumberField ↥P₀ :=
    NK.Reconstruct.numberField_levelMap (Submission.NeukirchUchida.isHomeomorph_symm ψ hψ) M₂
  let E₀ : IntermediateField K₁ Ω := L ⊔ P₀
  haveI hE₀fd : FiniteDimensional K₁ E₀ := IntermediateField.finiteDimensional_sup L P₀
  haveI hΩnorm : Normal K₁ Ω := IsSepClosure.isGalois.to_normal
  let M' : IntermediateField K₁ Ω := IntermediateField.normalClosure K₁ ↥E₀ Ω
  have hE₀M' : E₀ ≤ M' := IntermediateField.le_normalClosure E₀
  haveI hM'fd : FiniteDimensional K₁ M' := inferInstance
  haveI hM'norm : Normal K₁ M' := (isNormalClosure_normalClosure K₁ ↥E₀ Ω).normal
  haveI hM'nf : NumberField ↥M' := inferInstance
  have hLM' : L ≤ M' := le_trans le_sup_left hE₀M'
  have hP₀M' : P₀ ≤ M' := le_trans le_sup_right hE₀M'
  have hM₂M' : M₂ ≤ NK.Reconstruct.levelMap ψ M' := by
    have h1 : NK.Reconstruct.levelMap ψ P₀ ≤ NK.Reconstruct.levelMap ψ M' :=
      NK.ReconstructField.levelMap_monotone (ϕ := ψ) hP₀M'
    rwa [NK.ReconstructField.levelMap_levelMap_symm ψ hψ M₂] at h1
  have hMM' : (M : Set Ω) ⊆ (NK.Reconstruct.levelMap ψ M' : Set Ω) :=
    fun x hx => hM₂M' (by rwa [← hM₂eq] at hx)
  -- ## Step 3: apply `hg` at `M'` viewed over `↥L`
  let Me : IntermediateField ↥L Ω := IntermediateField.extendScalars hLM'
  haveI hMefin : FiniteDimensional ↥L Me := by
    haveI h1 : Module.Finite K₁ ↥Me := hM'fd
    exact Module.Finite.of_restrictScalars_finite K₁ ↥L ↥Me
  haveI hSTMeΩ : IsScalarTower K₁ ↥Me Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hSTLMeΩ : IsScalarTower ↥L ↥Me Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hNormK₁Me : Normal K₁ ↥Me := hM'norm
  haveI hMenorm : Normal ↥L Me := Normal.tower_top_of_normal K₁ ↥L ↥Me
  haveI hMenf : NumberField ↥Me := hM'nf
  obtain ⟨P_M, hP_M_lies, hP_M_frob⟩ := hg Me
  -- ## Step 4: base change `↥L` to `K₁`
  have hfK : (Ideal.under (NumberField.RingOfIntegers ↥L) P_M.asIdeal).inertiaDeg
      (NumberField.RingOfIntegers K₁) = 1 := by
    rw [show Ideal.under (NumberField.RingOfIntegers ↥L) P_M.asIdeal = 𝔭.asIdeal from
      hP_M_lies.over.symm]
    exact h𝔭
  have hP_M_frobK₁ : NK.Chebotarev.IsFrobAt (K := K₁) (L := ↥Me) P_M
      ((AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := Ω) Me g).restrictScalars K₁) :=
    NK.Reconstruct.isFrobAt_of_isFrobAt_of_inertiaDeg_eq_one P_M
      (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := Ω) Me g) hfK hP_M_frob
  have hElCompat : (AlgEquiv.restrictNormalHom (F := ↥L) (K₁ := Ω) Me g).restrictScalars K₁
      = AlgEquiv.restrictNormalHom (F := K₁) (K₁ := Ω) Me (g.restrictScalars K₁) :=
    restrictNormalHom_restrictScalars_eq_levelSplit (F := K₁) (L := ↥L) (M := ↥Me) (Ω := Ω) g
  -- ## Step 5: a place `A` over `P_M` and the correspondence `b`
  obtain ⟨A, hA, hAval⟩ := NK.Reconstruct.exists_place_over_prime (K := K₁) (K' := Ω) M'
    (P_M.under (NumberField.RingOfIntegers K₁)) P_M (Ideal.over_under P_M.asIdeal)
  have hAne : A.comap (algebraMap K₁ Ω) ≠ ⊤ := by
    rw [hAval]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _
  let A' : NK.Reconstruct.FinitePlaceOf K₁ Ω := ⟨A, hAne⟩
  have hA_Me : A.comap (algebraMap ↥Me Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥Me P_M := hA
  have hprimeM' : NK.Reconstruct.primeOfLevel A'.1 M'
      (NK.Reconstruct.comap_level_ne_top A'.2 M') = P_M :=
    NK.Reconstruct.primeOfLevel_eq_of_comap_eq M' hA _
  have hAL : A.comap (algebraMap ↥L Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L 𝔭 := by
    have hcomp : A.comap (algebraMap ↥L Ω)
        = (A.comap (algebraMap ↥Me Ω)).comap (algebraMap ↥L ↥Me) := by
      refine SetLike.ext fun x => ?_
      simp only [ValuationSubring.mem_comap]
      rw [show algebraMap ↥L Ω x = algebraMap ↥Me Ω (algebraMap ↥L ↥Me x) from
        IsScalarTower.algebraMap_apply ↥L ↥Me Ω x]
    rw [hcomp, hA_Me,
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (q := P_M.under (NumberField.RingOfIntegers ↥L)) (w := P_M) (Ideal.over_under _)]
    congr 1
    exact IsDedekindDomain.HeightOneSpectrum.ext hP_M_lies.over.symm
  haveI hXfd : FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ M') :=
    NK.Reconstruct.finiteDimensional_levelMap hψ M'
  haveI hXnorm : Normal K₂ (NK.Reconstruct.levelMap ψ M') :=
    NK.Reconstruct.normal_levelMap hψ M'
  haveI hXnf : NumberField ↥(NK.Reconstruct.levelMap ψ M') :=
    NK.Reconstruct.numberField_levelMap hψ M'
  let X : IntermediateField K₂ Ω := NK.Reconstruct.levelMap ψ M'
  let P₁ : NK.Chebotarev.PrimeIdeal ↥X :=
    NK.Reconstruct.primeOfLevel (a.placeMap A').1 X
      (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 X)
  have hbX : NK.Chebotarev.IsFrobAt (K := K₂) (L := ↥X) P₁
      (AlgEquiv.restrictNormalHom (F := K₂) (K₁ := Ω) X (ψ (g.restrictScalars K₁))) := by
    refine b M' A' (g.restrictScalars K₁) ?_
    rw [hprimeM']
    rw [hElCompat] at hP_M_frobK₁
    exact hP_M_frobK₁
  -- ## Step 6: the prime `𝔮` and the descent to `M`
  have hL₂X : L₂ ≤ X := NK.ReconstructField.levelMap_monotone ψ hLM'
  letI hAlgL₂X : Algebra ↥L₂ ↥X := (IntermediateField.inclusion hL₂X).toRingHom.toAlgebra
  haveI hSTL₂XΩ : IsScalarTower ↥L₂ ↥X Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI hSTK₂L₂X : IsScalarTower K₂ ↥L₂ ↥X :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI hFDXL₂ : FiniteDimensional ↥L₂ ↥X := by
    haveI h1 : Module.Finite K₂ ↥X := hXfd
    exact Module.Finite.of_restrictScalars_finite K₂ ↥L₂ ↥X
  haveI hNormL₂X : Normal ↥L₂ ↥X := Normal.tower_top_of_normal K₂ ↥L₂ ↥X
  haveI hGalL₂X : IsGalois ↥L₂ ↥X :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hXunder : P₁.under (NumberField.RingOfIntegers ↥L₂) =
      NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭 := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L₂) ?_
    rw [← Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (q := P₁.under (NumberField.RingOfIntegers ↥L₂)) (w := P₁) (Ideal.over_under _)]
    rw [show (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥X P₁)
        = (a.placeMap A').1.comap (algebraMap ↥X Ω) from
      (NK.Reconstruct.primeOfLevel_spec (a.placeMap A').1 X
        (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 X)).symm]
    rw [ValuationSubring.comap_comap]
    rw [show (algebraMap ↥X Ω).comp (algebraMap ↥L₂ ↥X) = algebraMap ↥L₂ Ω from by
      ext x; exact IsScalarTower.algebraMap_apply ↥L₂ ↥X Ω x]
    rw [show (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭)
        = NK.Reconstruct.primeOfLevel (a.placeMap A').1 L₂
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 L₂) from
      NK.ReconstructField.levelPrimeMapGen_spec ψ hψ a L 𝔭 A' hAL]
    exact NK.Reconstruct.primeOfLevel_spec (a.placeMap A').1 L₂
      (NK.Reconstruct.comap_level_ne_top (a.placeMap A').2 L₂)
  have hσ₂X : (AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := Ω) X
        (NK.ReconstructField.levelGalEquiv ψ hψ L g)).restrictScalars K₂
      = AlgEquiv.restrictNormalHom (F := K₂) (K₁ := Ω) X (ψ (g.restrictScalars K₁)) := by
    rw [restrictNormalHom_restrictScalars_eq_levelSplit (F := K₂) (L := ↥L₂) (M := ↥X) (Ω := Ω)
      (NK.ReconstructField.levelGalEquiv ψ hψ L g)]
    rw [levelGalEquiv_restrictScalars_levelSplit ψ hψ L g]
  have hfL₂ : (Ideal.under (NumberField.RingOfIntegers ↥L₂) P₁.asIdeal).inertiaDeg
      (NumberField.RingOfIntegers K₂) = 1 := by
    rw [show Ideal.under (NumberField.RingOfIntegers ↥L₂) P₁.asIdeal =
        (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal from
      congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hXunder]
    exact h𝔮
  have hbK₂ : NK.Chebotarev.IsFrobAt (K := K₂) (L := ↥X) P₁
      ((AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := Ω) X
        (NK.ReconstructField.levelGalEquiv ψ hψ L g)).restrictScalars K₂) := by
    rw [hσ₂X]
    exact hbX
  have hresX : NK.Chebotarev.IsFrobAt (K := ↥L₂) (L := ↥X) P₁
      (AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := Ω) X
        (NK.ReconstructField.levelGalEquiv ψ hψ L g)) :=
    NK.Reconstruct.isFrobAt_of_isFrobAt_restrictScalars P₁
      (AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := Ω) X
        (NK.ReconstructField.levelGalEquiv ψ hψ L g)) hfL₂ hbK₂
  have hMX : (M : Set Ω) ⊆ (X : Set Ω) := hMM'
  let inclMX : ↥M →+* ↥X :=
    { toFun := fun x => ⟨(x : Ω), hMX x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  letI hAlgMX : Algebra ↥M ↥X := inclMX.toAlgebra
  haveI hTowerMX : IsScalarTower ↥L₂ ↥M ↥X :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI hTowerMXΩ : IsScalarTower ↥M ↥X Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hresM : NK.Chebotarev.IsFrobAt (K := ↥L₂) (L := ↥M) (P₁.under (NumberField.RingOfIntegers ↥M))
      (AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := ↥X) M
        (AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := Ω) X
          (NK.ReconstructField.levelGalEquiv ψ hψ L g))) :=
    NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := ↥L₂) (E := ↥M) (M := ↥X) P₁
      (AlgEquiv.restrictNormalHom (F := ↥L₂) (K₁ := Ω) X
        (NK.ReconstructField.levelGalEquiv ψ hψ L g)) hresX
  refine ⟨P₁.under (NumberField.RingOfIntegers ↥M), ?_, ?_⟩
  · refine Ideal.LiesOver.mk ?_
    show (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭).asIdeal =
      Ideal.under (NumberField.RingOfIntegers ↥L₂)
        (Ideal.under (NumberField.RingOfIntegers ↥M) P₁.asIdeal)
    rw [Ideal.under_under (A := NumberField.RingOfIntegers ↥L₂)
      (B := NumberField.RingOfIntegers ↥M) (C := NumberField.RingOfIntegers ↥X) P₁.asIdeal]
    exact (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hXunder).symm
  · rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (F := ↥L₂) ↥M ↥X (K₃ := Ω)
      (NK.ReconstructField.levelGalEquiv ψ hψ L g)]
    exact hresM

set_option maxHeartbeats 1000000 in
theorem frobCorrespondenceGammaHaus_levelSplit {K₁ : Type*} [Field K₁] [NumberField K₁] {K₂ : Type*}
    [Field K₂] [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (a : NK.Reconstruct.LocalCorrespondence ψ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ψ hψ a)
    (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ψ L)]
    (σbar : NK.Reconstruct.Gamma ↥L Ω ℓ ≃*
      NK.Reconstruct.Gamma ↥(NK.Reconstruct.levelMap ψ L) Ω ℓ)
    (hσbar : ∀ g : Gal(Ω/↥L), σbar (NK.Reconstruct.galToGamma (K := ↥L) (K' := Ω) ℓ g) =
      NK.Reconstruct.galToGamma (K := ↥(NK.Reconstruct.levelMap ψ L)) (K' := Ω) ℓ
        (NK.ReconstructField.levelGalEquiv ψ hψ L g))
    (p : ℕ) [Fact p.Prime]
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L)
    (hsplit : NK.Reconstruct.SplitsCompletelyOverRat 𝔭)
    (hres : CharP (NumberField.RingOfIntegers ↥L ⧸ 𝔭.asIdeal) p) (hne : p ≠ ℓ)
    (g₁ : Gal(Ω/↥L)) (g₂ : Gal(Ω/↥(NK.Reconstruct.levelMap ψ L)))
    (hg₁ : NK.Reconstruct.IsFrobElementAt 𝔭 g₁)
    (hg₂ : NK.Reconstruct.IsFrobElementAt
        (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭) g₂) :
    NK.Reconstruct.gammaHausMk (K := ↥(NK.Reconstruct.levelMap ψ L)) (K' := Ω) ℓ
        (σbar (NK.Reconstruct.galToGamma (K := ↥L) (K' := Ω) ℓ g₁))
      = NK.Reconstruct.gammaHausMk (K := ↥(NK.Reconstruct.levelMap ψ L)) (K' := Ω) ℓ
        (NK.Reconstruct.galToGamma (K := ↥(NK.Reconstruct.levelMap ψ L)) (K' := Ω) ℓ g₂) := by
  haveI hsep : IsSepClosure ↥(NK.Reconstruct.levelMap ψ L) Ω :=
    NK.Reconstruct.isSepClosure_level (k := K₂) (L := NK.Reconstruct.levelMap ψ L)
  rw [hσbar g₁]
  refine frobUniquenessAwayFromL ℓ p (NK.ReconstructField.levelPrimeMapGen ψ hψ a L 𝔭)
    (charP_levelPrimeMapGen ψ hψ a L 𝔭 p hres) hne
    (NK.ReconstructField.levelGalEquiv ψ hψ L g₁) g₂ ?_ hg₂
  exact isFrobElementAt_levelGalEquiv_levelSplit ψ hψ a b L 𝔭
    (NK.Reconstruct.inertiaDeg_eq_one_of_splitsCompletelyOverRat (K := K₁) 𝔭 hsplit)
    (inertiaDeg_levelPrimeMapGen_splitCompletely ψ hψ a L 𝔭 hsplit) g₁ hg₁

end NK.Reconstruct
