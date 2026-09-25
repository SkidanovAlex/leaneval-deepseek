import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq

set_option linter.unusedVariables false

open scoped NumberField Pointwise

namespace Commons.NumberTheory.NumberField.Completion

/-! ## The decomposition subgroup as the stabiliser of the valuation ring -/

section Stabilizer

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]

/-- **The valuation of the place `σ • w` at `σ x` is the valuation of `w` at `x`.** -/
private theorem valuation_placeSmul (σ : Gal(E/F))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (x : E) :
    IsDedekindDomain.HeightOneSpectrum.valuation E (placeSmul σ w) (σ x) =
      IsDedekindDomain.HeightOneSpectrum.valuation E w x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    (R := NumberField.RingOfIntegers E) (K := E)
    (galRestrict (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E) σ :
      NumberField.RingOfIntegers E ≃+* NumberField.RingOfIntegers E)
    σ.toRingEquiv
    (fun r => (algebraMap_galRestrict_apply (NumberField.RingOfIntegers F) σ r).symm)
    w (placeSmul σ w) (placeSmul_asIdeal σ w) x

/-- **The stabiliser of the valuation ring of a finite place is its decomposition group.** -/
private theorem mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (σ : Gal(E/F)) :
    σ ∈ MulAction.stabilizer (Gal(E/F))
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w) ↔
      σ ∈ decompositionSubgroup (K := F) w := by
  have hmem : ∀ y : E,
      (y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation E w y ≤ 1) := by
    intro y
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  constructor
  · intro h
    rw [MulAction.mem_stabilizer_iff] at h
    have hstab : ∀ y : E,
        (y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
          σ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w) := by
      intro y
      have hy : σ y ∈ σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
          σ⁻¹ • (σ y) ∈
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      rw [h] at hy
      simpa using hy.symm
    rw [mem_decompositionSubgroup]
    refine IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := E) ?_
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [valuation_placeSmul σ w x]
    exact (hmem x).symm.trans ((hstab x).trans (hmem (σ x)))
  · intro h
    rw [mem_decompositionSubgroup] at h
    rw [MulAction.mem_stabilizer_iff]
    refine SetLike.ext fun y => ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hkey : IsDedekindDomain.HeightOneSpectrum.valuation E w (σ⁻¹ • y) =
        IsDedekindDomain.HeightOneSpectrum.valuation E w y := by
      have h2 := valuation_placeSmul (F := F) σ w (σ⁻¹ • y)
      rw [h] at h2
      simpa using h2.symm
    have hy : σ⁻¹ • y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation E w (σ⁻¹ • y) ≤ 1 := hmem _
    have hy' : y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation E w y ≤ 1 := hmem _
    rw [hy, hy', hkey]

/-- The decomposition group of a place is the stabiliser of its valuation ring, in `•` form. -/
theorem smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (σ : Gal(E/F)) :
    σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
      σ ∈ decompositionSubgroup (K := F) w := by
  rw [← MulAction.mem_stabilizer_iff]
  exact mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup w σ

end Stabilizer

/-! ## Restriction of the decomposition group -/

open scoped Pointwise in
/-- **The restriction of a decomposition group element is a decomposition group element.** -/
theorem restrictNormalHom_mem_decompositionSubgroup {K M : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (L' : IntermediateField K M) [FiniteDimensional K L'] [Normal K L'] [IsGalois K ↥L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L'))
    (hq' : q'.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers ↥L'))
    {σ : Gal(M/K)} (hσ : σ ∈ decompositionSubgroup (K := K) q) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L' σ ∈ decompositionSubgroup (K := K) q' := by
  have hlies : q.asIdeal.LiesOver q'.asIdeal := ⟨hq'⟩
  have hcomap : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M q).comap
      (algebraMap ↥L' M) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L' q' :=
    Commons.RingTheory.Valuation.comap_valuationSubringAtPrime q' q hlies
  have hA : σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M q =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M q :=
    (smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup (F := K) (E := M) q σ).mpr hσ
  refine (smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup (F := K) (E := ↥L')
    q' (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L' σ)).mp ?_
  rw [← hcomap]
  rw [← Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M q) σ L']
  rw [hA]

theorem card_decompositionSubgroup_under_mul_card_ker
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (L' : IntermediateField K M) [FiniteDimensional K L'] [Normal K L'] [IsGalois K ↥L']
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L'))
    (hq' : q'.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers ↥L')) :
    Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q')
      * Nat.card (((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L').ker).comap
          (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q).subtype)
    = Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q) := by
  have hlies : q.asIdeal.LiesOver q'.asIdeal := ⟨hq'⟩
  let D : Subgroup Gal(M/K) := decompositionSubgroup (K := K) q
  let D' : Subgroup Gal(↥L'/K) := decompositionSubgroup (K := K) q'
  let ρ : Gal(M/K) →* Gal(↥L'/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L'
  let φ : D →* D' :=
    { toFun := fun σ => ⟨ρ σ.1, restrictNormalHom_mem_decompositionSubgroup L' q q' hq' σ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  have hsurj : Function.Surjective φ := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_mem_decompositionSubgroup_restrictNormalHom_eq
      (K := K) (M := M) L' q' q hq' hlies τ
    exact ⟨σ, Subtype.ext hσ⟩
  have hcard : Nat.card D = Nat.card φ.ker * Nat.card D' := by
    have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card D := by
      rw [← Subgroup.index_ker φ]
      exact Subgroup.card_mul_index φ.ker
    rw [MonoidHom.range_eq_top.mpr hsurj] at h1
    rw [show Nat.card (⊤ : Subgroup D') = Nat.card D' from
      Nat.card_congr (Subgroup.topEquiv (G := D')).toEquiv] at h1
    exact h1.symm
  have hker : φ.ker = (ρ.ker).comap D.subtype := by
    ext σ
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · intro h
      have h' := congrArg (fun x : D' => (x : Gal(↥L'/K))) h
      simpa [φ, ρ] using h'
    · intro h
      apply Subtype.ext
      simpa [φ, ρ] using h
  show Nat.card D' * Nat.card ((ρ.ker).comap D.subtype) = Nat.card D
  rw [hcard, ← hker, Nat.mul_comm]

end Commons.NumberTheory.NumberField.Completion
