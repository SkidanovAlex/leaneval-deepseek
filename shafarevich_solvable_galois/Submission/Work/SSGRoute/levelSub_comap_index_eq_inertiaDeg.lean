import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.levelSub_commutator_and_generator
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of the level subgroup is the inertia degree

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` over `k` and a finite
normal intermediate field `M ⊆ Ω`, the index in the decomposition group `D_A` of the level
subgroup `levelSub A M` (the elements of `D_A` acting trivially, modulo the maximal ideal, on the
level ring `A ∩ M`) is the inertia degree of the prime `P` of `𝓞 M` below `A` over `𝓞 k`.

The proof assembles three independent statements:

* `levelSub_comap_eq_inertia_comap` — the level subgroup is the preimage in `D_A` of the inertia
  subgroup `I_P ≤ Gal(M/k)`;
* `range_restrictNormalHom_eq_stabilizer` — the restriction `D_A → Gal(M/k)` has image the
  decomposition group (stabiliser of `P`) of `P`;
* `inertia_relIndex_stabilizer_eq_inertiaDeg` — the index `[D_P : I_P]` is the inertia degree
  (Mathlib's `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Work.SSGRoute
open scoped Pointwise NumberField
open _root_.SSGRoute

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The two descriptions of the level inertia agree.**  The elements of `Gal(M/k)` acting
trivially on the prime `P` of `𝓞 M` below the place `B` of `Ω` are exactly the elements whose
restriction to `M` acts trivially on the residue field of `P`. -/
theorem mem_inertia_levelPrime_iff_isTrivialAtLevel
    (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (g : Ω ≃ₐ[k] Ω) :
    AlgEquiv.restrictNormalHom L g ∈
        Ideal.inertia (↥L ≃ₐ[k] ↥L) (levelPrime k Ω B hB L).asIdeal ↔
      IsTrivialAtLevel k Ω B hB L g := by
  rw [IsTrivialAtLevel, NK.FrobeniusBridge.IsTrivialOnResidueAtLevel, AddSubgroup.mem_inertia]
  refine forall_congr' fun x => ?_
  have hsmul : (AlgEquiv.restrictNormalHom L g) • x =
      galRestrict (NumberField.RingOfIntegers k) k ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom L g) x := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [algebraMap_galRestrict_apply, algebraMap.smul']
    rfl
  rw [hsmul]
  exact Iff.rfl

/-! ## The stabiliser of a prime and the stabiliser of its valuation ring

These are copies of `private` lemmas of `Submission.Work.SSGRoute.decomp_mod_inertia_cyclic`
(and `levelSub_commutator_and_generator`), for a general finite Galois extension `L/K` of number
fields. -/

/-- The action on the ring of integers by `galRestrict` is the canonical `MulSemiringAction`. -/
private theorem galRestrict_coe_eq_toRingHom' {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (τ : L ≃ₐ[K] L) :
    (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) =
      MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) τ := by
  ext y
  rw [MulSemiringAction.toRingHom_apply]
  change algebraMap (𝓞 L) L (((galRestrict (𝓞 K) K L (𝓞 L)) τ) y) =
    algebraMap (𝓞 L) L (τ • y)
  rw [algebraMap_galRestrict_apply, algebraMap.smul']
  rfl

/-- The stabiliser of a prime equals the stabiliser of its valuation ring. -/
private theorem placeSmul_eq_iff_smul_asIdeal' {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[K] L) :
    Submission.NeukirchUchida.Local.placeSmul τ P = P ↔ τ • P.asIdeal = P.asIdeal := by
  constructor
  · intro h
    have h2 : Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) P.asIdeal = P.asIdeal := by
      conv_rhs => rw [← congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h]
      rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    rw [Ideal.pointwise_smul_def, ← galRestrict_coe_eq_toRingHom']
    exact h2
  · intro h
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Submission.NeukirchUchida.Local.placeSmul_asIdeal]
    rw [Ideal.pointwise_smul_def, ← galRestrict_coe_eq_toRingHom'] at h
    exact h

/-- The stabiliser of a prime ideal is contained in the stabiliser of its valuation ring. -/
private theorem stabilizer_asIdeal_le_stabilizer_valuationSubringAtPrime' {K L : Type*} [Field K]
    [Field L] [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal ≤
      MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) := by
  intro τ hτ
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  have hmap : Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) P.asIdeal = P.asIdeal := by
    rw [galRestrict_coe_eq_toRingHom', ← Ideal.pointwise_smul_def]
    exact hτ
  exact Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
    P P τ hmap.symm

/-- The stabiliser of the valuation ring of a prime is contained in the stabiliser of the prime
ideal. -/
private theorem stabilizer_valuationSubringAtPrime_le_stabilizer_asIdeal' {K L : Type*} [Field K]
    [Field L] [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) ≤
      MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal := by
  intro τ hτ
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  have h1 : τ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) P :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      P τ).mp hτ
  rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup] at h1
  exact (placeSmul_eq_iff_smul_asIdeal' P τ).mp h1

/-- **The level subgroup is the preimage of the inertia subgroup.**  The elements of the
decomposition group `D_A` whose restriction to the level `M` acts trivially on `𝓞 M ⧸ P` are
exactly the elements of the level subgroup `levelSub A M`. -/
theorem levelSub_comap_eq_inertia_comap
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    (Work.SSGRoute.levelSub A M).comap (Subgroup.subtype (SSGRoute.decomp k A)) =
      (Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).comap
        ((AlgEquiv.restrictNormalHom M).comp (Subgroup.subtype (SSGRoute.decomp k A))) := by
  haveI hsep : IsSepClosure k Ω := inferInstance
  ext δ
  rw [Subgroup.mem_comap, Subgroup.mem_comap]
  constructor
  · intro h
    rw [show ((AlgEquiv.restrictNormalHom M).comp (Subgroup.subtype (SSGRoute.decomp k A))) δ
        = AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω) from rfl]
    rw [AddSubgroup.mem_inertia]
    intro x
    have hyB : algebraMap ↥M Ω (x : ↥M) ∈ A := by
      have hx := ringOfIntegers_mem_of_isFinPlace_k k Ω A hA M x
      rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M Ω] at hx
      exact hx
    have hval := h.2 (⟨(x : ↥M), (ValuationSubring.mem_comap).mpr hyB⟩ :
      ↥(A.comap (algebraMap ↥M Ω)))
    refine (primeOfLevel_mem_iff_k k Ω A hA M
      ((AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω)) • x - x)).mpr ?_
    have hsmul : (AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω)) • x =
        galRestrict (NumberField.RingOfIntegers k) k ↥M (NumberField.RingOfIntegers ↥M)
          (AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω)) x := by
      apply NumberField.RingOfIntegers.coe_injective
      rw [algebraMap_galRestrict_apply, algebraMap.smul']
      rfl
    have key : algebraMap (NumberField.RingOfIntegers ↥M) Ω
        (galRestrict (NumberField.RingOfIntegers k) k ↥M (NumberField.RingOfIntegers ↥M)
          (AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω)) x) =
        (δ : Ω ≃ₐ[k] Ω) (algebraMap (NumberField.RingOfIntegers ↥M) Ω x) := by
      rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M Ω,
        algebraMap_galRestrict_apply]
      exact AlgEquiv.restrictNormalHom_apply M (δ : Ω ≃ₐ[k] Ω)
        (algebraMap (NumberField.RingOfIntegers ↥M) ↥M x)
    rw [hsmul, map_sub, key, IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M Ω]
    exact hval
  · intro h
    have h' : AlgEquiv.restrictNormalHom M (δ : Ω ≃ₐ[k] Ω) ∈
        Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal := h
    have htriv : IsTrivialAtLevel k Ω A hA M (δ : Ω ≃ₐ[k] Ω) :=
      (mem_inertia_levelPrime_iff_isTrivialAtLevel A hA M (δ : Ω ≃ₐ[k] Ω)).mp h'
    refine ⟨δ.2, fun x => ?_⟩
    exact valuation_sub_lt_one_of_isTrivialAtLevel A hA M (δ : Ω ≃ₐ[k] Ω) δ.2 htriv
      (x : ↥M).2 ((ValuationSubring.mem_comap).mp x.2)

/-- **The restriction `D_A → Gal(M/k)` has image the decomposition group of `P`.** -/
theorem range_restrictNormalHom_eq_stabilizer
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ((AlgEquiv.restrictNormalHom M).comp (Subgroup.subtype (SSGRoute.decomp k A))).range =
      MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal := by
  haveI hsep : IsSepClosure k Ω := inferInstance
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hgalO : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  have hspec : A.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
        (Work.SSGRoute.levelPrime k Ω A hA M) :=
    NK.Reconstruct.primeOfLevel_spec A M (NK.Reconstruct.comap_level_ne_top hA M)
  have hV : (SSGRoute.decomp k A).map (AlgEquiv.restrictNormalHom M) =
      MulAction.stabilizer (↥M ≃ₐ[k] ↥M)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
          (Work.SSGRoute.levelPrime k Ω A hA M)) := by
    rw [← hspec]
    refine le_antisymm ?_ ?_
    · intro g hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨σ, hσ, rfl⟩ := hg
      rw [MulAction.mem_stabilizer_iff]
      have hcom := Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A σ M
      rw [MulAction.mem_stabilizer_iff.mp hσ] at hcom
      exact hcom.symm
    · intro g hg
      obtain ⟨σ, hσ, hres⟩ :=
        Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
          A hA M g hg
      exact Subgroup.mem_map.mpr ⟨σ, hσ, hres⟩
  have hmap : (SSGRoute.decomp k A).map (AlgEquiv.restrictNormalHom M) =
      MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal :=
    hV.trans (le_antisymm
      (stabilizer_asIdeal_le_stabilizer_valuationSubringAtPrime'
        (Work.SSGRoute.levelPrime k Ω A hA M))
      (stabilizer_valuationSubringAtPrime_le_stabilizer_asIdeal'
        (Work.SSGRoute.levelPrime k Ω A hA M))).symm
  have hrange : (SSGRoute.decomp k A).map (AlgEquiv.restrictNormalHom M) =
      ((AlgEquiv.restrictNormalHom M).comp (Subgroup.subtype (SSGRoute.decomp k A))).range := by
    ext g
    rw [Subgroup.mem_map, MonoidHom.mem_range]
    exact ⟨fun ⟨x, hx, hxg⟩ => ⟨⟨x, hx⟩, hxg⟩,
      fun ⟨y, hy⟩ => ⟨(y : Ω ≃ₐ[k] Ω), y.2, hy⟩⟩
  rw [← hrange, hmap]

/-- **The index of the inertia subgroup in the decomposition group is the inertia degree.** -/
theorem inertia_relIndex_stabilizer_eq_inertiaDeg
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    (Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).relIndex
        (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) =
      (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  classical
  haveI hsep : IsSepClosure k Ω := inferInstance
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGal : IsGaloisGroup (↥M ≃ₐ[k] ↥M) (NumberField.RingOfIntegers k)
      (NumberField.RingOfIntegers ↥M) :=
    IsGaloisGroup.of_isFractionRing (↥M ≃ₐ[k] ↥M) (NumberField.RingOfIntegers k)
      (NumberField.RingOfIntegers ↥M) k ↥M
  haveI hlie : (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf A hA).asIdeal :=
    NK.ResidueFrob.primeOfLevel_liesOver
      (⟨A, (hA : A.comap (algebraMap k Ω) ≠ ⊤)⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω) M
  haveI hperf : PerfectField (Submission.NeukirchUchida.primeOf A hA).asIdeal.ResidueField := by
    haveI : Finite (NumberField.RingOfIntegers k ⧸
        (Submission.NeukirchUchida.primeOf A hA).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
    infer_instance
  have hcard : Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) =
      Nat.card (Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) *
      (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Ideal.card_stabilizer_eq_card_inertia_mul_finrank
      (Submission.NeukirchUchida.primeOf A hA).asIdeal (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal
  have hc : Nat.card ((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)) =
      Nat.card (Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := ↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)).toEquiv
  have hmul : Nat.card ((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)) *
      ((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)).index =
      Nat.card (MulAction.stabilizer (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) :=
    Subgroup.card_mul_index _
  have h1 : Nat.card ((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)) *
      ((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)).index =
      Nat.card ((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)) *
      (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [hmul, hc, hcard]
  haveI : Nonempty ↥((Ideal.inertia (↥M ≃ₐ[k] ↥M)
        (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal).subgroupOf
      (MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal)) := ⟨1⟩
  exact Nat.mul_left_cancel Nat.card_pos h1

/-- **The index of the level subgroup in the decomposition group is the inertia degree.** -/
theorem levelSub_comap_index_eq_inertiaDeg
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ((Work.SSGRoute.levelSub A M).comap (Subgroup.subtype (SSGRoute.decomp k A))).index =
      (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  have h1 := levelSub_comap_eq_inertia_comap A hA M
  have h3 := range_restrictNormalHom_eq_stabilizer A hA M
  rw [h1, Subgroup.index_comap, h3]
  exact inertia_relIndex_stabilizer_eq_inertiaDeg A hA M

end Work.SSGRoute
