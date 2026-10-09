import Mathlib
import Submission.Work.SSGRoute.pointwiseInstances
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NeukirchUchida.Local.DecompositionGroup
import Submission.NeukirchUchida.Local.Transitivity
import Mathlib.NumberTheory.RamificationInertia.Galois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped Pointwise

namespace Work.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# The index of the level subgroup times the inertia

This file proves `Work.SSGRoute.levelIndex`: for a finite place `A'` of `ℚ̄` and a finite normal
level `L/ℚ`, the index in the decomposition group `D_A` of the product of the level subgroup and
the global inertia subgroup is the inertia degree of the prime of `𝓞 L` below `A'`.

The proof splits into four independent statements:

* `levelSub_eq_comap_inertia` — `levelSubQBar` is the preimage of the inertia subgroup of `Gal(L/ℚ)`;
* `globalInertiaSub_le_levelSub` — the global inertia subgroup is contained in `levelSubQBar`;
* `range_eq_stab` — the range of the restriction `D_A → Gal(L/ℚ)` is the decomposition group of
  the prime of `𝓞 L` below `A'`;
* `inertia_index_in_stabilizer` — Mathlib's `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`
  gives `[D_P : I_P] = f`.
-/

instance instGaloisIntermediateField (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L]
    [Normal ℚ L] [NumberField ↥L] : IsGalois ℚ ↥L :=
  { to_normal := inferInstance, to_isSeparable := inferInstance }

/-- Transport of `Normal` along an equality of `Algebra` structures. -/
theorem normalTransport {A : Type*} [Field A] {a b : Algebra ℚ A} (h : a = b)
    (hn : @Normal ℚ A _ _ a) : @Normal ℚ A _ _ b := h ▸ hn

/-- The prime of `𝓞 L` below the finite place `A'` of `ℚ̄`. -/
noncomputable def levelPrimeQBar (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [Normal ℚ L] [NumberField ↥L] :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) :=
  NK.Reconstruct.primeOfLevel A'.1 L (NK.Reconstruct.comap_level_ne_top A'.2 L)

/-- **The action on the ring of integers is the `galRestrict` action.**  With the default
`MulSemiringAction (↥L ≃ₐ[ℚ] ↥L) (𝓞 ↥L)`, an automorphism `τ` acts on `𝓞 ↥L` by evaluation. -/
theorem smul_eq_galRestrict
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [NumberField ↥L]
    (τ : ↥L ≃ₐ[ℚ] ↥L) (x : NumberField.RingOfIntegers ↥L) :
    τ • x = galRestrict (NumberField.RingOfIntegers ℚ) ℚ ↥L (NumberField.RingOfIntegers ↥L) τ x := by
  apply NumberField.RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply, algebraMap.smul']
  rfl

/-- **The level-inertia condition is membership in the inertia subgroup of `Gal(L/ℚ)` at the
prime below the place.** -/
theorem isTrivialAtLevel_iff_mem_inertia
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] (g : ↥(SSGRoute.decomp ℚ A'.1)) :
    Work.SSGRoute.IsTrivialAtLevelQBar A' L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ↔
      AlgEquiv.restrictNormalHom L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ∈
        Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal := by
  constructor
  · intro h
    rw [AddSubgroup.mem_inertia]
    intro x
    rw [Submodule.mem_toAddSubgroup, smul_eq_galRestrict L
      (AlgEquiv.restrictNormalHom L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)) x]
    exact h x
  · intro h x
    rw [AddSubgroup.mem_inertia] at h
    have hx := h x
    rw [Submodule.mem_toAddSubgroup] at hx
    rw [smul_eq_galRestrict L
      (AlgEquiv.restrictNormalHom L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)) x] at hx
    exact hx

/-- `levelSubQBar` is the preimage in `D_A` of the inertia subgroup of `Gal(L/ℚ)` at the prime of
`𝓞 L` below `A`. -/
theorem levelSub_eq_comap_inertia
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] :
    Work.SSGRoute.levelSubQBar A' L =
      (Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).comap
      ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype _)) := by
  show Subgroup.closure {g : ↥(SSGRoute.decomp ℚ A'.1) |
      Work.SSGRoute.IsTrivialAtLevelQBar A' L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)} =
    (Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).comap
      ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype _))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    exact (isTrivialAtLevel_iff_mem_inertia A' L g).mp hg
  · intro g hg
    exact Subgroup.subset_closure ((isTrivialAtLevel_iff_mem_inertia A' L g).mpr hg)

/-- The global inertia subgroup is contained in the level subgroup. -/
theorem globalInertiaSub_le_levelSub
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] :
    Work.SSGRoute.globalInertiaSub A' ≤ Work.SSGRoute.levelSubQBar A' L := by
  show Subgroup.closure {g : ↥(SSGRoute.decomp ℚ A'.1) |
      SSGRoute.IsInertia ℚ A'.1 (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)} ≤
    Subgroup.closure {g : ↥(SSGRoute.decomp ℚ A'.1) |
      Work.SSGRoute.IsTrivialAtLevelQBar A' L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar)}
  apply (Subgroup.closure_le _).mpr
  intro g hg
  exact Subgroup.subset_closure
    ((isTrivialAtLevel_iff_mem_inertia A' L g).mpr
      (Work.SSGRoute.mem_inertia_of_isInertia L A'.1 A'.2 hg))

/-- The decomposition group of the level prime, computed inside `Gal(L/ℚ)`, is the stabiliser of
`(levelPrimeQBar A' L).asIdeal`. -/
theorem decompSub_eq_stab
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] :
    Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) (levelPrimeQBar A' L) =
      MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal := by
  apply Subgroup.ext
  intro σ
  rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup, MulAction.mem_stabilizer_iff]
  have hring : ((galRestrict (NumberField.RingOfIntegers ℚ) ℚ ↥L (NumberField.RingOfIntegers ↥L) σ :
        NumberField.RingOfIntegers ↥L ≃ₐ[NumberField.RingOfIntegers ℚ] NumberField.RingOfIntegers ↥L) :
      NumberField.RingOfIntegers ↥L →+* NumberField.RingOfIntegers ↥L)
      = MulSemiringAction.toRingHom (↥L ≃ₐ[ℚ] ↥L) (NumberField.RingOfIntegers ↥L) σ := by
    apply RingHom.ext
    intro x
    rw [MulSemiringAction.toRingHom_apply]
    exact (smul_eq_galRestrict L σ x).symm
  rw [show (σ • (levelPrimeQBar A' L).asIdeal) =
      Ideal.map (MulSemiringAction.toRingHom (↥L ≃ₐ[ℚ] ↥L)
        (NumberField.RingOfIntegers ↥L) σ) (levelPrimeQBar A' L).asIdeal from rfl, ← hring]
  rw [show (Submission.NeukirchUchida.Local.placeSmul σ (levelPrimeQBar A' L) = levelPrimeQBar A' L) ↔
      ((Submission.NeukirchUchida.Local.placeSmul σ (levelPrimeQBar A' L)).asIdeal =
        (levelPrimeQBar A' L).asIdeal) from
    ⟨fun h => by rw [h], fun h => IsDedekindDomain.HeightOneSpectrum.ext h⟩,
    Submission.NeukirchUchida.Local.placeSmul_asIdeal]

/-- The range of the restriction `D_A → Gal(L/ℚ)` is the decomposition group of the level
prime. -/
theorem range_eq_stab
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] :
    ((AlgEquiv.restrictNormalHom L).comp
        (Subgroup.subtype (SSGRoute.decomp ℚ A'.1))).range =
      MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal := by
  apply le_antisymm
  · intro τ hτ
    rw [MonoidHom.mem_range] at hτ
    obtain ⟨g, rfl⟩ := hτ
    have hmem : AlgEquiv.restrictNormalHom L (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ∈
        Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) (levelPrimeQBar A' L) := by
      refine @Submission.NeukirchUchida.Local.restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer
        ℚ SSGRoute.QBar Rat.instField Rat.numberField (AlgebraicClosure.instField ℚ)
        (inferInstanceAs (Algebra ℚ SSGRoute.QBar)) (inferInstanceAs (IsGalois ℚ SSGRoute.QBar))
        A'.1 L (inferInstanceAs (FiniteDimensional ℚ ↥L)) hN
        (levelPrimeQBar A' L)
        (NK.Reconstruct.primeOfLevel_spec A'.1 L (NK.Reconstruct.comap_level_ne_top A'.2 L))
        (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) g.2
    rw [decompSub_eq_stab] at hmem
    exact hmem
  · intro τ hτ
    have hτ' : τ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) (levelPrimeQBar A' L) := by
      rw [decompSub_eq_stab]; exact hτ
    have hplace : Submission.NeukirchUchida.Local.placeOf
        (Submission.NeukirchUchida.primeOf A'.1 A'.2) A'.1
        (Submission.NeukirchUchida.primeOf_spec A'.1 A'.2) L = levelPrimeQBar A' L := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (R := NumberField.RingOfIntegers ↥L) (K := ↥L)
      rw [← Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf
        (Submission.NeukirchUchida.primeOf A'.1 A'.2) A'.1
        (Submission.NeukirchUchida.primeOf_spec A'.1 A'.2) L]
      exact NK.Reconstruct.primeOfLevel_spec A'.1 L (NK.Reconstruct.comap_level_ne_top A'.2 L)
    have hτ'' : τ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ)
        (Submission.NeukirchUchida.Local.placeOf (Submission.NeukirchUchida.primeOf A'.1 A'.2) A'.1
          (Submission.NeukirchUchida.primeOf_spec A'.1 A'.2) L) := by
      rw [hplace]; exact hτ'
    rw [MonoidHom.mem_range]
    obtain ⟨σ, hσ, hres⟩ :=
      @Submission.NeukirchUchida.Local.exists_mem_stabilizer_restrictNormalHom_eq
        ℚ SSGRoute.QBar Rat.instField Rat.numberField (AlgebraicClosure.instField ℚ)
        (inferInstanceAs (Algebra ℚ SSGRoute.QBar)) (inferInstanceAs (IsGalois ℚ SSGRoute.QBar))
        (Submission.NeukirchUchida.primeOf A'.1 A'.2) A'.1
        (Submission.NeukirchUchida.primeOf_spec A'.1 A'.2) L
        (inferInstanceAs (FiniteDimensional ℚ ↥L))
        (normalTransport (Subsingleton.elim _ _) hN) ⟨τ, hτ''⟩
    exact ⟨⟨σ, hσ⟩, hres⟩

/-- **The index of the inertia subgroup in the decomposition group is the inertia degree.** -/
theorem inertia_index_in_stabilizer
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] :
    ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)).index
      = (levelPrimeQBar A' L).asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
  haveI hGal : IsGaloisGroup (↥L ≃ₐ[ℚ] ↥L) (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers ↥L) :=
    IsGaloisGroup.of_isFractionRing (↥L ≃ₐ[ℚ] ↥L) (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers ↥L) ℚ ↥L
  haveI hlie : (levelPrimeQBar A' L).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal := by
    have h := Work.SSGRoute.primeOfLevel_liesOver' L A'.1 A'.2
    simpa [levelPrimeQBar, NK.Reconstruct.comap_level_ne_top] using h
  haveI hperf : PerfectField (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal.ResidueField := by
    haveI : Finite (NumberField.RingOfIntegers ℚ ⧸
        (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
    infer_instance
  have hcard : Nat.card (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal) =
      Nat.card (Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal) *
      (levelPrimeQBar A' L).asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
    Ideal.card_stabilizer_eq_card_inertia_mul_finrank
      (Submission.NeukirchUchida.primeOf A'.1 A'.2).asIdeal (levelPrimeQBar A' L).asIdeal
  have hc : Nat.card ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)) =
      Nat.card (Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := ↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)).toEquiv
  have hmul : Nat.card ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)) *
      ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)).index =
      Nat.card (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal) :=
    Subgroup.card_mul_index _
  have h1 : Nat.card ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)) *
      ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)).index =
      Nat.card ((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)) *
      (levelPrimeQBar A' L).asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    rw [hmul, hc, hcard]
  haveI : Nonempty ↥((Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal).subgroupOf
      (MulAction.stabilizer (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal)) := ⟨1⟩
  exact Nat.mul_left_cancel Nat.card_pos h1

theorem levelIndex (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [Normal ℚ L]
    [NumberField ↥L] :
    (Work.SSGRoute.levelSubQBar A' L ⊔ Work.SSGRoute.globalInertiaSub A').index =
      (NK.Reconstruct.primeOfLevel A'.1 L (NK.Reconstruct.comap_level_ne_top A'.2 L)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers ℚ) := by
  have h1 := levelSub_eq_comap_inertia A' L
  have h2 := globalInertiaSub_le_levelSub A' L
  have h3 := range_eq_stab A' L
  have h4 := inertia_index_in_stabilizer A' L
  rw [sup_eq_left.mpr h2, h1, Subgroup.index_comap, h3]
  exact h4

end Work.SSGRoute
