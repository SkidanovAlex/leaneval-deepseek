import Mathlib
import Submission.NK.RamificationAdic.exists_valuationRingData
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.Ramification.Defs
import Submission.NK.RamificationDeep.UnitMap
import Submission.NK.RamificationDeep.RamificationDeterminesSubfields
import Submission.NK.RamificationDeep.WildInertiaUnconditional
import Submission.NK.TameStructureDeep.Tame.mem_tameClosure_of_pow_mem_unramifiedClosure
import Submission.NK.TameStructureDeep.Tame.InertiaFieldAux
import Submission.NK.TameStructureDeep.Tame.galoisData_fixedField_extendScalars_mulEquiv_quotient_ramificationSubgroup
import Submission.NK.TameStructureDeep.Tame.isCyclic_and_card_dvd_ramificationSubgroup_quotient
import Submission.NK.TameStructureDeep.Tame.primitiveRoots_finrank_of_dvd_card_residueField_sub_one
import Submission.NK.TameStructureDeep.Tame.le_comap_tameClosure_of_cyclic_extendScalars

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

/-- **The fixed field of the wild inertia is tamely ramified.**

Let `κ = K_𝔭` be the `𝔭`-adic completion of a number field `K`, `K'` a separable closure of `κ`,
`p = resCharAt 𝔭` its residue characteristic, `π` a uniformiser of `κ`, and
`T = κ^{tr} = tameClosure p π = κ^{ur}(π^{1/n} : p ∤ n)` the maximal tamely ramified extension.

Let `M/κ` be a finite dimensional Galois extension inside `K'`, and `A` a Galois-stable
discrete valuation ring of `M` (`hdec : A.decompositionSubgroup κ = ⊤`), Henselian, with finite
residue field of cardinality `p ^ f`.  Write `G_i = ramificationSubgroup A i` for the higher
ramification subgroups and assume that the *inertia field* is unramified: `M^{G_0} ⊆ κ^{ur}`
(the classical statement `inertiaFixedField_le_unramifiedClosure`, supplied here as an explicit
hypothesis so that this result isolates the Kummer-theoretic content).

Then the fixed field of the *wild* inertia `G_1` is tamely ramified: `M^{G_1} ⊆ κ^{tr}`, i.e.
`M^{G_1} ⊆ M ∩ κ^{tr}`.

**Route.**  Put `L = M^{G_1}`, `F = M^{G_0}`; thus `F ⊆ κ^{ur}` by hypothesis, `μ_e ⊆ F` for
`e = [L : F]` (lift a generator of `(A ⧸ 𝔪_A)^×` to a primitive `(#(A ⧸ 𝔪_A) - 1)`-st root of
unity, using Henselianity; the inertia `G_0` fixes it, so it lies in `F`), and `G_0/G_1`
embeds into the cyclic group `(A ⧸ 𝔪_A)^×`, so `Gal(L/F)` — a quotient of `G_0/G_1` — is cyclic.
Kummer theory (`exists_root_adjoin_eq_top_of_isCyclic`) gives `L = F(α)` with `α^e ∈ F ⊆ κ^{ur}`;
finally `mem_tameClosure_of_pow_mem_unramifiedClosure` (the Kummer computation over `κ^{ur}`)
gives `α ∈ T`, whence `L = F(α) ⊆ T` since `F ⊆ κ^{ur} ⊆ T`. -/
theorem fixedField_wildInertia_le_tameClosure_of_inertia_le_unramified {K : Type*} [Field K]
    [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A] [HenselianLocalRing A]
    (hdec : A.decompositionSubgroup (𝔭.adicCompletion K) = ⊤)
    (hcard : ∃ f : ℕ, Nat.card (IsLocalRing.ResidueField A) =
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f)
    (hU : (IntermediateField.fixedField
        (((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0).map
          (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
            Subgroup (M ≃ₐ[𝔭.adicCompletion K] M))).map (IntermediateField.val M) ≤
      NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)) :
    (IntermediateField.fixedField
        (((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 1).map
          (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
            Subgroup (M ≃ₐ[𝔭.adicCompletion K] M))).map (IntermediateField.val M) ≤
      NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) := by
  classical
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  -- ### The residue field of `A` is finite
  obtain ⟨f, hfcard⟩ := hcard
  haveI hFinRes : Finite (IsLocalRing.ResidueField A) :=
    (Nat.card_ne_zero.mp (by rw [hfcard]; exact pow_ne_zero f hp.ne_zero)).2
  have hfpos : 0 < f := by
    haveI hft : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
    have h1 : 1 < Nat.card (IsLocalRing.ResidueField A) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    by_contra h
    rw [Nat.eq_zero_of_not_pos h, pow_zero] at hfcard
    omega
  -- ### The inertia field `F` and the fixed field `L` of the wild inertia
  set F : IntermediateField (𝔭.adicCompletion K) M :=
    IntermediateField.fixedField
      (((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0).map
        (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
          Subgroup (M ≃ₐ[𝔭.adicCompletion K] M)) with hF
  set L : IntermediateField (𝔭.adicCompletion K) M :=
    IntermediateField.fixedField
      (((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 1).map
        (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype) :
          Subgroup (M ≃ₐ[𝔭.adicCompletion K] M)) with hL
  have hFL : F ≤ L := IntermediateField.fixedField_le
    (Subgroup.map_mono (f := (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype)
      (NK.Ramification.ramificationSubgroup_le_ramificationSubgroup
        (K := 𝔭.adicCompletion K) A (Nat.zero_le 1)))
  -- ### The Galois data of `L/F`
  obtain ⟨hfin, hgal, hΦne⟩ :=
    galoisData_fixedField_extendScalars_mulEquiv_quotient_ramificationSubgroup
      (κ := 𝔭.adicCompletion K) A hdec hFL
  haveI hfinI : FiniteDimensional ↥F ↥(IntermediateField.extendScalars hFL) := hfin
  haveI hgalI : IsGalois ↥F ↥(IntermediateField.extendScalars hFL) := hgal
  obtain ⟨Φ⟩ := hΦne
  obtain ⟨hcycQ, hdvdQ⟩ :=
    isCyclic_and_card_dvd_ramificationSubgroup_quotient (κ := 𝔭.adicCompletion K) A hdec
  have hcyc : IsCyclic
      (↥(IntermediateField.extendScalars hFL) ≃ₐ[↥F] ↥(IntermediateField.extendScalars hFL)) :=
    (MulEquiv.isCyclic Φ).mpr hcycQ
  have hcardGal : Nat.card
        (↥(IntermediateField.extendScalars hFL) ≃ₐ[↥F] ↥(IntermediateField.extendScalars hFL)) =
      Nat.card ((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0)) :=
    Nat.card_congr Φ.toEquiv
  have hfr : Module.finrank ↥F ↥(IntermediateField.extendScalars hFL) =
      Nat.card ((NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 0)) := by
    rw [← IsGalois.card_aut_eq_finrank ↥F ↥(IntermediateField.extendScalars hFL)]
    exact hcardGal
  have hdvd : Module.finrank ↥F ↥(IntermediateField.extendScalars hFL) ∣
      Nat.card (IsLocalRing.ResidueField A) - 1 := by
    rw [hfr]
    exact hdvdQ
  have he0 : 0 < Module.finrank ↥F ↥(IntermediateField.extendScalars hFL) :=
    Module.finrank_pos
  -- `p` does not divide `#(A ⧸ 𝔪) - 1 = p ^ f - 1`, hence does not divide `[L : F]`
  have hpf : ¬ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
      Nat.card (IsLocalRing.ResidueField A) - 1 := by
    intro hd
    rw [hfcard] at hd
    have hsub : (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f -
          ((NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f - 1) :=
      Nat.dvd_sub (dvd_pow_self _ hfpos.ne') hd
    rw [Nat.sub_sub_self (Nat.one_le_pow f _ hp.pos)] at hsub
    exact hp.not_dvd_one hsub
  have hnp : ¬ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
      Module.finrank ↥F ↥(IntermediateField.extendScalars hFL) :=
    fun h => hpf (h.trans hdvd)
  -- ### The roots of unity of order `[L : F]` lie in `F`
  have hμ := primitiveRoots_finrank_of_dvd_card_residueField_sub_one
    (κ := 𝔭.adicCompletion K) A he0 hdvd
  -- ### `F ⊆ κ^{ur}`
  have hFU : ∀ y : ↥F, ((y : M) : K') ∈
      NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
    intro y
    exact hU ⟨y.1, y.2, rfl⟩
  -- ### Kummer theory and the tameness conclusion
  have hLN : L ≤ IntermediateField.comap (IntermediateField.val M)
      (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) :=
    le_comap_tameClosure_of_cyclic_extendScalars 𝔭 hπ M F L hFL hfin hgal hcyc hμ hnp hFU
  exact (IntermediateField.gc_map_comap (IntermediateField.val M)).l_le hLN

end NK.TameStructureDeep.Tame
