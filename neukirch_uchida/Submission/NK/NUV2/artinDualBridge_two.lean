import Mathlib
import Submission.NK.NUV2.TowerRank.artinDualBridge
import Submission.NK.NUV2.ADB.artinConductor_cyclic_exists
import Submission.NK.GlobalCFTdeep.Existence
import Submission.NK.NUV2.ArtinBridge.takagiExistence

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


/-!
# The target from the ideal-theoretic reciprocity law

The target `NK.NUV2.artinDualBridge_two` is

  `ArtinDualBridge Ω 2`, i.e. `rank_{ℤ_2} Hom_cts(Γ_K^Ω, ℤ_2) = rank_{ℤ_2} Hom_cts(C_K, ℤ_2)`
  for every number field `K ⊆ Ω`.

The assembly is on disk:

* `NK.NUV2.TowerRank.Bridge.artinDualBridge_of_artinReciprocityIdeal` produces it from the
  ideal-theoretic reciprocity law `NK.CFTLib.ArtinReciprocityIdeal` and the existence theorem
  `NK.GlobalCFT.ExistenceTheorem` (Takagi's existence theorem plus the norm-group
  correspondence).  The canonicity input `LevelPairIso` is *derived* from the reciprocity law by
  the proved `NK.NUV2.TowerRank.levelPairIso_of_artinReciprocityIdeal`;
* Takagi's existence theorem is the proved `NK.NUV2.ArtinBridge.takagiExistence`;
* the norm-group correspondence is proved here from the reciprocity law: the canonical idèlic
  Artin map of an abelian level `L/K` — built in
  `Submission/Work/NUV2/TowerRank/levelPairIso_of_artinReciprocityIdeal.lean` — is compatible with
  the restriction to an intermediate field `L' ⊆ L`, so the preimage of `Gal(L/L')` under the
  Artin map is exactly `N_{L'/K}C_{L'}`.  The Galois correspondence then produces, for every
  subgroup `N ⊇ N_{L/K}C_L`, a field `L'` with `N_{L'/K}C_{L'} = N`.
-/

namespace NK.NUV2

open NK.GlobalCFT (Idele IdeleClassGroup)
open scoped NumberField

/-- **The norm-group correspondence from the ideal-theoretic reciprocity law.**

Let `L/K` be a finite abelian extension of number fields and `N ≤ C_K` a subgroup containing the
norm group `N_{L/K}C_L`.  Then `N` is the norm group of a finite abelian extension `L'/K`.

The proof uses the *canonical* (Frobenius-normalised) idèlic Artin map `art : 𝕀 K →* Gal(L/K)`
attached to the reciprocity law `h`, with kernel `Kˣ·N_{L/K}𝕀 L`
(`NK.NUV2.TowerRank.exists_artData`), and its compatibility with the restriction to an
intermediate field `L' ⊆ L` (`NK.NUV2.TowerRank.ideleArtin_restrictNormalHom`, itself deduced from
the functoriality of the ideal-theoretic Artin symbol).  The norm group of `L'` is then the
preimage of `Gal(L/L')` under `art`, and the Galois correspondence finishes. -/
theorem normGroupCorrespondence_of_artinReciprocityIdeal (h : NK.CFTLib.ArtinReciprocityIdeal)
    (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFTdeep.NormGroupCorrespondence.{0, 0, 0} K where
  exists_normSubgroup_eq := by
    intro L _ _ _ _ _ _ N hN
    classical
    have hFC : NK.GlobalCFTdeep.FundamentalClassElement := NK.CFTLib.fcElement_of_arl h
    have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    obtain ⟨m, hm, hram, hprinc⟩ := h K L hcomm
    obtain ⟨art, hart, hker, hsurj, hfrob⟩ :=
      NK.NUV2.TowerRank.exists_artData (K := K) (F := L) hFC hcomm m hm hram hprinc
    -- the induced map `C_K →* Gal(L/K)`
    have hprin_le : Idele.principalSubgroup K ≤ art.ker := by
      rw [hker]; exact le_sup_left
    let f : IdeleClassGroup K →* Gal(L/K) :=
      QuotientGroup.lift (Idele.principalSubgroup K) art hprin_le
    have hf : ∀ x : Idele K, f (IdeleClassGroup.mk K x) = art x :=
      fun x => QuotientGroup.lift_mk' _ _ x
    have hkerf : f.ker = Idele.normClassSubgroup K L := by
      rw [show f = QuotientGroup.lift (Idele.principalSubgroup K) art hprin_le from rfl,
        QuotientGroup.ker_lift, hker, Subgroup.map_sup,
        show Subgroup.map (QuotientGroup.mk' (Idele.principalSubgroup K))
            (Idele.principalSubgroup K) = ⊥ from
          (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm),
        bot_sup_eq]
      rfl
    have hkerle : f.ker ≤ N := by rw [hkerf]; exact hN
    -- the subgroup of `Gal(L/K)` cut out by `N`, and its fixed field
    let H : Subgroup Gal(L/K) := N.map f
    haveI hHn : H.Normal := Subgroup.normal_of_isMulCommutative H
    let L' : IntermediateField K L := IntermediateField.fixedField H
    haveI hL'fd : FiniteDimensional K ↥L' := IntermediateField.finiteDimensional_left L'
    haveI hL'gal : IsGalois K ↥L' := IsGalois.of_fixedField_normal_subgroup H
    haveI hL'nor : Normal K ↥L' := hL'gal.to_normal
    haveI hL'nf : NumberField ↥L' :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L'
    have hHker : H = (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) L').ker := by
      rw [IntermediateField.restrictNormalHom_ker L',
        show L' = IntermediateField.fixedField H from rfl,
        IntermediateField.fixingSubgroup_fixedField H]
    -- `N` is the preimage of `H`
    have hNH : N = Subgroup.comap f H := by
      refine le_antisymm ?_ ?_
      · intro c hc
        exact Subgroup.mem_map_of_mem f hc
      · intro c hc
        rw [Subgroup.mem_comap] at hc
        obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.mp hc
        have h1 : n⁻¹ * c ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, inv_mul_cancel]
        have h2 : n⁻¹ * c ∈ N := hkerle h1
        have h3 : c = n * (n⁻¹ * c) := by group
        rw [h3]
        exact N.mul_mem hn h2
    -- `Gal(L'/K)` is commutative (a quotient of the abelian `Gal(L/K)`)
    haveI hq : IsMulCommutative (Gal(L/K) ⧸ H) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).mpr (by
        rw [_root_.commutator_eq_bot]; exact bot_le)
    haveI hL'comm : IsMulCommutative (Gal(↥L'/K)) := by
      refine IsMulCommutative.of_comm fun a b => ?_
      have h1 : (IsGalois.normalAutEquivQuotient (K := K) (L := L) H).symm (a * b)
          = (IsGalois.normalAutEquivQuotient (K := K) (L := L) H).symm (b * a) := by
        rw [map_mul, map_mul]
        exact hq.is_comm.comm _ _
      exact (IsGalois.normalAutEquivQuotient (K := K) (L := L) H).symm.injective h1
    have hcomm' : ∀ a b : Gal(↥L'/K), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    -- the reciprocity law and the idèlic Artin map at the subfield
    have hram' : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥L') = 1 :=
      fun p hp =>
        NK.NUV2.TowerRank.ramificationIdxIn_eq_one_of_intermediateField L' p (hram p hp)
    have hprinc' : NK.CFTLib.artinKillsPrincipal K ↥L' m :=
      NK.NUV2.TowerRank.artinKillsPrincipal_of_intermediateField hcomm L' hcomm' hram hprinc
    obtain ⟨art', hart', hker', hsurj', hfrob'⟩ :=
      NK.NUV2.TowerRank.exists_artData (K := K) (F := ↥L') hFC hcomm' m hm hram' hprinc'
    -- the two Artin maps are intertwined by restriction
    have hcompat : ∀ x : Idele K,
        AlgEquiv.restrictNormalHom (F := K) (K₁ := L) L' (art x) = art' x := by
      intro x
      rw [hart x, hart' x]
      exact NK.NUV2.TowerRank.ideleArtin_restrictNormalHom L' hcomm hcomm' m hm hram x
    -- the norm group of `L'` is `N`
    have hnorm : Idele.normClassSubgroup K ↥L' = N := by
      rw [hNH]
      refine le_antisymm ?_ ?_
      · intro c hc
        rw [show Idele.normClassSubgroup K ↥L' =
            (Idele.normImage K ↥L').map (IdeleClassGroup.mk K) from rfl] at hc
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
        rw [Subgroup.mem_comap, hf y, hHker, MonoidHom.mem_ker, hcompat y]
        rw [← MonoidHom.mem_ker, hker']
        exact Subgroup.mem_sup_right hy
      · intro c hc
        rw [Subgroup.mem_comap] at hc
        obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
        rw [hf x, hHker, MonoidHom.mem_ker, hcompat x] at hc
        rw [← MonoidHom.mem_ker, hker'] at hc
        have hmem : IdeleClassGroup.mk K x ∈
            (Idele.normImage K ↥L').map (IdeleClassGroup.mk K) := by
          have h1 : IdeleClassGroup.mk K x ∈ Subgroup.map (IdeleClassGroup.mk K)
              (Idele.principalSubgroup K ⊔ Idele.normImage K ↥L') :=
            Subgroup.mem_map_of_mem _ hc
          rwa [Subgroup.map_sup,
            show Subgroup.map (IdeleClassGroup.mk K) (Idele.principalSubgroup K) = ⊥ from
              (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm),
            bot_sup_eq] at h1
        exact hmem
    exact ⟨↥L', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hnorm⟩

/-- **The existence theorem from the ideal-theoretic reciprocity law.**  Takagi's existence theorem
is the proved `NK.NUV2.ArtinBridge.takagiExistence`; the norm-group correspondence is proved
above. -/
theorem existenceTheorem_of_artinReciprocityIdeal (h : NK.CFTLib.ArtinReciprocityIdeal)
    (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFT.ExistenceTheorem.{0, 0} K :=
  NK.GlobalCFTdeep.existenceTheorem_of_takagi (NK.NUV2.ArtinBridge.takagiExistence K)
    (normGroupCorrespondence_of_artinReciprocityIdeal h K)

/-- **`ℓ`-adic Artin reciprocity in dual form at `ℓ = 2`.**

This is `NK.NUV2.TowerRank.Bridge.artinDualBridge_of_artinReciprocityIdeal` applied to the
ideal-theoretic reciprocity law `NK.CFTLib.artinReciprocityIdeal` and the existence theorem
proved above: the canonicity input `LevelPairIso` is derived from the reciprocity law by
`NK.NUV2.TowerRank.levelPairIso_of_artinReciprocityIdeal`, and the global fundamental class is
the proved `NK.CFTLib.fundamentalClassElement` (so the `hFC` hypothesis is not used). -/
theorem artinReciprocityIdeal_derived : NK.CFTLib.ArtinReciprocityIdeal :=
  NK.CFTLib.ArtinReciprocityIdeal_of_cyclicCase
    (fun K L _ _ _ _ _ _ _ _ => NK.NUV2.ADB.artinConductor_cyclic_exists K L)

theorem artinDualBridge_two (hFC : NK.GlobalCFTdeep.FundamentalClassElement) (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    NK.RankTheoryDeep.ArtinDualBridge Ω 2 :=
  NK.NUV2.TowerRank.Bridge.artinDualBridge_of_artinReciprocityIdeal
    artinReciprocityIdeal_derived
    (fun K _ _ => existenceTheorem_of_artinReciprocityIdeal artinReciprocityIdeal_derived K)
    Ω

end NK.NUV2
