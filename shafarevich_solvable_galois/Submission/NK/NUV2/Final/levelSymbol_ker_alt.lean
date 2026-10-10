import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.NUV2.Final.levelSymbol_ker_cyclic
import Submission.NK.NUV2.RouteE.levelCompat
import Submission.NK.NUV2.RouteF.transition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# L7: kernel and surjectivity of the level symbol

`NK.NUV2.Final.levelSymbol_ker` (the full L7) with the last step (`surjectivity`) carried out by
restricting to the subfield fixed by a subgroup `K ≥ Im θ` with cyclic Galois group
(`NK.NUV2.Final.exists_cyclic_quotient_of_ne_top`), where
`NK.NUV2.Final.levelSymbol_ker_cyclic` applies and the level symbols are compatible
(`NK.NUV2.RouteE.levelSymbol_restrict`).  The norm index theorem
(`Commons...natCard_quotient_units_range_norm_eq_finrank_of_abelian_local`) rules out the
contradiction `N_C = Fˣ` at the subfield.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.NUV2.Final

/-- `NK.NUV2.Final.exists_cyclic_quotient_of_ne_top` with the commutativity supplied as an
`IsMulCommutative` instance (a `Prop`-only class, so that no alternative group structure — and in
particular no alternative `Mul` — is installed in the ambient context). -/
theorem exists_cyclic_quotient_of_ne_top_of_isMulCommutative {G : Type} [Group G]
    [IsMulCommutative G] [Finite G] (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≠ ⊤ ∧ IsCyclic (G ⧸ K) := by
  haveI : IsCoatomic (Subgroup G) := inferInstance
  obtain ⟨K, hKmax, hHK⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH
  have hKne : K ≠ ⊤ := hKmax.ne_top
  haveI : K.Normal := Subgroup.normal_of_isMulCommutative K
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hKne)
  have hgne : (QuotientGroup.mk' K) g ≠ 1 := by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hg
  refine ⟨K, hHK, hKne, ?_⟩
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨QuotientGroup.mk' K g, ?_⟩
  have hsup : K ⊔ Subgroup.zpowers g = ⊤ := by
    rcases eq_or_lt_of_le (le_sup_left : K ≤ K ⊔ Subgroup.zpowers g) with h | h
    · exact absurd (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g)) hg
    · exact hKmax.lt_iff.mp h
  have hmap : Subgroup.map (QuotientGroup.mk' K) (K ⊔ Subgroup.zpowers g)
      = Subgroup.zpowers (QuotientGroup.mk' K g) := by
    have hbot : Subgroup.map (QuotientGroup.mk' K) K = ⊥ :=
      (Subgroup.map_eq_bot_iff K).mpr (le_of_eq (QuotientGroup.ker_mk' K).symm)
    rw [Subgroup.map_sup, hbot, bot_sup_eq]
    apply Subgroup.ext
    intro y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨n, by rw [← hxy, map_zpow]⟩
    · rintro ⟨n, hn⟩
      refine ⟨g ^ n, ?_, ?_⟩
      · rw [Subgroup.mem_zpowers_iff]
        exact ⟨n, rfl⟩
      · rw [map_zpow]; exact hn
  rw [← hmap, hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]

theorem levelSymbol_ker_alt {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {L : Type} [Field L] [Algebra (Q.adicCompletion K) L]
    [FiniteDimensional (Q.adicCompletion K) L] [IsGalois (Q.adicCompletion K) L]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) L) 2)]
    (hcomm : ∀ σ τ : L ≃ₐ[Q.adicCompletion K] L, σ * τ = τ * σ)
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) L) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) L) 2)) :
    MonoidHom.ker (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := L) hcomm u hu)
        = NK.LocalReciprocity.normGroup (Q.adicCompletion K) L ∧
      Function.Surjective
        (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := L) hcomm u hu) := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[Q.adicCompletion K] L) := ⟨Std.Commutative.mk hcomm⟩
  let θ : (Q.adicCompletion K)ˣ →* (L ≃ₐ[Q.adicCompletion K] L) :=
    NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := L) hcomm u hu
  have hθ : θ = NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := L) hcomm u hu := rfl
  -- ## Step 0: the norm group is contained in the kernel
  have hnorm_le : NK.LocalReciprocity.normGroup (Q.adicCompletion K) L ≤ MonoidHom.ker θ := by
    intro a ha
    rw [MonoidHom.mem_ker]
    rw [hθ]
    apply NK.NUV2.RouteE.doubleDual_injective hcomm
    intro χ'
    rw [NK.NUV2.RouteE.levelSymbol_apply]
    show NK.NUV2.RouteE.charValue u hu a χ' = χ' (Additive.ofMul 1)
    rw [show NK.NUV2.RouteE.charValue u hu a χ'
        = NK.NUV2.RouteC.invariantOf u hu ((groupCohomology.map
            (MonoidHom.id (L ≃ₐ[Q.adicCompletion K] L))
            (NK.NUV2.RouteC.powHom (F := Q.adicCompletion K) (E := L) a) 2)
            (NK.NUV2.RouteC.deltaHomChar (L ≃ₐ[Q.adicCompletion K] L) χ')) from rfl]
    rw [show (groupCohomology.map (MonoidHom.id (L ≃ₐ[Q.adicCompletion K] L))
        (NK.NUV2.RouteC.powHom (F := Q.adicCompletion K) (E := L) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (L ≃ₐ[Q.adicCompletion K] L) χ') = 0 from
      NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup χ' a ha,
      map_zero]
    simp
  -- ## Step 2: the level symbol is surjective
  have hsurj : Function.Surjective θ := by
    by_contra hcon
    have hHne : MonoidHom.range θ ≠ ⊤ := fun htop => hcon (MonoidHom.range_eq_top.mp htop)
    let H0 : Subgroup (L ≃ₐ[Q.adicCompletion K] L) := MonoidHom.range θ
    obtain ⟨K', hHK', hK'ne, hcycK'⟩ :=
      NK.NUV2.Final.exists_cyclic_quotient_of_ne_top_of_isMulCommutative H0 hHne
    haveI hK'normal : K'.Normal := Subgroup.normal_of_isMulCommutative K'
    let C : IntermediateField (Q.adicCompletion K) L := IntermediateField.fixedField K'
    haveI hCgal : IsGalois (Q.adicCompletion K) ↥C :=
      IsGalois.of_fixedField_normal_subgroup (K := Q.adicCompletion K) (H := K')
    have hcommC : ∀ σ τ : ↥C ≃ₐ[Q.adicCompletion K] ↥C, σ * τ = τ * σ := by
      intro σ τ
      obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := Q.adicCompletion K)
        (K₁ := ↥C) L σ
      obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := Q.adicCompletion K)
        (K₁ := ↥C) L τ
      rw [← map_mul, ← map_mul, hcomm]
    have hcycC : IsCyclic (↥C ≃ₐ[Q.adicCompletion K] ↥C) := by
      have e := IsGalois.normalAutEquivQuotient (K := Q.adicCompletion K) (L := L) K'
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    haveI hfinC : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2) :=
      Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
        (K := K) Q (F := Q.adicCompletion K) (E := ↥C) (Group.isSolvable_of_comm hcommC)
    have h1C : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2)
        = Module.finrank (Q.adicCompletion K) ↥C :=
      (NK.NUV2.RouteE.h2_cyclic_level (K := K) Q
        (F := Q.adicCompletion K) (E := ↥C) hcommC).1
    have hcard : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) L) 2)
        = Nat.card (L ≃ₐ[Q.adicCompletion K] L) := by
      rw [(NK.NUV2.RouteE.h2_cyclic_level (K := K) Q
        (F := Q.adicCompletion K) (E := L) hcomm).1]
      exact (IsGalois.card_aut_eq_finrank (Q.adicCompletion K) L).symm
    have hcardK : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2)
        = K'.index := by
      rw [h1C, ← IsGalois.card_aut_eq_finrank (Q.adicCompletion K) ↥C,
        Subgroup.index_eq_card]
      exact (Nat.card_congr (IsGalois.normalAutEquivQuotient (K := Q.adicCompletion K)
        (L := L) K').toEquiv).symm
    have hdvd : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2)
        ∣ Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) L) 2) := by
      rw [hcardK, hcard]
      exact Subgroup.index_dvd_card K'
    obtain ⟨v, hv, hv_eq⟩ := NK.NUV2.RouteF.transition_generator (F := Q.adicCompletion K)
      (L := L) K' (inferInstance) hcard u hu hcardK
    have hcoh : (NK.NUV2.RouteD.levelInfMap (F := Q.adicCompletion K)
          (M := ↥C) (L := L)) v
        = (((Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) L) 2))
            / (Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2)) : ℕ) : ℤ) • u := by
      rw [hcard, hcardK]
      exact hv_eq
    have hresθ : ∀ a, (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := L) (E := ↥C))
        (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := L) hcomm u hu a)
        = NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := ↥C) hcommC v hv a :=
      fun a => NK.NUV2.RouteE.levelSymbol_restrict (F := Q.adicCompletion K)
        (M := ↥C) (L := L) hcommC hcomm v hv u hu hdvd hcoh a
    have hres_one : ∀ a, (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K)
        (K₁ := L) (E := ↥C)) (θ a) = 1 := by
      intro a
      have hmem : θ a ∈ K' := hHK' (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      have hmem2 : θ a ∈ (IntermediateField.fixedField K').fixingSubgroup := by
        rwa [IntermediateField.fixingSubgroup_fixedField (F := Q.adicCompletion K) K']
      rw [← IntermediateField.restrictNormalHom_ker (K := Q.adicCompletion K) (L := L)
        (IntermediateField.fixedField K'), MonoidHom.mem_ker] at hmem2
      exact hmem2
    have hθC_one : NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := ↥C)
        hcommC v hv = 1 :=
      MonoidHom.ext fun a => by
        rw [← hresθ a]
        exact hres_one a
    have htop : NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥C = ⊤ := by
      rw [← NK.NUV2.Final.levelSymbol_ker_cyclic (F := Q.adicCompletion K) (E := ↥C)
        hcommC hcycC v hv, hθC_one]
      ext x
      simp [MonoidHom.mem_ker]
    have hone : Nat.card ((Q.adicCompletion K)ˣ ⧸
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥C) = 1 := by
      rw [← Subgroup.index_eq_card, htop, Subgroup.index_top]
    have hfr : Module.finrank (Q.adicCompletion K) ↥C = 1 := by
      have h := Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
        (K := K) Q (E := ↥C) hcommC
      rw [← h]
      show Nat.card ((Q.adicCompletion K)ˣ ⧸
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥C) = 1
      exact hone
    have hK'idx : K'.index = 1 := by
      rw [← hcardK, h1C, hfr]
    exact hK'ne (Subgroup.index_eq_one.mp hK'idx)
  -- ## Conclusion: the kernel is the norm group
  have hker_eq : MonoidHom.ker θ = NK.LocalReciprocity.normGroup (Q.adicCompletion K) L := by
    refine le_antisymm ?_ hnorm_le
    have hidx1 : Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.ker θ)
        = Nat.card (L ≃ₐ[Q.adicCompletion K] L) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hsurj).toEquiv
    have hidx2 : Nat.card ((Q.adicCompletion K)ˣ ⧸
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) L)
        = Module.finrank (Q.adicCompletion K) L :=
      Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
        (K := K) Q (E := L) hcomm
    have hidx : (MonoidHom.ker θ).index
        = (NK.LocalReciprocity.normGroup (Q.adicCompletion K) L).index := by
      rw [Subgroup.index_eq_card, Subgroup.index_eq_card, hidx1, hidx2]
      exact IsGalois.card_aut_eq_finrank (Q.adicCompletion K) L
    have hpos : (MonoidHom.ker θ).index ≠ 0 := by
      have heq : (MonoidHom.ker θ).index = Module.finrank (Q.adicCompletion K) L := by
        rw [hidx, Subgroup.index_eq_card, hidx2]
      rw [heq]
      exact (Module.finrank_pos (R := Q.adicCompletion K) (M := L)).ne'
    have hrel : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) L).relIndex
        (MonoidHom.ker θ) = 1 := by
      have h := Subgroup.relIndex_mul_index hnorm_le
      rw [← hidx] at h
      have h' : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) L).relIndex
            (MonoidHom.ker θ) * (MonoidHom.ker θ).index = 1 * (MonoidHom.ker θ).index := by
        rw [one_mul]
        exact h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h'
    exact Subgroup.relIndex_eq_one.mp hrel
  refine ⟨?_, ?_⟩
  · show MonoidHom.ker θ = NK.LocalReciprocity.normGroup (Q.adicCompletion K) L
    exact hker_eq
  · show Function.Surjective θ
    exact hsurj

end NK.NUV2.Final
