import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.exists_idealOf_eq_of_mem_idealCoprimeGroupId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.idealOf_mem_principalRayId_sup_normRayId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The range and the index of the map `θ` for an ideal modulus

This module completes the basic theory of the map
`thetaId : 𝕀 K →* (fractional ideals of K) ⧸ P(𝔪)·𝔑(𝔪)` of `AdjustId.lean`:

* `mk'_rayNormClId_mul_spanUnit` — multiplying by a principal idèle of `U(𝔪)` does not change the
  class (well-definedness of `θ`);
* `thetaId_range` — the image of `θ` is the image of `I(𝔪)` under the projection;
* `thetaIdFun_norm_eq_one`, `thetaId_norm_eq_one` — `θ` kills the idèlic norms;
* `principalSubgroup_sup_normImage_le_ker_thetaId` — the kernel contains `Kˣ · N_{L/K} 𝕀 L`;
* `index_rayNormId_eq_ker_index` — `[I(𝔪) : P(𝔪)·𝔑(𝔪)]` is the index of the kernel of `θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- A prime `(γ)` with `principalIdele γ ∈ U(𝔪)` lies in `P(𝔪) ⊆ P(𝔪)·𝔑(𝔪)`. -/
lemma spanUnitHom_mem_rayNormClId {𝔪 : Ideal (𝓞 K)} {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ congruenceSubgroupId K 𝔪) :
    spanUnitHom K γ ∈ rayNormClId K L 𝔪 :=
  Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)

/-- **The class of `θ` does not depend on the adjustment**: the ratio of two adjustments is a
principal idèle of `U(𝔪)`, hence a generator of `P(𝔪)`. -/
lemma mk'_rayNormClId_mul_spanUnit {𝔪 : Ideal (𝓞 K)} {γ : Kˣ}
    (hγ : Idele.principalIdele K γ ∈ congruenceSubgroupId K 𝔪) (𝔞 : Frac K) :
    QuotientGroup.mk' (rayNormClId K L 𝔪) (𝔞 * spanUnitHom K γ)
      = QuotientGroup.mk' (rayNormClId K L 𝔪) 𝔞 := by
  have hmk : QuotientGroup.mk' (rayNormClId K L 𝔪) (spanUnitHom K γ) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (spanUnitHom_mem_rayNormClId (K := K) hγ)
  rw [map_mul, hmk, ← map_one (QuotientGroup.mk' (rayNormClId K L 𝔪)), ← map_mul, mul_one]

/-- **`θ` kills the idèlic norms.** -/
lemma thetaIdFun_norm_eq_one {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (y : Idele L) :
    thetaIdFun (K := K) (L := L) 𝔪 h𝔪 (Idele.normIdeleHom K L y) = 1 := by
  have hmem : IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y *
      Idele.principalIdele K (adjIdMod 𝔪 h𝔪 (Idele.normIdeleHom K L y))) ∈ rayNormClId K L 𝔪 := by
    rw [rayNormClId, principalRayClId_eq_principalRayId h𝔪]
    exact Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.idealOf_mem_principalRayId_sup_normRayId
      (K := K) (L := L) 𝔪 h𝔪 (adjIdMod_spec h𝔪 _) rfl
  rw [thetaIdFun]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

/-- **`θ` kills the idèlic norms**, in the form of the homomorphism `thetaId`. -/
lemma thetaId_norm_eq_one {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (y : Idele L) :
    thetaId K L 𝔪 h𝔪 (Idele.normIdeleHom K L y) = 1 := by
  rw [thetaId_apply]
  exact thetaIdFun_norm_eq_one (K := K) (L := L) h𝔪 y

/-- **The kernel of `θ` contains the principal idèles and the idèlic norms.** -/
lemma principalSubgroup_sup_normImage_le_ker_thetaId {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (Idele.principalSubgroup K ⊔ Idele.normImage K L) ≤ (thetaId K L 𝔪 h𝔪).ker := by
  rw [Idele.normImage_eq_range]
  refine sup_le ?_ ?_
  · rintro x ⟨α, rfl⟩
    exact principalSubgroup_le_ker_thetaId (K := K) (L := L) h𝔪 ⟨α, rfl⟩
  · rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    exact thetaId_norm_eq_one (K := K) (L := L) h𝔪 y

/-- **The image of `θ` is the image of `I(𝔪)`.** -/
lemma thetaId_range {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (thetaId K L 𝔪 h𝔪).range
      = (idealCoprimeGroupId 𝔪).map (QuotientGroup.mk' (rayNormClId K L 𝔪)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨IdeleClassGroup.idealOfUnitHom K (x * Idele.principalIdele K (adjIdMod 𝔪 h𝔪 x)), ?_, ?_⟩
    · refine (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
        (K := K) 𝔪 (IdeleClassGroup.idealOfUnitHom K
          (x * Idele.principalIdele K (adjIdMod 𝔪 h𝔪 x)))).mpr ?_
      intro 𝔭 h𝔭
      exact count_idealOf_eq_zero_of_congruenceId (adjIdMod_spec h𝔪 x) 𝔭
        ((dvdPrime_iff_one_le_count h𝔪 𝔭).mp h𝔭)
    · rw [thetaId_apply]
      rfl
  · rintro ⟨𝔞, h𝔞, rfl⟩
    obtain ⟨z, hz, hzide⟩ :=
      Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.exists_idealOf_eq_of_mem_idealCoprimeGroupId
        (K := K) 𝔪 h𝔪 𝔞
        ((Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff 𝔪 𝔞).mp
          h𝔞)
    have hzadj : Idele.principalIdele K (adjIdMod 𝔪 h𝔪 z) ∈ congruenceSubgroupId K 𝔪 :=
      mem_congruenceSubgroupId_of_mul_eq (x := z * Idele.principalIdele K (adjIdMod 𝔪 h𝔪 z))
        (y := z) (adjIdMod_spec h𝔪 z) hz (γ := adjIdMod 𝔪 h𝔪 z) rfl
    refine ⟨z, ?_⟩
    rw [thetaId_apply, thetaIdFun_eq_mk (K := K) (L := L) h𝔪 (x := z)
      (c := adjIdMod 𝔪 h𝔪 z) (adjIdMod_spec h𝔪 z)]
    rw [show IdeleClassGroup.idealOfUnitHom K (z * Idele.principalIdele K (adjIdMod 𝔪 h𝔪 z))
        = IdeleClassGroup.idealOfUnitHom K z * spanUnitHom K (adjIdMod 𝔪 h𝔪 z) by
      rw [map_mul, idealOfUnitHom_principalIdele']]
    rw [hzide]
    exact mk'_rayNormClId_mul_spanUnit (K := K) (L := L) hzadj 𝔞

/-- **The index of `P(𝔪)·𝔑(𝔪)` in `I(𝔪)` equals the index of the kernel of `θ`.** -/
lemma index_rayNormId_eq_ker_index {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    ((rayNormClId K L 𝔪).subgroupOf (idealCoprimeGroupId 𝔪)).index
      = (thetaId K L 𝔪 h𝔪).ker.index := by
  have hfker : ((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).ker
      = (rayNormClId K L 𝔪).subgroupOf (idealCoprimeGroupId 𝔪) := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h1 : ((rayNormClId K L 𝔪).subgroupOf (idealCoprimeGroupId 𝔪)).index
      = Nat.card ((idealCoprimeGroupId 𝔪) ⧸ ((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
              (idealCoprimeGroupId 𝔪).subtype).ker) := by
    rw [Subgroup.index_eq_card, hfker]
  have h2 : (thetaId K L 𝔪 h𝔪).ker.index = Nat.card (thetaId K L 𝔪 h𝔪).range := by
    rw [Subgroup.index_eq_card]
    have hker'' : (thetaId K L 𝔪 h𝔪).rangeRestrict.ker = (thetaId K L 𝔪 h𝔪).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker'']
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (thetaId K L 𝔪 h𝔪).rangeRestrict
      (fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩)).toEquiv
  have h3 : Nat.card ((idealCoprimeGroupId 𝔪) ⧸
        ((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
          (idealCoprimeGroupId 𝔪).subtype).ker)
      = Nat.card (thetaId K L 𝔪 h𝔪).range := by
    have hsurj : Function.Surjective (((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).rangeRestrict) :=
      fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩
    have hrange : ((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).range = (thetaId K L 𝔪 h𝔪).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype,
        ← thetaId_range (K := K) (L := L) h𝔪]
    have hker' : ((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
        (idealCoprimeGroupId 𝔪).subtype).rangeRestrict.ker
        = ((QuotientGroup.mk' (rayNormClId K L 𝔪)).comp
            (idealCoprimeGroupId 𝔪).subtype).ker := by
      ext x
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [← hker', Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
      hrange]
  rw [h1, h3, h2]

end NK.CFTLib.ArtinReciprocityIdeal
