import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Submission.NK.NUV2.kernelCondition_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local class field theory: degree-`p` Galois levels versus index-`p` subgroups of the units

Let `F` be a field with a separable closure `F'` and let `D` be the canonical local Artin
reciprocity datum (`NK.LocalCFT.ArtinReciprocity F F'`).  We prove

  `#{L ⊆ F^{ab} : L/F Galois of degree p} = #{M ≤ Fˣ : M.index = p}`,

i.e. local class field theory in the form needed here: the abelian extensions of degree `p` are
classified by their norm groups, and the norm groups of the degree-`p` levels are exactly the
index-`p` subgroups of `Fˣ`.

The two directions:
* *existence* (every index-`p` subgroup `M` is a norm group): by cofinality of the norm groups
  (`D.cofinal`) there is a level `L₀` with `N_{L₀} ≤ M`; the fixed field of the image of `M` in
  `Gal(L₀/F)` under the reciprocity isomorphism `Fˣ ⧸ N_{L₀} ≃* Gal(L₀/F)` is then a degree-`p`
  level with norm group `M`;
* *uniqueness* (a level is determined by its norm group): if `L₁`, `L₂` are degree-`p` levels with
  `N_{L₁} = N_{L₂}`, take the compositum `L' = L₁ ⊔ L₂`; the restriction
  `Gal(L'/F) →* Gal(Lᵢ/F)` is surjective, and the image of `N_{Lᵢ}` in `Gal(L'/F)` is its kernel,
  so `N_{L₁} = N_{L₂}` forces `Gal(L'/L₁) = Gal(L'/L₂)` and hence `L₁ = L₂`.
-/

namespace Work.SSGRoute.PTembedding

open scoped Classical

/-- The maximal abelian subextension of `F'/F`, locally. -/
abbrev MaxAb (F F' : Type*) [Field F] [Field F'] [Algebra F F'] : IntermediateField F F' :=
  NK.LocalReciprocity.maxAbelianSubext F F'

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

section Levels

variable [IsSepClosure F F']

/-- A degree-`p` Galois level of the maximal abelian subextension `F^{ab}`. -/
def IsDegPLevel (p : ℕ) (L : IntermediateField F ↥(MaxAb F F')) : Prop :=
  IsGalois F ↥L ∧ Module.finrank F ↥L = p

variable {p : ℕ} [Fact p.Prime]

include F in
lemma isDegPLevel_finiteDimensional {L : IntermediateField F ↥(MaxAb F F')}
    (h : IsDegPLevel p L) : FiniteDimensional F ↥L :=
  FiniteDimensional.of_finrank_pos (by rw [h.2]; exact (Fact.out : p.Prime).pos)

lemma isDegPLevel_commutative {L : IntermediateField F ↥(MaxAb F F')}
    (h : IsDegPLevel p L) : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ := by
  haveI := isDegPLevel_finiteDimensional (F := F) h
  haveI : IsGalois F ↥L := h.1
  have hcard : Nat.card (↥L ≃ₐ[F] ↥L) = p := by
    rw [IsGalois.card_aut_eq_finrank F ↥L, h.2]
  intro σ τ
  exact isMulCommutative_iff.mp (isCyclic_of_prime_card hcard).isMulCommutative σ τ

lemma isDegPLevel_normal {L : IntermediateField F ↥(MaxAb F F')}
    (h : IsDegPLevel p L) : Normal F ↥L :=
  h.1.to_normal

/-- **The norm group of a degree-`p` level has index `p`.** -/
theorem index_normGroup_of_isDegPLevel (D : NK.LocalCFT.ArtinReciprocity F F')
    {L : IntermediateField F ↥(MaxAb F F')} (h : IsDegPLevel p L) :
    (NK.LocalReciprocity.normGroup F ↥L).index = p := by
  haveI := isDegPLevel_finiteDimensional (F := F) h
  haveI : IsGalois F ↥L := h.1
  haveI : Normal F ↥L := isDegPLevel_normal h
  rw [Subgroup.index_eq_card]
  rw [Nat.card_congr (D.artinLevelMulEquiv L (isDegPLevel_commutative h)).toEquiv,
    IsGalois.card_aut_eq_finrank F ↥L, h.2]

end Levels


section Existence

variable [IsSepClosure F F'] {p : ℕ} [Fact p.Prime]

/-- **Existence of a degree-`p` level with prescribed norm group.**  Every index-`p` subgroup of
`Fˣ` is the norm group of a degree-`p` Galois level of the maximal abelian subextension. -/
theorem exists_isDegPLevel_normGroup_eq (D : NK.LocalCFT.ArtinReciprocity F F')
    {M : Subgroup Fˣ} (hM : M.index = p) :
    ∃ L : IntermediateField F ↥(MaxAb F F'), IsDegPLevel p L ∧
      NK.LocalReciprocity.normGroup F ↥L = M := by
  have hpne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfin : M.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by rw [hM]; exact hpne)
  obtain ⟨L₀, hfd₀, hnorm₀, hcomm₀, hle₀⟩ := D.cofinal M hfin
  haveI := hfd₀
  haveI := hnorm₀
  set N₀ : Subgroup Fˣ := NK.LocalReciprocity.normGroup F ↥L₀ with hN₀
  haveI hN₀normal : N₀.Normal := Subgroup.normal_of_isMulCommutative N₀
  haveI hcommCyc : IsMulCommutative (↥L₀ ≃ₐ[F] ↥L₀) := isMulCommutative_iff.mpr hcomm₀
  set e := D.artinLevelMulEquiv L₀ hcomm₀ with he
  set H : Subgroup (↥L₀ ≃ₐ[F] ↥L₀) := (M.map (QuotientGroup.mk' N₀)).map e.toMonoidHom with hH
  haveI hHnormal : H.Normal := Subgroup.normal_of_isMulCommutative H
  -- `H` has index `p`
  have hHindex : H.index = p := by
    have h1 : H.index = (M.map (QuotientGroup.mk' N₀)).index := Subgroup.index_map_equiv _ e
    rw [h1, Subgroup.index_map_eq M (QuotientGroup.mk'_surjective N₀)
      (by rw [QuotientGroup.ker_mk']; exact hle₀), hM]
  -- the preimage of `H` in the abelianised absolute Galois group
  set Ht : Subgroup (NK.LocalCFT.AbGal F F') := H.comap (NK.LocalCFT.levelRestrict L₀) with hHt
  haveI : IsGalois F ↥(MaxAb F F') := NK.LocalReciprocity.instIsGaloisMaxAbelianSubext
  haveI hAbComm : IsMulCommutative (NK.LocalCFT.AbGal F F') :=
    isMulCommutative_iff.mpr NK.LocalReciprocity.commutative_gal_maxAbelianSubext
  haveI hHtnormal : Ht.Normal := Subgroup.normal_of_isMulCommutative Ht
  -- `Ht` has index `p` as well
  have hsurj₀ : Function.Surjective ⇑(NK.LocalCFT.levelRestrict L₀) :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L₀) ↥(MaxAb F F')
  have hHtindex : Ht.index = p := by
    rw [hHt, Subgroup.index_comap_of_surjective H hsurj₀, hHindex]
  -- it is closed, hence the fixing subgroup of its fixed field
  have hclosed : IsClosed (Ht : Set (NK.LocalCFT.AbGal F F')) := by
    rw [hHt, Subgroup.coe_comap]
    exact IsClosed.preimage
      (InfiniteGalois.restrictNormalHom_continuous (k := F) (K := ↥(MaxAb F F')) L₀)
      (isClosed_discrete (H : Set (↥L₀ ≃ₐ[F] ↥L₀)))
  have hfix : (IntermediateField.fixedField Ht).fixingSubgroup = Ht :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨Ht, hclosed⟩
  haveI hGalL : IsGalois F ↥(IntermediateField.fixedField Ht) :=
    IsGalois.of_fixedField_normal_subgroup Ht
  have hfinrank : Module.finrank F ↥(IntermediateField.fixedField Ht) = p := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index ↥(MaxAb F F')
      (IntermediateField.fixedField Ht), hfix, hHtindex]
  haveI : FiniteDimensional F ↥(IntermediateField.fixedField Ht) :=
    FiniteDimensional.of_finrank_pos (by rw [hfinrank]; exact (Fact.out : p.Prime).pos)
  have hcommL : ∀ σ τ : ↥(IntermediateField.fixedField Ht) ≃ₐ[F]
      ↥(IntermediateField.fixedField Ht), σ * τ = τ * σ := by
    have hcard : Nat.card (↥(IntermediateField.fixedField Ht) ≃ₐ[F]
        ↥(IntermediateField.fixedField Ht)) = p := by
      rw [IsGalois.card_aut_eq_finrank F ↥(IntermediateField.fixedField Ht), hfinrank]
    intro σ τ
    exact isMulCommutative_iff.mp (isCyclic_of_prime_card hcard).isMulCommutative σ τ
  -- translation of the reciprocity isomorphism
  have htrans : ∀ y : Fˣ, e (QuotientGroup.mk' N₀ y) =
      NK.LocalCFT.levelRestrict L₀ (D.artin y) := by
    intro y
    rw [he, QuotientGroup.mk'_apply]
    exact D.artinLevelMulEquiv_mk L₀ hcomm₀ y
  have hmem : ∀ x : Fˣ, (NK.LocalCFT.levelRestrict L₀ (D.artin x) ∈ H) ↔ x ∈ M := by
    intro x
    conv_lhs => rw [← htrans x]
    rw [hH, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [Subgroup.mem_map] at hz
      obtain ⟨m, hm, hmz⟩ := hz
      have hqm : QuotientGroup.mk' N₀ m = QuotientGroup.mk' N₀ x :=
        e.injective (by rw [hmz]; exact hzx)
      have hker : x * m⁻¹ ∈ N₀ := by
        rw [← QuotientGroup.eq_one_iff (x * m⁻¹)]
        rw [← QuotientGroup.mk'_apply, map_mul, map_inv, hqm, mul_inv_cancel]
      have hxm : x * m⁻¹ * m ∈ M := M.mul_mem (hle₀ hker) hm
      rwa [mul_assoc, inv_mul_cancel, mul_one] at hxm
    · intro hx
      exact ⟨QuotientGroup.mk' N₀ x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨IntermediateField.fixedField Ht, ⟨⟨hGalL, hfinrank⟩, ?_⟩⟩
  rw [← (D.isLevelIso (IntermediateField.fixedField Ht) hcommL).2]
  have hker1 : (NK.LocalCFT.levelRestrict (IntermediateField.fixedField Ht)).ker = Ht := by
    change (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(MaxAb F F'))
      ↥(IntermediateField.fixedField Ht)).ker = Ht
    rw [IntermediateField.restrictNormalHom_ker (IntermediateField.fixedField Ht), hfix]
  have hker2 : ((NK.LocalCFT.levelRestrict (IntermediateField.fixedField Ht)).comp D.artin).ker
      = Subgroup.comap D.artin Ht := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
    rw [← MonoidHom.mem_ker, hker1]
  rw [hker2]
  ext x
  rw [Subgroup.mem_comap]
  exact hmem x

end Existence


section Injectivity

variable [IsSepClosure F F'] {p : ℕ} [Fact p.Prime]

/-- **A degree-`p` level is determined by its norm group.**  Two degree-`p` Galois levels of the
maximal abelian subextension with the same norm group are equal. -/
theorem eq_of_normGroup_eq (D : NK.LocalCFT.ArtinReciprocity F F')
    {L₁ L₂ : IntermediateField F ↥(MaxAb F F')} (h₁ : IsDegPLevel p L₁) (h₂ : IsDegPLevel p L₂)
    (hN : NK.LocalReciprocity.normGroup F ↥L₁ = NK.LocalReciprocity.normGroup F ↥L₂) :
    L₁ = L₂ := by
  haveI hfd₁ : FiniteDimensional F ↥L₁ := isDegPLevel_finiteDimensional (F := F) h₁
  haveI hfd₂ : FiniteDimensional F ↥L₂ := isDegPLevel_finiteDimensional (F := F) h₂
  haveI hgal₁ : IsGalois F ↥L₁ := h₁.1
  haveI hgal₂ : IsGalois F ↥L₂ := h₂.1
  haveI hn₁ : Normal F ↥L₁ := isDegPLevel_normal h₁
  haveI hn₂ : Normal F ↥L₂ := isDegPLevel_normal h₂
  -- the compositum `L' = L₁ ⊔ L₂`, a level of `F^{ab}`
  set L' : IntermediateField F ↥(MaxAb F F') := L₁ ⊔ L₂ with hL'
  haveI hfd' : FiniteDimensional F ↥L' := by
    rw [hL']; exact IntermediateField.finiteDimensional_sup L₁ L₂
  haveI hAb : IsMulCommutative (NK.LocalCFT.AbGal F F') :=
    isMulCommutative_iff.mpr NK.LocalReciprocity.commutative_gal_maxAbelianSubext
  haveI hgal' : IsGalois F ↥L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp
      (Subgroup.normal_of_isMulCommutative L'.fixingSubgroup)
  haveI hn' : Normal F ↥L' := hgal'.to_normal
  have hcomm' : ∀ σ τ : ↥L' ≃ₐ[F] ↥L', σ * τ = τ * σ := by
    have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := F)
        (K₁ := ↥(MaxAb F F')) ↥L') :=
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L') ↥(MaxAb F F')
    intro σ τ
    obtain ⟨σ', rfl⟩ := hsurj σ
    obtain ⟨τ', rfl⟩ := hsurj τ
    rw [← map_mul, ← map_mul, isMulCommutative_iff.mp hAb σ' τ']
  -- restriction to a sub-level factors through `L'`
  have hker_eq : ∀ (L : IntermediateField F ↥(MaxAb F F')) (hL : L ≤ L') [Normal F ↥L],
      MonoidHom.ker (NK.LocalCFT.levelRestrict L) =
        Subgroup.comap (NK.LocalCFT.levelRestrict L')
          (MonoidHom.ker (NK.LocalCFT.levelRestrictLe hL)) := by
    intro L hL _
    have hcomp : NK.LocalCFT.levelRestrict L =
        (NK.LocalCFT.levelRestrictLe hL).comp (NK.LocalCFT.levelRestrict L') :=
      MonoidHom.ext fun σ =>
        (NK.LocalCFT.Functoriality.levelRestrictLe_comp_levelRestrict hL σ).symm
    rw [hcomp]
    ext σ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
  -- the norm group as the preimage of the kernel of the restriction map
  have key : ∀ (L : IntermediateField F ↥(MaxAb F F')) (hL : L ≤ L') [FiniteDimensional F ↥L]
      [Normal F ↥L] (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ),
      NK.LocalReciprocity.normGroup F ↥L =
        Subgroup.comap ((NK.LocalCFT.levelRestrict L').comp D.artin)
          (MonoidHom.ker (NK.LocalCFT.levelRestrictLe hL)) := by
    intro L hL _ _ hcommL
    have h1 : NK.LocalReciprocity.normGroup F ↥L =
        MonoidHom.ker ((NK.LocalCFT.levelRestrict L).comp D.artin) :=
      ((D.isLevelIso L hcommL).2).symm
    rw [h1]
    have h2 : MonoidHom.ker ((NK.LocalCFT.levelRestrict L).comp D.artin) =
        Subgroup.comap D.artin (MonoidHom.ker (NK.LocalCFT.levelRestrict L)) := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
    rw [h2, hker_eq L hL]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
  -- the kernels of the two restrictions agree, because the norm groups do
  have hsurjψ : Function.Surjective ⇑((NK.LocalCFT.levelRestrict L').comp D.artin) :=
    (D.isLevelIso L' hcomm').1
  have hkerfix : ∀ (L : IntermediateField F ↥(MaxAb F F')) [Normal F ↥L],
      MonoidHom.ker (NK.LocalCFT.levelRestrict L) = L.fixingSubgroup := by
    intro L _
    change (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(MaxAb F F')) ↥L).ker = L.fixingSubgroup
    exact IntermediateField.restrictNormalHom_ker L
  have hkerf : MonoidHom.ker (NK.LocalCFT.levelRestrictLe (le_sup_left : L₁ ≤ L')) =
      MonoidHom.ker (NK.LocalCFT.levelRestrictLe (le_sup_right : L₂ ≤ L')) := by
    have hN₁ := key L₁ le_sup_left (isDegPLevel_commutative h₁)
    have hN₂ := key L₂ le_sup_right (isDegPLevel_commutative h₂)
    calc MonoidHom.ker (NK.LocalCFT.levelRestrictLe (le_sup_left : L₁ ≤ L'))
        = Subgroup.map ((NK.LocalCFT.levelRestrict L').comp D.artin)
            (Subgroup.comap ((NK.LocalCFT.levelRestrict L').comp D.artin)
              (MonoidHom.ker (NK.LocalCFT.levelRestrictLe (le_sup_left : L₁ ≤ L')))) :=
          (Subgroup.map_comap_eq_self_of_surjective hsurjψ _).symm
      _ = Subgroup.map ((NK.LocalCFT.levelRestrict L').comp D.artin)
            (NK.LocalReciprocity.normGroup F ↥L₁) := by rw [← hN₁]
      _ = Subgroup.map ((NK.LocalCFT.levelRestrict L').comp D.artin)
            (NK.LocalReciprocity.normGroup F ↥L₂) := by rw [hN]
      _ = Subgroup.map ((NK.LocalCFT.levelRestrict L').comp D.artin)
            (Subgroup.comap ((NK.LocalCFT.levelRestrict L').comp D.artin)
              (MonoidHom.ker (NK.LocalCFT.levelRestrictLe (le_sup_right : L₂ ≤ L')))) := by
          rw [hN₂]
      _ = MonoidHom.ker (NK.LocalCFT.levelRestrictLe (le_sup_right : L₂ ≤ L')) :=
          Subgroup.map_comap_eq_self_of_surjective hsurjψ _
  have hA : L₁.fixingSubgroup = L₂.fixingSubgroup := by
    rw [← hkerfix L₁, ← hkerfix L₂, hker_eq L₁ le_sup_left, hker_eq L₂ le_sup_right, hkerf]
  calc L₁ = IntermediateField.fixedField L₁.fixingSubgroup :=
        (InfiniteGalois.fixedField_fixingSubgroup L₁).symm
    _ = IntermediateField.fixedField L₂.fixingSubgroup := by rw [hA]
    _ = L₂ := InfiniteGalois.fixedField_fixingSubgroup L₂

end Injectivity


section Main

variable [IsSepClosure F F'] {p : ℕ} [Fact p.Prime]

/-- **Local class field theory: degree-`p` Galois levels of `F^{ab}` are counted by the index-`p`
subgroups of `Fˣ`.**  The bijection is `L ↦ N_{L/F} Lˣ`; its inverse is the fixed field of the
image of `M` in `Gal(L₀/F)` under the reciprocity isomorphism at a level `L₀` with `N_{L₀} ≤ M`
(which exists by the existence theorem). -/
theorem natCard_isDegPLevel_eq_indexP_subgroups (D : NK.LocalCFT.ArtinReciprocity F F') :
    Nat.card {L : IntermediateField F ↥(MaxAb F F') // IsDegPLevel p L}
      = Nat.card {M : Subgroup Fˣ // M.index = p} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun L : {L : IntermediateField F ↥(MaxAb F F') // IsDegPLevel p L} =>
      (⟨NK.LocalReciprocity.normGroup F ↥L.1, index_normGroup_of_isDegPLevel D L.2⟩ :
        {M : Subgroup Fˣ // M.index = p}))
    ⟨?_, ?_⟩)
  · intro L₁ L₂ h
    exact Subtype.ext (eq_of_normGroup_eq D L₁.2 L₂.2 (congrArg Subtype.val h))
  · intro M
    obtain ⟨L, hL, hN⟩ := exists_isDegPLevel_normGroup_eq D M.2
    exact ⟨⟨L, hL⟩, Subtype.ext hN⟩

end Main

end Work.SSGRoute.PTembedding
