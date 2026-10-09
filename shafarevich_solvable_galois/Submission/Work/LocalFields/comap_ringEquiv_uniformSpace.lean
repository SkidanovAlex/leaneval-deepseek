import Mathlib
import Submission.Work.LocalFields.Inputs
import Submission.Work.LocalFields.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The uniform structure of a valuation pulled back along a ring equivalence

If `e : l ≃+* k` is a ring equivalence and `v` a valuation on `k` taking values in a
`LinearOrderedCommGroupWithZero`, then the uniform structure induced by the valuation
`v.comap e` on `l` is the pull-back along `e` of the uniform structure induced by `v` on `k`.

The proof computes both uniformities: the uniformity of `Valued.mk' w` is the filter
`comap (fun p => p.2 - p.1) (𝓝 0)` for the valuation topology of `w`, so it suffices to
identify the neighbourhoods of `0` for `v.comap e` with the preimages along `e` of the
neighbourhoods of `0` for `v`.  Both filters have an explicit basis (the subgroups
`v.ltAddSubgroup γ`, indexed by the units of the value group), and the two bases are matched
using that `e` is bijective, hence induces an identification of the value groups.
-/

namespace Work.LocalFields

open scoped Valued
open Filter

section ValueGroupHelpers

/-- Membership in the value group of a monoid-with-zero homomorphism into a group with
zero, in terms of the range of the homomorphism. -/
lemma mem_valueGroup_iff_mem_range {A B : Type*} [GroupWithZero A] [GroupWithZero B]
    {φ : A →*₀ B} {y : Bˣ} :
    y ∈ MonoidWithZeroHom.valueGroup φ ↔ ∃ a, φ a = (y : B) := by
  constructor
  · intro hy
    have h : (y : B) ∈ Units.val '' (MonoidWithZeroHom.valueGroup φ) := ⟨y, hy, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at h
    exact ⟨h.1.choose, h.1.choose_spec⟩
  · rintro ⟨a, ha⟩
    have hne : φ a ≠ 0 := by rw [ha]; exact y.ne_zero
    have h : (Units.mk0 (φ a) hne : Bˣ).val ∈ Set.range φ := ⟨a, rfl⟩
    have hmem := MonoidWithZeroHom.mem_valueGroup φ h
    have heq : (Units.mk0 (φ a) hne : Bˣ) = y := Units.ext (by rw [Units.val_mk0, ha])
    rwa [heq] at hmem

/-- The embedding of the value group of a monoid-with-zero homomorphism, evaluated on an
element of the underlying value group. -/
lemma valueGroup₀_embedding_coe {A B : Type*} [MonoidWithZero A] [GroupWithZero B]
    {φ : A →*₀ B} (z : MonoidWithZeroHom.valueGroup φ) :
    MonoidWithZeroHom.ValueGroup₀.embedding (f := φ)
      (↑z : MonoidWithZeroHom.ValueGroup₀ φ) = ((z : Bˣ) : B) := by
  simp [MonoidWithZeroHom.ValueGroup₀.embedding]

/-- Every element of the value group of `φ` is the image under `Units.map` of the embedding
`ValueGroup₀ φ →*₀ B` of a unit of `ValueGroup₀ φ`. -/
lemma exists_units_map_embedding_eq {A B : Type*} [GroupWithZero A] [GroupWithZero B]
    {φ : A →*₀ B} {y : Bˣ} (hy : ∃ a, φ a = (y : B)) :
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ φ)ˣ,
      Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := φ)) γ = y := by
  have hmem : y ∈ MonoidWithZeroHom.valueGroup φ := mem_valueGroup_iff_mem_range.mpr hy
  refine ⟨Units.mk0 (↑(⟨y, hmem⟩ : MonoidWithZeroHom.valueGroup φ)) (by simp), ?_⟩
  ext
  simp [MonoidWithZeroHom.ValueGroup₀.embedding]

/-- The image under `Units.map` of the embedding `ValueGroup₀ φ →*₀ B` of a unit of
`ValueGroup₀ φ` lies in the value group of `φ`. -/
lemma units_map_embedding_mem_valueGroup {A B : Type*} [GroupWithZero A] [GroupWithZero B]
    {φ : A →*₀ B} (γ : (MonoidWithZeroHom.ValueGroup₀ φ)ˣ) :
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := φ)) γ ∈
      MonoidWithZeroHom.valueGroup φ := by
  rw [mem_valueGroup_iff_mem_range]
  set z : MonoidWithZeroHom.valueGroup φ :=
    WithZero.unzero (x := γ.val) (Units.ne_zero γ) with hzdef
  have hcoe : (↑z : MonoidWithZeroHom.ValueGroup₀ φ) = γ.val := WithZero.coe_unzero _
  obtain ⟨a, ha⟩ := (mem_valueGroup_iff_mem_range (φ := φ) (y := (z : Bˣ))).mp z.2
  refine ⟨a, ?_⟩
  rw [ha, Units.coe_map]
  rw [← hcoe]
  exact (valueGroup₀_embedding_coe z).symm

end ValueGroupHelpers

section Main

variable {l k : Type*} [Field l] [Field k] (e : l ≃+* k)
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)

/-- The neighbourhoods of `0` in the valuation topology of `v.comap e` on `l` are the
preimages along `e` of the neighbourhoods of `0` in the valuation topology of `v` on `k`. -/
theorem nhds_zero_comap_ringEquiv :
    @nhds l ((v.comap (e : l →+* k)).subgroups_basis.topology) 0
      = Filter.comap (e : l → k) (@nhds k v.subgroups_basis.topology 0) := by
  let φL : l →*₀ Γ₀ := ((v.comap (e : l →+* k)) : l →*₀ Γ₀)
  let φV : k →*₀ Γ₀ := (v : k →*₀ Γ₀)
  let embL : MonoidWithZeroHom.ValueGroup₀ φL →*₀ Γ₀ := MonoidWithZeroHom.ValueGroup₀.embedding
  let embV : MonoidWithZeroHom.ValueGroup₀ φV →*₀ Γ₀ := MonoidWithZeroHom.ValueGroup₀.embedding
  have hnzL : ∀ γ : (MonoidWithZeroHom.ValueGroup₀ φL)ˣ, embL (↑γ) ≠ 0 := by
    intro γ h
    refine Units.ne_zero γ ?_
    exact (MonoidWithZeroHom.ValueGroup₀.embedding_inj (f := φL)).mp (by rw [h, map_zero])
  have hnzV : ∀ δ : (MonoidWithZeroHom.ValueGroup₀ φV)ˣ, embV (↑δ) ≠ 0 := by
    intro δ h
    refine Units.ne_zero δ ?_
    exact (MonoidWithZeroHom.ValueGroup₀.embedding_inj (f := φV)).mp (by rw [h, map_zero])
  -- every unit of `Γ₀ˣ` in the image of `embL` is also in the image of `embV`, and conversely
  have key : ∀ (γ : (MonoidWithZeroHom.ValueGroup₀ φL)ˣ),
      ∃ δ : (MonoidWithZeroHom.ValueGroup₀ φV)ˣ, embV (↑δ) = embL (↑γ) := by
    intro γ
    have hC : Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := φL)) γ ∈
        MonoidWithZeroHom.valueGroup φL := units_map_embedding_mem_valueGroup γ
    obtain ⟨a, ha⟩ := mem_valueGroup_iff_mem_range.mp hC
    rw [Units.coe_map] at ha
    have ha' : φL a = embL (↑γ) := ha
    obtain ⟨δ, hδ⟩ := exists_units_map_embedding_eq (φ := φV)
      (y := Units.mk0 (embL (↑γ)) (hnzL γ)) ⟨e a, by
        rw [Units.val_mk0]
        simpa only [φL, φV, Valuation.coe_toMonoidWithZeroHom, Valuation.comap_apply,
          RingEquiv.coe_toRingHom] using ha'⟩
    refine ⟨δ, ?_⟩
    have h := congrArg (fun u : Γ₀ˣ => (u : Γ₀)) hδ
    simpa [Units.coe_map] using h
  have key' : ∀ (δ : (MonoidWithZeroHom.ValueGroup₀ φV)ˣ),
      ∃ γ : (MonoidWithZeroHom.ValueGroup₀ φL)ˣ, embL (↑γ) = embV (↑δ) := by
    intro δ
    have hC : Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := φV)) δ ∈
        MonoidWithZeroHom.valueGroup φV := units_map_embedding_mem_valueGroup δ
    obtain ⟨b, hb⟩ := mem_valueGroup_iff_mem_range.mp hC
    rw [Units.coe_map] at hb
    have hb' : φV b = embV (↑δ) := hb
    obtain ⟨γ, hγ⟩ := exists_units_map_embedding_eq (φ := φL)
      (y := Units.mk0 (embV (↑δ)) (hnzV δ)) ⟨e.symm b, by
        rw [Units.val_mk0]
        simpa only [φL, φV, Valuation.coe_toMonoidWithZeroHom, Valuation.comap_apply,
          RingEquiv.coe_toRingHom, e.apply_symm_apply] using hb'⟩
    refine ⟨γ, ?_⟩
    have h := congrArg (fun u : Γ₀ˣ => (u : Γ₀)) hγ
    simpa [Units.coe_map] using h
  have hL : (@nhds l ((v.comap (e : l →+* k)).subgroups_basis.topology) 0).HasBasis
      (fun _ => True) (fun γ : (MonoidWithZeroHom.ValueGroup₀ φL)ˣ =>
        {x : l | (v.comap (e : l →+* k)) x < embL (↑γ)}) := by
    refine ((v.comap (e : l →+* k)).subgroups_basis.hasBasis_nhds_zero).congr
      (fun _ => Iff.rfl) (fun γ _ => ?_)
    ext x
    simp only [SetLike.mem_coe, Valuation.mem_ltAddSubgroup_iff, Set.mem_ofPred_eq]
    dsimp only [φL, embL]
    rw [Units.coe_map]
    rfl
  have hR : (Filter.comap (e : l → k) (@nhds k v.subgroups_basis.topology 0)).HasBasis
      (fun _ => True) (fun δ : (MonoidWithZeroHom.ValueGroup₀ φV)ˣ =>
        e ⁻¹' {y : k | v y < embV (↑δ)}) := by
    refine ((v.subgroups_basis.hasBasis_nhds_zero).comap (e : l → k)).congr
      (fun _ => Iff.rfl) (fun δ _ => ?_)
    have hs : (↑(v.ltAddSubgroup ((Units.map (↑(MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (v : k →*₀ Γ₀))))) δ)) : Set k) = {y : k | v y < embV (↑δ)} := by
      ext y
      simp only [SetLike.mem_coe, Valuation.mem_ltAddSubgroup_iff, Set.mem_ofPred_eq]
      dsimp only [φV, embV]
      rw [Units.coe_map]
      rfl
    rw [hs]
  refine hL.ext hR ?_ ?_
  · rintro γ -
    obtain ⟨δ, hδ⟩ := key γ
    refine ⟨δ, trivial, ?_⟩
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    rw [Valuation.comap_apply, RingEquiv.coe_toRingHom]
    rw [hδ] at hx
    exact hx
  · rintro δ -
    obtain ⟨γ, hγ⟩ := key' δ
    refine ⟨γ, trivial, ?_⟩
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    rw [Valuation.comap_apply, RingEquiv.coe_toRingHom] at hx
    rw [hγ] at hx
    exact hx

theorem comap_ringEquiv_uniformSpace {l k : Type*} [Field l] [Field k] (e : l ≃+* k)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀) :
    (Valued.mk' (v.comap (e : l →+* k))).toUniformSpace =
      UniformSpace.comap (e : l → k) (Valued.mk' v).toUniformSpace := by
  have h0 := nhds_zero_comap_ringEquiv e v
  apply UniformSpace.ext
  have hL : @uniformity l (Valued.mk' (v.comap (e : l →+* k))).toUniformSpace
      = Filter.comap (fun p : l × l => p.2 + -p.1)
        (@nhds l ((v.comap (e : l →+* k)).subgroups_basis.topology) 0) := rfl
  have hR : @uniformity k (Valued.mk' v).toUniformSpace
      = Filter.comap (fun q : k × k => q.2 + -q.1)
        (@nhds k v.subgroups_basis.topology 0) := rfl
  rw [uniformity_comap, hL, hR, h0, Filter.comap_comap, Filter.comap_comap]
  congr 1
  ext p
  simp only [Function.comp_apply]
  rw [map_add, map_neg]
  rfl

end Main

end Work.LocalFields
