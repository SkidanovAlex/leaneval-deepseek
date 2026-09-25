import Mathlib

set_option linter.style.haveILetI false

namespace Work.Tower

open NumberField

/-- A number field which is a Galois extension of `ℚ` of degree `3` is totally real.

Indeed, if some complex embedding were not real, complex conjugation would induce a
non-trivial element of `Gal(K/ℚ)` of order dividing `2`, impossible in a group of order `3`. -/
theorem isTotallyReal_of_isGalois_finrank_three (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (h : Module.finrank ℚ K = 3) : NumberField.IsTotallyReal K := by
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isReal_iff]
  by_contra hnr
  -- complex conjugation of the embedding `v.embedding` is another `ℚ`-embedding, hence is
  -- the composite with an automorphism `σ` of `K` over `ℚ`
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) v.embedding
      (ComplexEmbedding.conjugate v.embedding) (by ext x; simp)
  have hconj : ComplexEmbedding.IsConj v.embedding σ.symm := hσ.symm
  -- since `v.embedding` is not real, `σ ≠ 1`, so `σ` has order `2`
  have hne : σ.symm ≠ 1 := (ComplexEmbedding.isConj_ne_one_iff hconj).mpr hnr
  have ho : orderOf σ = 2 := by
    have h2 := ComplexEmbedding.orderOf_isConj_two_of_ne_one hconj hne
    rwa [show σ.symm = σ⁻¹ from rfl, orderOf_inv] at h2
  -- but `orderOf σ` divides the order `3` of the Galois group
  have hdvd : orderOf σ ∣ Module.finrank ℚ K := by
    rw [← IsGalois.card_aut_eq_finrank ℚ K]
    exact orderOf_dvd_natCard σ
  rw [ho, h] at hdvd
  norm_num at hdvd

/-- For a prime `r ≡ 1 (mod 3)`, the cyclotomic field `ℚ(ζ_r)` contains a subfield `F` of
degree `3` over `ℚ` which is Galois with automorphism group of order `3` and is totally real. -/
theorem CyclotomicCubic (r : ℕ) (hr : Nat.Prime r) (hr3 : r % 3 = 1) :
    ∃ (F : IntermediateField ℚ (CyclotomicField r ℚ)),
      Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧ Fintype.card (↥F ≃ₐ[ℚ] ↥F) = 3 ∧
      NumberField.IsTotallyReal ↥F := by
  classical
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  let L := CyclotomicField r ℚ
  haveI hLc : IsCyclotomicExtension {r} ℚ L := CyclotomicField.isCyclotomicExtension r ℚ
  haveI hLg : IsGalois ℚ L := IsCyclotomicExtension.isGalois {r} ℚ L
  haveI hLn : NumberField L := (inferInstance : NumberField (CyclotomicField r ℚ))
  haveI : IsCyclic (ZMod r)ˣ := ZMod.isCyclic_units_prime hr
  -- the subgroup of cubes in `(ℤ/rℤ)ˣ`, which has index `3`
  let C : Subgroup (ZMod r)ˣ := (powMonoidHom 3).range
  have hCidx : C.index = 3 := by
    change (powMonoidHom 3 : (ZMod r)ˣ →* (ZMod r)ˣ).range.index = 3
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units r]
    exact Nat.gcd_eq_right (by simpa [hr3] using Nat.dvd_sub_mod (n := 3) r)
  -- its preimage in `Gal(ℚ(ζ_r)/ℚ)` under the cyclotomic character
  let g : Gal(L/ℚ) →* (ZMod r)ˣ := (IsCyclotomicExtension.Rat.galEquivZMod r L).toMonoidHom
  have hg : Function.Surjective g := (IsCyclotomicExtension.Rat.galEquivZMod r L).surjective
  let H : Subgroup Gal(L/ℚ) := C.comap g
  have hHidx : H.index = 3 := by
    change (C.comap g).index = 3
    rw [Subgroup.index_comap_of_surjective C hg, hCidx]
  haveI hHn : H.Normal := Subgroup.Normal.comap (inferInstance : C.Normal) g
  -- the associated subfield, of degree `3`, Galois and totally real
  let F : IntermediateField ℚ L := IntermediateField.fixedField H
  haveI hFg : IsGalois ℚ ↥F := IsGalois.of_fixedField_normal_subgroup H
  have hfin : Module.finrank ℚ ↥F = 3 := by
    change Module.finrank ℚ ↥(IntermediateField.fixedField H) = 3
    rw [IntermediateField.finrank_eq_fixingSubgroup_index L (IntermediateField.fixedField H),
      IntermediateField.fixingSubgroup_fixedField H, hHidx]
  refine ⟨F, hfin, hFg, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ ↥F, hfin]
  · exact isTotallyReal_of_isGalois_finrank_three ↥F hfin

end Work.Tower
