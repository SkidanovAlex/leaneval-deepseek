import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Submission.Work.GenericKernelReduction.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem inClosure_of_surjective {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {A : Type} [Group A] [Finite A] {N : Type} [Group N] [Finite N]
    {Φ : (L ≃ₐ[ℚ] L) →* MulAut A} {φ : (L ≃ₐ[ℚ] L) →* MulAut N}
    (f : A ⋊[Φ] (L ≃ₐ[ℚ] L) →* N ⋊[φ] (L ≃ₐ[ℚ] L)) (hf : Function.Surjective f)
    (hproj : ∀ x : A ⋊[Φ] (L ≃ₐ[ℚ] L), SemidirectProduct.rightHom (f x) = SemidirectProduct.rightHom x)
    (h : Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L A Φ) :
    Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L N φ := by
  classical
  obtain ⟨M, hLM, hfdM, hgalM, hAlg, hST, hfdLM, hgalLM, e, he⟩ := h
  haveI : FiniteDimensional ℚ ↥M := hfdM
  haveI : IsGalois ℚ ↥M := hgalM
  haveI hNrm : Normal ℚ ↥L := IsGalois.to_normal
  letI : Algebra ↥L ↥M := hAlg
  haveI : IsScalarTower ℚ ↥L ↥M := hST
  -- the `ℚ`-algebra homomorphism `↥L → ↥M` of the hypothesis, and the compatibility of `e`
  let ι : ↥L →ₐ[ℚ] ↥M := IsScalarTower.toAlgHom ℚ ↥L ↥M
  have he' : ∀ (g : A ⋊[Φ] (L ≃ₐ[ℚ] L)) (x : ↥L),
      e g (ι x) = ι (SemidirectProduct.rightHom g x) := by
    intro g x
    simpa only [ι, IsScalarTower.toAlgHom_apply] using he g x
  -- the image in `Gal(M/ℚ)` of the kernel of `f`
  let H : Subgroup (↥M ≃ₐ[ℚ] ↥M) := f.ker.map e.toMonoidHom
  have hH : H.Normal := (MonoidHom.normal_ker f).map e.toMonoidHom e.surjective
  haveI : H.Normal := hH
  -- the fixed field of `H` inside `M`, pushed into `ℚ̄`
  let Mfix : IntermediateField ℚ ↥M := IntermediateField.fixedField H
  haveI hfdMfix : FiniteDimensional ℚ ↥Mfix := IntermediateField.finiteDimensional_left Mfix
  haveI hgalMfix : IsGalois ℚ ↥Mfix := IsGalois.of_fixedField_normal_subgroup H
  let M' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.lift Mfix
  let j : ↥Mfix ≃ₐ[ℚ] ↥M' := IntermediateField.liftAlgEquiv Mfix
  haveI hfdM' : FiniteDimensional ℚ ↥M' := j.toLinearEquiv.finiteDimensional
  haveI hgalM' : IsGalois ℚ ↥M' := IsGalois.of_algEquiv j
  -- `H` fixes the image of `L` under `ι`: this is `he` together with `hproj`
  have hfixmem : ∀ x : ↥L, ι x ∈ Mfix := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hσ
    show e k (ι x) = ι x
    have hrk : SemidirectProduct.rightHom k = 1 := by
      rw [← hproj k, MonoidHom.mem_ker.mp hk, map_one]
    rw [he' k x, hrk, AlgEquiv.one_apply]
  -- `ι` maps `↥L` *onto* the copy of `L` inside `M` (normality of `L/ℚ`)
  let f₀ : ↥L →ₐ[ℚ] AlgebraicClosure ℚ :=
    (IsScalarTower.toAlgHom ℚ ↥M (AlgebraicClosure ℚ)).comp ι
  have hf₀ : ∀ x : ↥L, f₀ x = (ι x : AlgebraicClosure ℚ) := fun x => by
    simp only [f₀, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      IntermediateField.algebraMap_apply]
  have hιsurj : ∀ x : ↥L, ∃ y : ↥L, ι y = ⟨x.1, hLM x.2⟩ := by
    intro x
    have hrange : f₀.fieldRange = L :=
      @AlgHom.fieldRange_of_normal ℚ (AlgebraicClosure ℚ) _ _ _ L hNrm f₀
    have hx : (x : AlgebraicClosure ℚ) ∈ f₀.fieldRange := by
      rw [hrange]; exact x.2
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext (by rw [← hf₀ y]; exact hy)⟩
  -- consequently `L ≤ M'`
  have hLM' : L ≤ M' := by
    intro x hx
    obtain ⟨y, hy⟩ := hιsurj ⟨x, hx⟩
    change x ∈ IntermediateField.lift Mfix
    refine (IntermediateField.mem_lift (F := M) (E := Mfix) (⟨x, hLM hx⟩ : ↥M)).mpr ?_
    have hmem : ι y ∈ Mfix := hfixmem y
    rwa [hy] at hmem
  -- the identification of `L` with its image in `M'`
  let g' : ↥L →ₐ[ℚ] ↥Mfix := ι.codRestrict Mfix.toSubalgebra hfixmem
  let f' : ↥L →ₐ[ℚ] ↥M' := j.toAlgHom.comp g'
  letI : Algebra ↥L ↥M' := f'.toRingHom.toAlgebra
  haveI hST' : IsScalarTower ℚ ↥L ↥M' := inferInstance
  haveI hfdL' : FiniteDimensional ↥L ↥M' := FiniteDimensional.right ℚ ↥L ↥M'
  haveI hgalL' : IsGalois ↥L ↥M' := IsGalois.tower_top_of_isGalois ℚ ↥L ↥M'
  -- the isomorphism `N ⋊[φ] G ≃* Gal(M'/ℚ)`
  let e₁ : N ⋊[φ] (L ≃ₐ[ℚ] L) ≃* (↥M' ≃ₐ[ℚ] ↥M') :=
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      ((QuotientGroup.congr f.ker H e (by simp [H])).trans
        ((IsGalois.normalAutEquivQuotient H).trans (AlgEquiv.autCongr j)))
  have key : ∀ (w : A ⋊[Φ] (L ≃ₐ[ℚ] L)) (y : ↥Mfix),
      (e₁ (f w)) (j y)
        = j ((IsGalois.normalAutEquivQuotient H (QuotientGroup.mk (e w))) y) := by
    intro w y
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f w)
        = QuotientGroup.mk w :=
      (MulEquiv.symm_apply_eq _).mpr (QuotientGroup.kerLift_mk f w).symm
    have h2 : (QuotientGroup.congr f.ker H e (by simp [H])) (QuotientGroup.mk w)
        = QuotientGroup.mk (e w) := QuotientGroup.congr_mk f.ker H e _ w
    simp only [e₁, MulEquiv.trans_apply, h1, h2]
    rfl
  have key2 : ∀ (w : A ⋊[Φ] (L ≃ₐ[ℚ] L)) (x : ↥L),
      (IsGalois.normalAutEquivQuotient H (QuotientGroup.mk (e w))) (g' x)
        = g' (SemidirectProduct.rightHom w x) := by
    intro w x
    rw [IsGalois.normalAutEquivQuotient_apply]
    refine Subtype.ext ?_
    rw [AlgEquiv.restrictNormalHom_apply,
      show ((g' x : ↥Mfix) : ↥M) = ι x from rfl,
      show ((g' (SemidirectProduct.rightHom w x) : ↥Mfix) : ↥M)
        = ι (SemidirectProduct.rightHom w x) from rfl]
    exact he' w x
  refine ⟨M', hLM', hfdM', hgalM', f'.toRingHom.toAlgebra, hST', hfdL', hgalL', e₁, ?_⟩
  intro g x
  obtain ⟨w, rfl⟩ := hf g
  have hx : (algebraMap ↥L ↥M') x = j (g' x) := rfl
  rw [hx, key w (g' x), key2 w x, hproj w]
  rfl

end Work.GenericKernelReduction
