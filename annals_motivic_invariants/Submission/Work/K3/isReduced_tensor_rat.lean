import Mathlib
import Submission.Work.K3.tensorProduct_tower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.K3

/-- Auxiliary lemma: `K ⊗[ℚ] L` is reduced when `L` is a field essentially of finite type over `ℚ`.

The proof separates a transcendence basis `s` of `L` over `ℚ`.  With `F = ℚ(s)` the tensor product
`K ⊗[ℚ] F` is a domain (it is the localisation of the polynomial ring `K ⊗[ℚ] ℚ[s] ≅ K[s]`), and
`L / F` is separable, so that the base change `K(s) ⊗[F] L` is reduced by
`Algebra.FormallyUnramified.isReduced_of_field`.  The tower isomorphism
`K ⊗[ℚ] L ≅ (K ⊗[ℚ] F) ⊗[F] L` finishes the job. -/
private theorem isReduced_tensor_rat_essFT (K L : Type) [Field K] [Field L] [Algebra ℚ K]
    [Algebra ℚ L] [Algebra.EssFiniteType ℚ L] : IsReduced (TensorProduct ℚ K L) := by
  haveI : PerfectField ℚ := PerfectField.ofCharZero
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ℚ L
  have hAI : AlgebraicIndependent ℚ (Subtype.val : s → L) := hs.1
  -- the `ℚ`-algebra structure on a rational function field / intermediate field has a
  -- definitional diamond; we fix the intended instances here.
  letI : Algebra ℚ (FractionRing (MvPolynomial s ℚ)) := OreLocalization.instAlgebra
  let F0 : IntermediateField ℚ L := IntermediateField.adjoin ℚ (Set.range (Subtype.val : s → L))
  letI : Algebra ℚ ↥F0 := IntermediateField.algebra' F0
  set F : IntermediateField ℚ L := IntermediateField.adjoin ℚ (s : Set L) with hF
  haveI hsepF : Algebra.IsSeparable ↥F L := hsep
  letI : Algebra ℚ ↥F := IntermediateField.algebra' F
  letI : Module ℚ ↥F := Algebra.toModule
  -- `↥F` is the fraction field of `ℚ[s] ≅ MvPolynomial s ℚ`
  have hFeq : F0 = F :=
    (congrArg (IntermediateField.adjoin ℚ) (Subtype.range_val (s := (s : Set L)))).trans hF.symm
  have eF : FractionRing (MvPolynomial s ℚ) ≃ₐ[ℚ] ↥F :=
    (hAI.aevalEquivField).trans (IntermediateField.equivOfEq hFeq)
  -- `K ⊗[ℚ] ℚ[s]` is a domain
  haveI hBase : IsDomain (TensorProduct ℚ K (MvPolynomial s ℚ)) := by
    have e : TensorProduct ℚ K (MvPolynomial s ℚ) ≃ₐ[K] MvPolynomial s K :=
      MvPolynomial.algebraTensorAlgEquiv ℚ K
    exact Function.Injective.isDomain
      (e : TensorProduct ℚ K (MvPolynomial s ℚ) →+* MvPolynomial s K) e.injective
  -- `K ⊗[ℚ] ℚ(s)` is a domain: it is a localisation of the domain `K ⊗[ℚ] ℚ[s]`
  haveI hDomFR : IsDomain (TensorProduct ℚ K (FractionRing (MvPolynomial s ℚ))) := by
    letI : Algebra (MvPolynomial s ℚ) (TensorProduct ℚ K (MvPolynomial s ℚ)) :=
      Algebra.TensorProduct.rightAlgebra
    haveI hloc : IsLocalization
        (Algebra.algebraMapSubmonoid (TensorProduct ℚ K (MvPolynomial s ℚ))
          (nonZeroDivisors (MvPolynomial s ℚ)))
        (TensorProduct (MvPolynomial s ℚ) (TensorProduct ℚ K (MvPolynomial s ℚ))
          (FractionRing (MvPolynomial s ℚ))) :=
      IsLocalization.tensor (FractionRing (MvPolynomial s ℚ)) (nonZeroDivisors (MvPolynomial s ℚ))
    haveI hlocDom : IsDomain
        (TensorProduct (MvPolynomial s ℚ) (TensorProduct ℚ K (MvPolynomial s ℚ))
          (FractionRing (MvPolynomial s ℚ))) := by
      have hM : Algebra.algebraMapSubmonoid (TensorProduct ℚ K (MvPolynomial s ℚ))
          (nonZeroDivisors (MvPolynomial s ℚ)) ≤
          nonZeroDivisors (TensorProduct ℚ K (MvPolynomial s ℚ)) := by
        rw [Algebra.algebraMapSubmonoid, Submonoid.map_le_iff_le_comap]
        intro m hm
        exact map_mem_nonZeroDivisors _ (by
          rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
          exact Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap ℚ K)))
          hm
      exact IsLocalization.isDomain_of_le_nonZeroDivisors
        (S := TensorProduct (MvPolynomial s ℚ) (TensorProduct ℚ K (MvPolynomial s ℚ))
          (FractionRing (MvPolynomial s ℚ))) hM
    obtain ⟨e⟩ := tensorProduct_tower (R := ℚ) (S := MvPolynomial s ℚ)
      (T := FractionRing (MvPolynomial s ℚ)) (A := K)
    exact Function.Injective.isDomain
      (e.symm : TensorProduct ℚ K (FractionRing (MvPolynomial s ℚ)) →+*
        TensorProduct (MvPolynomial s ℚ) (TensorProduct ℚ K (MvPolynomial s ℚ))
          (FractionRing (MvPolynomial s ℚ)))
      e.symm.injective
  -- now the same for `↥F`
  haveI hDomF : IsDomain (TensorProduct ℚ K ↥F) := by
    have e2 : TensorProduct ℚ K (FractionRing (MvPolynomial s ℚ)) ≃ₐ[ℚ]
        TensorProduct ℚ K ↥F :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[ℚ] K) eF
    exact Function.Injective.isDomain
      (e2.symm : TensorProduct ℚ K ↥F →+* TensorProduct ℚ K (FractionRing (MvPolynomial s ℚ)))
      e2.symm.injective
  -- the base field `E = Frac (K ⊗[ℚ] ↥F)`
  letI : Algebra ↥F (TensorProduct ℚ K ↥F) := Algebra.TensorProduct.rightAlgebra
  let E := FractionRing (TensorProduct ℚ K ↥F)
  haveI : Algebra.FormallyUnramified ↥F L := Algebra.FormallyUnramified.of_isSeparable ↥F L
  haveI : Algebra.EssFiniteType ↥F L := Algebra.EssFiniteType.of_comp ℚ ↥F L
  letI : Algebra E E := Algebra.id E
  haveI hredE : IsReduced (TensorProduct ↥F E L) :=
    Algebra.FormallyUnramified.isReduced_of_field E (TensorProduct ↥F E L)
  -- descend along the injective `K ⊗[ℚ] ↥F → E`
  haveI : Module.Flat ↥F L := inferInstance
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥F (TensorProduct ℚ K ↥F) E)
        (AlgHom.id ↥F L)) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom ↥F (TensorProduct ℚ K ↥F) E).toLinearMap
      (IsFractionRing.injective (TensorProduct ℚ K ↥F) E)
  haveI hredD : IsReduced (TensorProduct ↥F (TensorProduct ℚ K ↥F) L) :=
    isReduced_of_injective _ hinj
  -- tower isomorphism back to `K ⊗[ℚ] L`
  obtain ⟨e⟩ := tensorProduct_tower (R := ℚ) (S := ↥F) (T := L) (A := K)
  exact isReduced_of_injective
    (e.symm.toRingHom : TensorProduct ℚ K L →+*
      TensorProduct ↥F (TensorProduct ℚ K ↥F) L) e.symm.injective

theorem isReduced_tensor_rat (K L : Type) [Field K] [Field L] [Algebra ℚ K]
    [Algebra ℚ L] : IsReduced (TensorProduct ℚ K L) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (R := ℚ) (C := K) (A := L) ?_
  intro B hB
  haveI : IsDomain ↥B := inferInstance
  haveI : Algebra.EssFiniteType ℚ (FractionRing ↥B) := by
    haveI : Algebra.FiniteType ℚ ↥B := (Subalgebra.fg_iff_finiteType B).mp hB
    exact Algebra.EssFiniteType.comp ℚ ↥B (FractionRing ↥B)
  haveI : IsReduced (TensorProduct ℚ K (FractionRing ↥B)) :=
    isReduced_tensor_rat_essFT K (FractionRing ↥B)
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id ℚ K)
        (IsScalarTower.toAlgHom ℚ ↥B (FractionRing ↥B))) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (IsFractionRing.injective ↥B (FractionRing ↥B))
  exact isReduced_of_injective _ hinj

end Work.K3
