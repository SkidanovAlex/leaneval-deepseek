import Mathlib
import Submission.Work.GenericKernelReduction.Canonical
import Submission.Work.GenericKernelReduction.inClosure_of_splitEmbeddingSolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

set_option linter.style.haveILetI false

theorem canonical_of_splitEmbeddingSolvable {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {N : Type} [Group N] [Finite N]
    {φ : (L ≃ₐ[ℚ] L) →* MulAut N} (h : Work.Fitting.SplitEmbeddingSolvable L N φ) :
    Work.GenericKernelReduction.CanonicalSplitEmbeddingSolvedInClosure L N φ := by
  classical
  obtain ⟨L', hF, hA, hFD, hG, hA2, hST, hFD2, hG2, e, he⟩ := h
  letI : Field L' := hF
  letI : Algebra ℚ L' := hA
  letI : Algebra ↥L L' := hA2
  letI : IsScalarTower ℚ ↥L L' := hST
  letI : FiniteDimensional ℚ L' := hFD
  letI : IsGalois ℚ L' := hG
  letI : FiniteDimensional ↥L L' := hFD2
  letI : IsGalois ↥L L' := hG2
  haveI hAlg : Algebra.IsAlgebraic ↥L L' := Algebra.IsAlgebraic.of_finite ↥L L'
  obtain ⟨φ', hφ'⟩ := (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := ℚ) (L := ↥L) (M := AlgebraicClosure ℚ) (E := L')) (IntermediateField.val L)
  have hφ'apply : ∀ y : ↥L, φ' (algebraMap ↥L L' y) = (y : AlgebraicClosure ℚ) := by
    intro y
    have h1 := congr_arg (fun g : ↥L →ₐ[ℚ] AlgebraicClosure ℚ => g y) hφ'
    simp only [AlgHom.domRestrict, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at h1
    exact h1
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := φ'.fieldRange
  have hLM : L ≤ M := by
    intro x hx
    rw [AlgHom.mem_fieldRange]
    exact ⟨algebraMap ↥L L' ⟨x, hx⟩, hφ'apply ⟨x, hx⟩⟩
  let algLM : Algebra ↥L ↥M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra ↥L ↥M := algLM
  haveI hSTLM : IsScalarTower ℚ ↥L ↥M := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp
  have hcoef : ∀ y : ↥L, (algebraMap ↥L ↥M y : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) :=
    fun y => rfl
  let φA : L' ≃ₐ[ℚ] ↥M := AlgEquiv.ofInjective φ' φ'.injective
  have hφAapply : ∀ a : L', (φA a : AlgebraicClosure ℚ) = φ' a :=
    fun a => AlgEquiv.ofInjective_apply φ' φ'.injective a
  have hφA : ∀ y : ↥L, φA (algebraMap ↥L L' y) = algebraMap ↥L ↥M y := by
    intro y
    apply Subtype.ext
    rw [hφAapply (algebraMap ↥L L' y), hφ'apply y]
    exact (hcoef y).symm
  let ψ : ↥M ≃ₐ[↥L] L' :=
    AlgEquiv.mk φA.symm.toEquiv (fun y z => map_mul φA.symm y z)
      (fun y z => map_add φA.symm y z) (fun r => by
        apply (AlgEquiv.symm_apply_eq φA).mpr
        exact (hφA r).symm)
  haveI hfdLM : FiniteDimensional ↥L ↥M := ψ.symm.toLinearEquiv.finiteDimensional
  haveI hgalLM : IsGalois ↥L ↥M := IsGalois.of_algEquiv ψ.symm
  haveI hfdM : FiniteDimensional ℚ ↥M := φA.toLinearEquiv.finiteDimensional
  haveI hgalM : IsGalois ℚ ↥M := IsGalois.of_algEquiv φA
  refine ⟨M, hLM, hfdM, hgalM, algLM, hSTLM, hfdLM, hgalLM, hcoef,
    e.trans (AlgEquiv.autCongr φA), ?_⟩
  intro g x
  have hsym : φA.symm (algebraMap ↥L ↥M x) = algebraMap ↥L L' x :=
    (AlgEquiv.symm_apply_eq φA).mpr (hφA x).symm
  rw [MulEquiv.trans_apply]
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  rw [hsym, he g x]
  exact hφA (SemidirectProduct.rightHom g x)

end Work.GenericKernelReduction
