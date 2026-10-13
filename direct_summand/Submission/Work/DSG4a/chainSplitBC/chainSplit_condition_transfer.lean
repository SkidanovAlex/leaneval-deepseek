import Mathlib
import Submission.Work.DSG4a.chainSplitBC.bridge
import Submission.Work.DSG4a.CSB_Defs

namespace Work.DSG4a.chainSplitBC

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct
set_option backward.isDefEq.respectTransparency false
universe u

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- **Naturality of the flavour bridge `extTensorEquiv` with respect to the differential.**

The base-changed differential `(baseChangeComplex P).d (-1) 0` is the transport of the base change
of the differential `(P.d (-1) 0).hom.baseChange A'` across `extTensorEquiv`.  This is the
`y`-form of the statement: the inverse bridge on the degree-`0` piece intertwines the base change
of the differential with the differential of the base-changed complex. -/
theorem extTensorEquiv_symm_baseChange (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∀ y : A' ⊗[A] ↥(P.X (-1)),
      (extTensorEquiv (P.X 0)).symm (((P.d (-1) 0).hom.baseChange A') y)
        = (Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0
            ((extTensorEquiv (P.X (-1))).symm y) := by
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, extTensorEquiv_symm_tmul, extTensorEquiv_symm_tmul,
      baseChangeComplex_d_tmul]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **Naturality of the flavour bridge `extTensorEquiv` with respect to the differential**, in the
direction used to transfer a functional on the base-changed complex to one on the algebra tensor
product. -/
theorem extTensorEquiv_baseChangeComplex_d (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (z : ↥((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).X (-1))) :
    extTensorEquiv (P.X 0) ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0 z)
      = ((P.d (-1) 0).hom.baseChange A') (extTensorEquiv (P.X (-1)) z) := by
  have h := extTensorEquiv_symm_baseChange (A := A) (A' := A') P (extTensorEquiv (P.X (-1)) z)
  rw [LinearEquiv.symm_apply_apply] at h
  calc extTensorEquiv (P.X 0) ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0 z)
      = extTensorEquiv (P.X 0) ((extTensorEquiv (P.X 0)).symm
          (((P.d (-1) 0).hom.baseChange A') (extTensorEquiv (P.X (-1)) z))) := by rw [← h]
    _ = ((P.d (-1) 0).hom.baseChange A') (extTensorEquiv (P.X (-1)) z) :=
        LinearEquiv.apply_symm_apply _ _

theorem chainSplit_condition_transfer {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (P : CochainComplex (ModuleCat.{u} A) ℤ) (x : ↥(P.X 0)) :
    (∃ s : ↥((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).X 0) →ₗ[A'] A',
        (s.comp ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0).hom = 0 ∧
          s ((1 : A') ⊗ₜ[A, algebraMap A A'] x) = 1)) ↔
      ∃ s : (A' ⊗[A] ↥(P.X 0)) →ₗ[A'] A',
        s.comp ((P.d (-1) 0).hom.baseChange A') = 0 ∧ s ((1 : A') ⊗ₜ[A] x) = 1 := by
  constructor
  · rintro ⟨s, hs0, hsx⟩
    refine ⟨s.comp (extTensorEquiv (P.X 0)).symm.toLinearMap, ?_, ?_⟩
    · apply LinearMap.ext; intro y
      show s ((extTensorEquiv (P.X 0)).symm (((P.d (-1) 0).hom.baseChange A') y)) = 0
      rw [extTensorEquiv_symm_baseChange P y]
      have hh := DFunLike.congr_fun hs0 ((extTensorEquiv (P.X (-1))).symm y)
      show (s.comp ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0).hom)
          ((extTensorEquiv (P.X (-1))).symm y) = 0
      exact hh
    · show s ((extTensorEquiv (P.X 0)).symm ((1 : A') ⊗ₜ[A] x)) = 1
      rw [extTensorEquiv_symm_tmul]
      exact hsx
  · rintro ⟨s, hs0, hsx⟩
    refine ⟨s.comp (extTensorEquiv (P.X 0)).toLinearMap, ?_, ?_⟩
    · apply LinearMap.ext; intro z
      show s ((extTensorEquiv (P.X 0))
        ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0 z)) = 0
      rw [extTensorEquiv_baseChangeComplex_d P z]
      have hh := DFunLike.congr_fun hs0 (extTensorEquiv (P.X (-1)) z)
      show (s.comp ((P.d (-1) 0).hom.baseChange A')) (extTensorEquiv (P.X (-1)) z) = 0
      exact hh
    · show s ((extTensorEquiv (P.X 0)) ((1 : A') ⊗ₜ[A, algebraMap A A'] x)) = 1
      rw [extTensorEquiv_tmul]
      exact hsx

end Work.DSG4a.chainSplitBC
