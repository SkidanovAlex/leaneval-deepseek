import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.sumFibreC_cxOfReal
import Submission.Work.Whitney.cxRePart_sumFibreC
import Submission.Work.Whitney.cxImPart_sumFibreC

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000

/-!
# Complexification commutes with the direct-sum transport of the splitting

`Work.Whitney.sumFibreR k₁ k₂` and `Work.Whitney.sumFibreC k₁ k₂` are the *same* coordinate shuffle
`EuclideanSpace.finAddEquivProd.symm` (only the coefficient field differs); that fact is recorded at
the vector level by `Work.Whitney.sumFibreC_cxOfReal`.  This module upgrades it to the level of
block-diagonal endomorphisms: complexifying the transport of `(T₁, T₂)` along the real splitting is
the same as transporting `(T₁ ⊗ id, T₂ ⊗ id)` along the complex splitting.

Concretely, `Work.Whitney.transportEnd e T₁ T₂ = e ∘ (T₁ × T₂) ∘ e⁻¹`, and the statement is

`cxTrans (transportEnd sumFibreR T₁ T₂) = transportEnd sumFibreC (cxTrans T₁) (cxTrans T₂)`.

The proof reduces, via `Work.Thom.cxTrans_cxOfReal` (a `cxTrans` is determined by its values on the
real part, see `ext_of_cxOfReal`), to the vector identity `sumFibreC_cxOfReal`: on `cxOfReal u` both
sides become `cxOfReal (transportEnd sumFibreR T₁ T₂ u)`.

This is the `cxTrans`-compatibility behind the equality of the complexifications
`(Z₁ ⊕ Z₂) ⊗_ℝ ℂ = (Z₁ ⊗_ℝ ℂ) ⊕ (Z₂ ⊗_ℝ ℂ)`.
-/

namespace Work.Whitney

noncomputable section

open Work.Thom

/-- Multiplication by `i` on `ℂ^k` is the ℂ-scalar multiplication by `Complex.I`. -/
lemma cxMulI_eq_I_smul {k : ℕ} (v : EuclideanSpace ℂ (Fin k)) :
    cxMulI v = Complex.I • v := by
  ext t
  simp only [cxMulI, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

/-- A ℂ-linear endomorphism of `ℂ^k` is determined by its values on the image of the real inclusion
`cxOfReal : ℝ^k → ℂ^k`: every vector is `cxRePart v + i · cxImPart v`. -/
lemma ext_of_cxOfReal {k : ℕ} {S S' : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)}
    (h : ∀ u : EuclideanSpace ℝ (Fin k), S (cxOfReal u) = S' (cxOfReal u)) : S = S' := by
  apply ContinuousLinearMap.ext
  intro v
  conv_lhs => rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart v]
  conv_rhs => rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart v]
  rw [map_add, map_add, h, cxMulI_eq_I_smul, map_smul, map_smul, h]

theorem sumFibre_cxTrans (k₁ k₂ : ℕ)
    (T₁ : EuclideanSpace ℝ (Fin k₁) →L[ℝ] EuclideanSpace ℝ (Fin k₁))
    (T₂ : EuclideanSpace ℝ (Fin k₂) →L[ℝ] EuclideanSpace ℝ (Fin k₂)) :
    Work.Thom.cxTrans (Work.Whitney.transportEnd (Work.Whitney.sumFibreR k₁ k₂) T₁ T₂) =
      Work.Whitney.transportEnd (Work.Whitney.sumFibreC k₁ k₂)
        (Work.Thom.cxTrans T₁) (Work.Thom.cxTrans T₂) := by
  symm
  apply ext_of_cxOfReal
  intro u
  rw [cxTrans_cxOfReal, transportEnd, transportEnd]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe]
  have h1 : (sumFibreC k₁ k₂) (cxOfReal ((sumFibreR k₁ k₂).symm u).1,
        cxOfReal ((sumFibreR k₁ k₂).symm u).2) = cxOfReal u := by
    rw [sumFibreC_cxOfReal]
    congr 1
    exact (sumFibreR k₁ k₂).apply_symm_apply u
  have h2 : (sumFibreC k₁ k₂).symm (cxOfReal u)
      = (cxOfReal ((sumFibreR k₁ k₂).symm u).1,
         cxOfReal ((sumFibreR k₁ k₂).symm u).2) := by
    rw [← h1, ContinuousLinearEquiv.symm_apply_apply]
  rw [h2]
  rw [ContinuousLinearMap.coe_prodMap', Prod.map_apply, cxTrans_cxOfReal, cxTrans_cxOfReal]
  rw [sumFibreC_cxOfReal]
  congr 1

end

end Work.Whitney
