import Mathlib
import Submission.Work.Whitney.Realified

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The determinant of complex conjugation on `ℂ^m` (as a real endomorphism)

The fibrewise conjugation `Work.Whitney.conjC m` of `ℂ^m` is an `ℝ`-linear endomorphism; its
determinant is `(-1)^m`.  This is what turns the real bundle isomorphism
`realification Z̄ ≅ realification Z` (given by the conjugation gauge) into a *sign rule* for the
top Chern class: `c_m(Z̄) = (-1)^m c_m(Z)`.

The computation is a change of basis: in the real and imaginary part coordinates
`Work.Whitney.reImPairLinearEquiv : ℂ^m ≃ₗ[ℝ] ℝ^m × ℝ^m`, conjugation is `(x, y) ↦ (x, -y)`, i.e.
`LinearMap.id.prodMap (-LinearMap.id)`, whose determinant is `1 · (-1)^m`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {m : ℕ}

/-- Conjugation does not change the real part. -/
theorem cxRePart_conjC (v : EuclideanSpace ℂ (Fin m)) :
    cxRePart (conjC m v) = cxRePart v := by
  ext i
  simp [conjC_coord, cxRePart]

/-- Conjugation negates the imaginary part. -/
theorem cxImPart_conjC (v : EuclideanSpace ℂ (Fin m)) :
    cxImPart (conjC m v) = -cxImPart v := by
  ext i
  simp [conjC_coord, cxImPart]

/-- `ℂ^m ≃ₗ[ℝ] ℝ^m × ℝ^m` (real and imaginary parts), as a **linear equivalence**. -/
def reImPairLinearEquiv (m : ℕ) :
    EuclideanSpace ℂ (Fin m) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) where
  toFun := reImPairCLM m
  invFun := pairCxCLM m
  map_add' := (reImPairCLM m).map_add
  map_smul' := (reImPairCLM m).map_smul
  left_inv v := by
    show pairCxCLM m (reImPairCLM m v) = v
    exact pairCxCLM_apply_reImPairCLM m v
  right_inv w := by
    show reImPairCLM m (pairCxCLM m w) = w
    exact reImPairCLM_apply_pairCxCLM m w

@[simp] theorem reImPairLinearEquiv_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    reImPairLinearEquiv m v = (cxRePart v, cxImPart v) := rfl

@[simp] theorem reImPairLinearEquiv_symm_apply (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    (reImPairLinearEquiv m).symm w = cxOfReal w.1 + cxMulI (cxOfReal w.2) := rfl

/-- In the real/imaginary coordinates, conjugation is `(x, y) ↦ (x, -y)`. -/
theorem reImPairLinearEquiv_conjC (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    reImPairLinearEquiv m (conjC m ((reImPairLinearEquiv m).symm w)) = (w.1, -w.2) := by
  simp only [reImPairLinearEquiv_symm_apply, reImPairLinearEquiv_apply, cxRePart_conjC,
    cxImPart_conjC, cxRePart_cxOfReal, cxImPart_cxOfReal, cxRePart_cxMulI, cxImPart_cxMulI]
  simp

/-- **The determinant of complex conjugation on `ℂ^m` is `(-1)^m`.** -/
theorem det_conjC (m : ℕ) : LinearMap.det (conjC m) = (-1 : ℝ) ^ m := by
  have hconj := LinearMap.det_conj (f := conjC m) (e := reImPairLinearEquiv m)
  rw [← hconj]
  have hfun : ((reImPairLinearEquiv m : EuclideanSpace ℂ (Fin m) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))) ∘ₗ conjC m ∘ₗ
        ((reImPairLinearEquiv m).symm : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →ₗ[ℝ]
          EuclideanSpace ℂ (Fin m)))
      = LinearMap.prodMap (LinearMap.id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _)
          (-LinearMap.id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _) := by
    apply LinearMap.ext
    intro w
    exact reImPairLinearEquiv_conjC m w
  rw [hfun, LinearMap.det_prodMap]
  have hneg : (-LinearMap.id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
      = (-1 : ℝ) • (LinearMap.id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _) := by
    ext x
    simp
  rw [hneg, LinearMap.det_smul]
  simp [finrank_euclideanSpace_fin]

end

end Work.Whitney
