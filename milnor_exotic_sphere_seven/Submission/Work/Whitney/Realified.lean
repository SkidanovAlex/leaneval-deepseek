import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.ConjDefs
import Submission.Work.Thom.realification
import Submission.Work.Thom.complexification
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The underlying real bundle `E_ℝ` of a complex bundle `E`, in the `ℝ^{2m}` presentation

`Work.Thom.realification Z` views a complex bundle `Z` as a real bundle with the *same* model fibre
`EuclideanSpace ℂ (Fin m)`.  For the complexification `E_ℝ ⊗_ℝ ℂ` and for Pontryagin classes one
wants instead the presentation with model fibre `EuclideanSpace ℝ (Fin (m + m))`, the real and
imaginary parts:

  `reImCore m : ℂ^m → ℝ^{m + m}`,   `v ↦ (re v, im v)`   (concatenated coordinates),
  `pairCxCore m : ℝ^{m + m} → ℂ^m`, `(x, y) ↦ x + i y`,

which are mutually inverse.  Then

* `Work.Whitney.realifiedCore Z` — the underlying real bundle of `Z` with model fibre `ℝ^{2m}` and
  transitions `reImCore ∘ g_{ij} ∘ pairCxCore` (i.e. the real block matrix `[[A, -B], [B, A]]` of
  `g = A + iB`), and
* `Work.Thom.complexificationCore (realifiedCore Z)` — the bundle `E_ℝ ⊗_ℝ ℂ`, the left-hand side of
  the isomorphism `E_ℝ ⊗_ℝ ℂ ≅ E ⊕ Ē` of deliverable item 4 of the WHITNEY subproject, whose right
  hand side is `Work.Whitney.whitneySum Z (Work.Whitney.conjCore Z)`.

The gauge is the constant `Work.Whitney.gaugeP` (`(a, b) ↦ (a + i b, a - i b)` in the `ℂ^m ⊕ ℂ^m`
coordinates): `P ∘ (g ⊗ id) = (g ⊕ ḡ) ∘ P`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## Real and imaginary parts, and their inverse -/

/-- `ℂ^m → ℝ^m × ℝ^m`, `v ↦ (re v, im v)`, as a real continuous linear map. -/
def reImPairCLM (m : ℕ) :
    EuclideanSpace ℂ (Fin m) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :=
  LinearMap.toContinuousLinearMap (cxRePart.prod cxImPart)

/-- `ℝ^m × ℝ^m → ℂ^m`, `(x, y) ↦ x + i y`, as a real continuous linear map. -/
def pairCxCLM (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℂ (Fin m) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) cxOfReal).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)))
    + (LinearMap.toContinuousLinearMap (𝕜 := ℝ) cxMulI).comp
        ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) cxOfReal).comp
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))))

theorem reImPairCLM_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    reImPairCLM m v = (cxRePart v, cxImPart v) := rfl

theorem pairCxCLM_apply (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    pairCxCLM m w = cxOfReal w.1 + cxMulI (cxOfReal w.2) := rfl

/-- The inverse law on `ℝ^m × ℝ^m`. -/
theorem reImPairCLM_apply_pairCxCLM (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    reImPairCLM m (pairCxCLM m w) = w := by
  rcases w with ⟨x, y⟩
  show (cxRePart (pairCxCLM m (x, y)), cxImPart (pairCxCLM m (x, y))) = (x, y)
  ext <;> simp [pairCxCLM]

/-- The inverse law on `ℂ^m`. -/
theorem pairCxCLM_apply_reImPairCLM (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    pairCxCLM m (cxRePart v, cxImPart v) = v := by
  rw [pairCxCLM_apply, cxOfReal_cxRePart_add_cxMulI_cxImPart]

/-! ## The `ℝ^{2m}` presentation -/

/-- `ℂ^m → ℝ^{m+m}`: the real and imaginary parts, concatenated. -/
def reImCore (m : ℕ) : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + m)) :=
  LinearMap.toContinuousLinearMap
    ((sumFibreR m m).toLinearEquiv.toLinearMap.comp (reImPairCLM m).toLinearMap)

/-- `ℝ^{m+m} → ℂ^m`: read the two halves as real and imaginary parts. -/
def pairCxCore (m : ℕ) : EuclideanSpace ℝ (Fin (m + m)) →L[ℝ] EuclideanSpace ℂ (Fin m) :=
  LinearMap.toContinuousLinearMap
    ((pairCxCLM m).toLinearMap.comp (sumFibreR m m).symm.toLinearEquiv.toLinearMap)

theorem reImCore_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    reImCore m v = sumFibreR m m (cxRePart v, cxImPart v) := rfl

theorem pairCxCore_apply (m : ℕ) (w : EuclideanSpace ℝ (Fin (m + m))) :
    pairCxCore m w = pairCxCLM m ((sumFibreR m m).symm w) := rfl

/-- The inverse law `pairCxCore ∘ reImCore = id`. -/
theorem reImCore_pairCxCore (m : ℕ) (w : EuclideanSpace ℝ (Fin (m + m))) :
    reImCore m (pairCxCore m w) = w := by
  rw [reImCore_apply, pairCxCore_apply]
  have h : reImPairCLM m (pairCxCLM m ((sumFibreR m m).symm w))
      = (sumFibreR m m).symm w := reImPairCLM_apply_pairCxCLM m _
  have h' : (cxRePart (pairCxCLM m ((sumFibreR m m).symm w)),
      cxImPart (pairCxCLM m ((sumFibreR m m).symm w))) = (sumFibreR m m).symm w := h
  rw [h']
  exact (sumFibreR m m).apply_symm_apply w

/-- The inverse law `reImCore ∘ pairCxCore = id`. -/
theorem pairCxCore_reImCore (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    pairCxCore m (reImCore m v) = v := by
  rw [pairCxCore_apply, reImCore_apply, (sumFibreR m m).symm_apply_apply]
  exact pairCxCLM_apply_reImPairCLM m v

/-! ## The underlying real bundle -/

/-- **The real-linear isomorphism `ℂ^m ≅ ℝ^{m+m}`** given by the real and imaginary parts
(concatenated coordinates).  Its inverse is `Work.Whitney.pairCxCore`. -/
def reImEquiv (m : ℕ) : EuclideanSpace ℂ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + m)) where
  toFun := reImCore m
  invFun := pairCxCore m
  map_add' := (reImCore m).map_add
  map_smul' := (reImCore m).map_smul
  left_inv := pairCxCore_reImCore m
  right_inv := reImCore_pairCxCore m

@[simp] theorem reImEquiv_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    reImEquiv m v = reImCore m v := rfl

@[simp] theorem reImEquiv_symm_apply (m : ℕ) (w : EuclideanSpace ℝ (Fin (m + m))) :
    (reImEquiv m).symm w = pairCxCore m w := rfl

/-- **The underlying real bundle `E_ℝ` of a complex bundle `E`**, in the `ℝ^{2m}` presentation:
the realification of `E` with its model fibre `ℂ^m` transported to `ℝ^{m+m}` along
`Work.Whitney.reImEquiv` (real and imaginary parts).  Its transitions are
`reImCore ∘ g_{ij} ∘ pairCxCore`, i.e. the real block matrix `[[A, -B], [B, A]]` of `g = A + iB`. -/
def realifiedCore {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin (m + m))) ι :=
  Work.TangentClasses.RealBundle.mapFibre (reImEquiv m) (realification Z)

theorem realifiedCore_baseSet {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) :
    (realifiedCore Z).baseSet i = Z.baseSet i := by
  rw [realifiedCore, Work.TangentClasses.RealBundle.mapFibre_baseSet, realification_baseSet]

theorem realifiedCore_indexAt {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (x : B) :
    (realifiedCore Z).indexAt x = Z.indexAt x := by
  rw [realifiedCore, Work.TangentClasses.RealBundle.mapFibre_indexAt, realification_indexAt]

end

end Work.Whitney
