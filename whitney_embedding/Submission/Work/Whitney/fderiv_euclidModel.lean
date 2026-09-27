import Mathlib
import Submission.Work.Whitney.EuclidModel

/-!
# The derivative of the transported and scaled model `euclidModel`

`Work.Whitney.euclidModel n lam β` is the map
`u ↦ pairToE n (scaledModel n lam β (euclidOfLp n u))` on `EuclideanSpace ℝ (Fin n)`, obtained from
a model `β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)` by

* scaling `x ↦ (1/lam) • β (lam • x)` (this keeps the double point pair of `β` but moves it and
  shrinks its support), followed by
* transporting the two components across the linear isomorphisms
  `euclidOfLp n : EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` and `pairToE n`.

This file computes its Fréchet derivative.  The scaling factors cancel: the derivative is the
transport `pairToE n` of the derivative of `β` at the *scaled* point `lam • euclidOfLp n u`.

The computation is phrased with continuous linear equivalences, because the unconditional
chain rule (`ContinuousLinearEquiv.comp_fderiv`, `ContinuousLinearEquiv.comp_right_fderiv`) is
only available for isomorphisms: writing `euclidModel` as `P ∘ (T ∘ β ∘ S) ∘ L` with `P`, `T`,
`S`, `L` continuous linear equivalences gives the identity *without* any differentiability
hypothesis, which is exactly what the statement demands (`fderiv` is the zero map off the set of
differentiability points, and the two sides vanish simultaneously).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- Scalar multiplication by a nonzero real number as a continuous linear equivalence. -/
noncomputable def smulCLE (M : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : ℝ) (hc : c ≠ 0) : M ≃L[ℝ] M :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)

lemma smulCLE_coe (M : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : ℝ) (hc : c ≠ 0) :
    (smulCLE M c hc : M →L[ℝ] M) = c • ContinuousLinearMap.id ℝ M := by
  ext x
  simp [smulCLE]

lemma smulCLE_fun (M : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : ℝ) (hc : c ≠ 0) (x : M) : (smulCLE M c hc : M → M) x = c • x := by
  simp [smulCLE]

/-- The scaling factors of `scaledModel` cancel on the level of derivatives: for a nonzero `lam`,
composing `X` with multiplication by `lam` and then multiplying by `1/lam` returns `X`. -/
lemma scale_cancel {n : ℕ} {lam : ℝ} (hlam : lam ≠ 0)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (X : (Fin n → ℝ) →L[ℝ] G) :
    (smulCLE G (1 / lam) (by rw [one_div]; exact inv_ne_zero hlam) : G →L[ℝ] G).comp
      (X.comp (smulCLE (Fin n → ℝ) lam hlam : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) = X := by
  rw [smulCLE_coe, smulCLE_coe]
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul]
  rw [smul_smul, show lam * (1 / lam) = 1 by field_simp, one_smul]

/-- **The derivative of the scaled model** `x ↦ (1/lam) • β (lam • x)` (for `lam ≠ 0`): the
scaling factors cancel, leaving the derivative of `β` at the scaled point. -/
lemma fderiv_scaledModel {n : ℕ} {lam : ℝ} (hlam : lam ≠ 0)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (x : Fin n → ℝ) :
    fderiv ℝ (scaledModel n lam β) x = fderiv ℝ β (lam • x) := by
  let S : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := smulCLE (Fin n → ℝ) lam hlam
  let T : ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
    smulCLE ((Fin n → ℝ) × (Fin n → ℝ)) (1 / lam) (by rw [one_div]; exact inv_ne_zero hlam)
  have hS : ∀ y, (S : (Fin n → ℝ) → (Fin n → ℝ)) y = lam • y := fun y => by simp [S, smulCLE]
  have hT : ∀ z : (Fin n → ℝ) × (Fin n → ℝ), (T : _ → _) z = (1 / lam) • z :=
    fun z => by simp [T, smulCLE]
  have hfun : scaledModel n lam β = (T : _ → _) ∘ (β ∘ (S : _ → _)) := by
    funext y
    simp only [Function.comp_apply, scaledModel_apply]
    rw [hS, hT]
  rw [hfun]
  rw [ContinuousLinearEquiv.comp_fderiv (iso := T) (f := β ∘ (S : _ → _)) (x := x)]
  rw [ContinuousLinearEquiv.comp_right_fderiv (iso := S) (f := β) (x := x)]
  rw [← hS]
  exact scale_cancel hlam (fderiv ℝ β ((S : (Fin n → ℝ) → (Fin n → ℝ)) x))

/-- The componentwise transport `pairToE n`, packaged as a continuous linear equivalence. -/
noncomputable def pairToECLE (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  { toLinearEquiv :=
      { toFun := pairToE n
        map_add' := (pairToE n).map_add
        map_smul' := (pairToE n).map_smul
        invFun := pairOfE n
        left_inv := fun z => by simp
        right_inv := fun z => by simp }
    continuous_toFun := (pairToE n).continuous
    continuous_invFun := (pairOfE n).continuous }

/-- **Chain rule along the transport and the linear isomorphisms**: the derivative of
`euclidModel n lam β` is `pairToE n` composed with the derivative of `scaledModel` at
`euclidOfLp n u`, composed with `euclidOfLp n`.  Here no differentiability hypothesis on `β` is
needed, because the chain rule for continuous linear *equivalences* is unconditional. -/
lemma fderiv_euclidModel_apply {n : ℕ} {lam : ℝ}
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (u : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (euclidModel n lam β) u =
      (pairToE n).comp ((fderiv ℝ (scaledModel n lam β) (euclidOfLp n u)).comp (euclidOfLp n)) := by
  let PE : ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := pairToECLE n
  let LE : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hPE : (PE : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) = pairToE n := rfl
  have hLE : (LE : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)) = euclidOfLp n := rfl
  have hLEf : (LE : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) = euclidOfLp n := by
    funext x; rfl
  have hPEf : (PE : ((Fin n → ℝ) × (Fin n → ℝ)) →
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) = pairToE n := by
    funext x; rfl
  have hfun : euclidModel n lam β = (PE : _ → _) ∘ (scaledModel n lam β ∘ (LE : _ → _)) := by
    funext u
    simp only [Function.comp_apply]
    rw [hPEf, hLEf]
    rfl
  rw [hfun]
  rw [ContinuousLinearEquiv.comp_fderiv (iso := PE)]
  rw [ContinuousLinearEquiv.comp_right_fderiv (iso := LE)]
  rw [hPE, hLE, hLEf]

/-- **The derivative of the transported and scaled model** `Work.Whitney.euclidModel`
(`Submission/Work/Whitney/EuclidModel.lean`): the scaling factors cancel, so the derivative is the
transport `pairToE` of the derivative of `β` at the scaled point. -/
theorem fderiv_euclidModel {n : ℕ} {lam : ℝ}
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hlam : lam ≠ 0) (u : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (Work.Whitney.euclidModel n lam β) u =
      (Work.Whitney.pairToE n).comp
        ((fderiv ℝ β (lam • Work.Whitney.euclidOfLp n u)).comp (Work.Whitney.euclidOfLp n)) := by
  rw [fderiv_euclidModel_apply]
  rw [fderiv_scaledModel (n := n) (lam := lam) hlam β (euclidOfLp n u)]

end Work.Whitney
