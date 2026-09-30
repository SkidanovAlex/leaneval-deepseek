import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Orthogonal matrices preserve Lebesgue measure

The lemma `Work.BW.measurePreservingOrthogonal`: if `M` is a real orthogonal matrix
(`Mᵀ * M = 1`), then the linear map `u ↦ M.mulVec u` preserves Lebesgue measure on
`Fin n → ℝ`.

The measure `volume` on `Fin n → ℝ` is the product (Haar) measure.  The matrix `M` is an
isometry for the Euclidean (L²) norm, hence measure preserving; the one subtlety is that the
*default* norm on `Fin n → ℝ` is the sup norm, not the L² norm, so we transfer the statement
across the volume-preserving linear equivalence `WithLp.toLp 2` onto `EuclideanSpace ℝ (Fin n)`,
where the general theorem `LinearIsometryEquiv.measurePreserving` applies.
-/

namespace Work.BW

open MeasureTheory Matrix WithLp

/-- An orthogonal matrix preserves the sum of squares of the coordinates of a vector. -/
lemma sum_sq_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ * M = 1)
    (y : Fin n → ℝ) : ∑ i, (M.mulVec y i) ^ 2 = ∑ i, y i ^ 2 := by
  have h1 : ∑ i, (M.mulVec y i) ^ 2 = dotProduct (M.mulVec y) (M.mulVec y) := by
    simp [dotProduct, sq]
  have h2 : dotProduct (M.mulVec y) (M.mulVec y) = dotProduct y y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hM,
      Matrix.one_mulVec]
  have h3 : dotProduct y y = ∑ i, y i ^ 2 := by
    simp [dotProduct, sq]
  rw [h1, h2, h3]

/-- The linear map `x ↦ toLp (M.mulVec (ofLp x))` on `EuclideanSpace ℝ (Fin n)` is an isometry
when `M` is orthogonal. -/
lemma norm_toLp_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ * M = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 (M.mulVec (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin n))‖ = ‖x‖ := by
  have hsq : ‖(WithLp.toLp 2 (M.mulVec (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin n))‖ ^ 2
      = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    exact sum_sq_mulVec M hM (WithLp.ofLp x)
  nlinarith [norm_nonneg (WithLp.toLp 2 (M.mulVec (WithLp.ofLp x)) : EuclideanSpace ℝ (Fin n)),
    norm_nonneg x]

theorem measurePreservingOrthogonal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.transpose * M = 1) :
    MeasureTheory.MeasurePreserving (fun u : Fin n → ℝ => M.mulVec u)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
  -- The linear map induced on the Euclidean space by `M`.
  let g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
      (M.mulVecLin.comp (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap)
  have hg : ∀ x, g x = WithLp.toLp 2 (M.mulVec (WithLp.ofLp x)) := by
    intro x
    show (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
        (M.mulVecLin ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) x)) =
      WithLp.toLp 2 (M.mulVec (WithLp.ofLp x))
    rw [WithLp.coe_linearEquiv]
    rfl
  -- Package it as a linear isometry equivalence.
  let li : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometry.mk g (fun x => by rw [hg x]; exact norm_toLp_mulVec M hM x)
  let T : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    li.toLinearIsometryEquiv rfl
  have hT : ∀ x, T x = WithLp.toLp 2 (M.mulVec (WithLp.ofLp x)) := by
    intro x
    rw [LinearIsometry.toLinearIsometryEquiv_apply]
    exact hg x
  -- Conjugate by the volume preserving linear equivalences `toLp`/`ofLp`.
  have hmp : MeasureTheory.MeasurePreserving
      (fun u : Fin n → ℝ => WithLp.ofLp (T (WithLp.toLp 2 u)))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) :=
    (PiLp.volume_preserving_ofLp (Fin n)).comp
      ((LinearIsometryEquiv.measurePreserving T).comp (PiLp.volume_preserving_toLp (Fin n)))
  have hfun : (fun u : Fin n → ℝ => M.mulVec u)
      = (fun u : Fin n → ℝ => WithLp.ofLp (T (WithLp.toLp 2 u))) := by
    funext u
    rw [hT (WithLp.toLp 2 u), WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  rw [hfun]
  exact hmp

end Work.BW
