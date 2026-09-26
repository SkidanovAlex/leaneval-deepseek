import Mathlib
import Submission.Work.SG.AffCoord

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

noncomputable section

/-! ### Auxiliary facts about the coordinate model `matOf`

These are the ingredients of `matOf_affCoord`: the standard basis in coordinates, the
coordinate form of `matOf`, and the fact that a matrix is determined by its action on
coordinate vectors.  (The names are prefixed `matOf_aux_` so that this file never collides
with the growing coordinate-model API in `Submission.Work.SG.AffCoord`.) -/

/-- The `j`-th standard basis vector has the `j`-th unit coordinate vector. -/
theorem matOf_aux_stdB_ofLp (j : Fin 3) : (stdB j).ofLp = Pi.single j 1 := by
  ext k
  rw [← stdB_repr_apply, Module.Basis.repr_self_apply, Pi.single_apply]
  by_cases h : k = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Coordinate form of `matOf`: applying `matOf g` to the coordinates of `x` gives the
coordinates of `g.linear x`. -/
theorem matOf_aux_mulVec_ofLp (g : AffineGroup 3) (x : E 3) :
    matOf g *ᵥ x.ofLp = (g.linear x).ofLp := by
  have h := LinearMap.toMatrix_mulVec_repr stdB stdB (g.linear : E 3 →ₗ[ℝ] E 3) x
  rw [stdB_repr, stdB_repr] at h
  exact h

/-- Conversely, a matrix acting on coordinates as `v ↦ M *ᵥ v` is the matrix of the linear map
it represents. -/
theorem matOf_aux_toMatrix_eq_of_agree (f : E 3 →ₗ[ℝ] E 3) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ v : Fin 3 → ℝ, WithLp.toLp 2 (M *ᵥ v) = f (WithLp.toLp 2 v)) :
    LinearMap.toMatrix stdB stdB f = M := by
  ext i j
  rw [LinearMap.toMatrix_apply, stdB_repr_apply]
  have h2 : (f (stdB j)).ofLp = M *ᵥ (stdB j).ofLp := by
    have hh := h (stdB j).ofLp
    rw [WithLp.toLp_ofLp] at hh
    rw [← hh, WithLp.ofLp_toLp]
  rw [h2, matOf_aux_stdB_ofLp, Matrix.mulVec_single_one, Matrix.col_apply]

/-- An affine equivalence sends `x` to `g.linear x + g 0`. -/
theorem matOf_aux_apply_eq_linear_add (g : AffineGroup 3) (x : E 3) :
    g x = g.linear x + g 0 := by
  have h := AffineMap.map_vadd (g : E 3 →ᵃ[ℝ] E 3) (0 : E 3) x
  simpa using h

/-- Pointwise coordinate formula for an affine equivalence. -/
theorem matOf_aux_apply (g : AffineGroup 3) (x : E 3) :
    g x = WithLp.toLp 2 (Matrix.mulVec (matOf g) x.ofLp + (g 0).ofLp) := by
  rw [WithLp.ext_iff, WithLp.ofLp_toLp, matOf_aux_apply_eq_linear_add, WithLp.ofLp_add,
    matOf_aux_mulVec_ofLp]

/-- The linear part acts by matrix-vector multiplication on coordinates. -/
theorem matOf_aux_linear_mulVec (g : AffineGroup 3) (v : Fin 3 → ℝ) :
    WithLp.toLp 2 (Matrix.mulVec (matOf g) v) = g.linear (WithLp.toLp 2 v) := by
  have h := matOf_aux_mulVec_ofLp g (WithLp.toLp 2 v)
  rw [WithLp.ofLp_toLp] at h
  rw [h, WithLp.toLp_ofLp]

/-- `matOf` is multiplicative. -/
theorem matOf_aux_mul (g h : AffineGroup 3) : matOf (g * h) = matOf g * matOf h := by
  have hlin : ((g * h).linear : E 3 →ₗ[ℝ] E 3)
      = (g.linear : E 3 →ₗ[ℝ] E 3) * (h.linear : E 3 →ₗ[ℝ] E 3) := rfl
  show LinearMap.toMatrix stdB stdB ((g * h).linear : E 3 →ₗ[ℝ] E 3)
     = LinearMap.toMatrix stdB stdB (g.linear : E 3 →ₗ[ℝ] E 3)
       * LinearMap.toMatrix stdB stdB (h.linear : E 3 →ₗ[ℝ] E 3)
  rw [hlin, LinearMap.toMatrix_mul]

/-- `matOf` sends the identity to the identity matrix. -/
theorem matOf_aux_one : matOf (1 : AffineGroup 3) = 1 := by
  show LinearMap.toMatrix stdB stdB (1 : E 3 →ₗ[ℝ] E 3) = 1
  exact LinearMap.toMatrix_one stdB

/-- `matOf` preserves determinants. -/
theorem matOf_aux_det (g : AffineGroup 3) :
    ((matOf g).det : ℝ) = ((g.linear).det : ℝ) := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix stdB (g.linear : E 3 →ₗ[ℝ] E 3)]
  rfl

/-- `matOf` commutes with inversion. -/
theorem matOf_aux_inv (g : AffineGroup 3) : matOf g⁻¹ = (matOf g)⁻¹ := by
  have h1 : matOf g * matOf g⁻¹ = 1 := by
    rw [← matOf_aux_mul, mul_inv_cancel, matOf_aux_one]
  exact (Matrix.inv_eq_right_inv h1).symm

/-- `linOfMat` as a linear map acts by matrix-vector multiplication on coordinates. -/
theorem matOf_aux_linOfMat_coe (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (x : E 3) :
    (↑(linOfMat M hM) : E 3 →ₗ[ℝ] E 3) x = WithLp.toLp 2 (M *ᵥ x.ofLp) := rfl

/-- `affOfMat` is a section of `matOf`. -/
theorem matOf_aux_affOfMat (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (v : Fin 3 → ℝ) :
    matOf (affOfMat M hM v) = M :=
  matOf_aux_toMatrix_eq_of_agree ((affOfMat M hM v).linear : E 3 →ₗ[ℝ] E 3) M fun w => by
    rw [affOfMat_linear, matOf_aux_linOfMat_coe, WithLp.ofLp_toLp]

/-- Uniqueness of the coordinate representation `x ↦ M *ᵥ x.ofLp + v`. -/
theorem matOf_aux_unique (g : AffineGroup 3) (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (h : ∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec M x.ofLp + v)) :
    matOf g = M ∧ (g 0).ofLp = v := by
  have h0 : (g 0).ofLp = v := by
    have hh := congrArg WithLp.ofLp (h 0)
    simpa using hh
  have hlin : ∀ w : Fin 3 → ℝ,
      WithLp.toLp 2 (Matrix.mulVec M w) = g.linear (WithLp.toLp 2 w) := by
    intro w
    have h1 := h (WithLp.toLp 2 w)
    rw [WithLp.ofLp_toLp] at h1
    have h2 := matOf_aux_apply g (WithLp.toLp 2 w)
    rw [WithLp.ofLp_toLp, h0] at h2
    rw [h1] at h2
    have h3 : M *ᵥ w + v = matOf g *ᵥ w + v := WithLp.toLp_injective 2 h2
    have h4 : M *ᵥ w = matOf g *ᵥ w := add_right_cancel h3
    rw [h4, matOf_aux_linear_mulVec]
  exact ⟨matOf_aux_toMatrix_eq_of_agree _ M hlin, h0⟩

/-- The coordinate model of `AffineGroup 3 = E 3 ≃ᵃ[ℝ] E 3`: the standard-basis matrix `matOf g`
of the linear part, the pointwise formula `g x = M x + g 0`, multiplicativity, determinant,
behaviour on the explicitly constructed maps `affOfMat`, and uniqueness of the representation
`x ↦ M *ᵥ x.ofLp + v`. -/
theorem matOf_affCoord :
    (∀ (g : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3)
      (x : LeanEval.Geometry.SpaceGroupsProblem.E 3),
      g x = WithLp.toLp 2 (Matrix.mulVec (Work.SG.matOf g) x.ofLp + (g 0).ofLp)) ∧
    (∀ (g : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3) (v : Fin 3 → ℝ),
      WithLp.toLp 2 (Matrix.mulVec (Work.SG.matOf g) v) =
        g.linear (WithLp.toLp 2 v)) ∧
    (∀ g h : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3,
      Work.SG.matOf (g * h) = Work.SG.matOf g * Work.SG.matOf h) ∧
    (Work.SG.matOf (1 : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3) = 1) ∧
    (∀ (g : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3),
      ((Work.SG.matOf g).det : ℝ) = ((g.linear).det : ℝ)) ∧
    (∀ (g : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3),
      Work.SG.matOf g⁻¹ = (Work.SG.matOf g)⁻¹) ∧
    (∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) (v : Fin 3 → ℝ),
      Work.SG.matOf (Work.SG.affOfMat M hM v) = M) ∧
    (∀ (g : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3)
      (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ),
      (∀ x : LeanEval.Geometry.SpaceGroupsProblem.E 3,
        g x = WithLp.toLp 2 (Matrix.mulVec M x.ofLp + v)) →
      Work.SG.matOf g = M ∧ (g 0).ofLp = v) :=
  ⟨matOf_aux_apply, matOf_aux_linear_mulVec, matOf_aux_mul, matOf_aux_one, matOf_aux_det,
    matOf_aux_inv, matOf_aux_affOfMat, matOf_aux_unique⟩

end

end Work.SG
