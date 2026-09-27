import Mathlib

namespace Work.Drive.PushDisc

open Module

/-- The matrix `fun i j => (w i).ofLp j` associated with a tuple `w` of vectors of
`EuclideanSpace ℝ (Fin n)` has determinant equal to the determinant of `w` with respect to the
standard basis of `EuclideanSpace ℝ (Fin n)`. -/
theorem det_ofLp_eq_basisDet {n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin n)) :
    Matrix.det (fun i j => (w i).ofLp j)
      = ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det w := by
  rw [Module.Basis.det_apply, ← Matrix.det_transpose]
  apply congrArg Matrix.det
  ext i j
  rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply]
  simp

/-- **The change of coordinates.** For a linear identification
`T : F ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)` of a real vector space `F` and a basis `b` of `F` indexed by
`Fin n`, the determinant of the coordinates of a tuple `v` of vectors of `F` computed through `T`
equals the determinant of the coordinates of `v` in the basis `b`, multiplied by the *fixed* factor
`Matrix.det (fun i j => (T (b i)).ofLp j)` (the determinant of the change of coordinates). -/
theorem det_comp_eq_det_mul {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (b : Module.Basis (Fin n) ℝ F)
    (v : Fin n → F) :
    Matrix.det (fun i j => (T (v i)).ofLp j)
      = Matrix.det (fun i j => (T (b i)).ofLp j) * b.det v := by
  classical
  -- Both sides are the two alternating `Fin n`-linear forms on `F` compared on the basis `b`.
  let G : AlternatingMap ℝ F ℝ (Fin n) :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det.compLinearMap
      (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hev : ∀ w : Fin n → F, G w = Matrix.det (fun i j => (T (w i)).ofLp j) := by
    intro w
    change (((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det.compLinearMap
        (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) w
      = Matrix.det (fun i j => (T (w i)).ofLp j)
    rw [AlternatingMap.compLinearMap_apply]
    exact (det_ofLp_eq_basisDet (fun i => (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (w i))).symm
  have h3 : G v = G (⇑b) * b.det v := by
    have hv' : G v = (G (⇑b) • b.det) v :=
      DFunLike.congr_fun (show G = G (⇑b) • b.det from AlternatingMap.eq_smul_basis_det b G) v
    rw [hv', AlternatingMap.smul_apply, smul_eq_mul]
  calc Matrix.det (fun i j => (T (v i)).ofLp j) = G v := (hev v).symm
    _ = G (⇑b) * b.det v := h3
    _ = Matrix.det (fun i j => (T (b i)).ofLp j) * b.det v := by rw [hev b]

/-- The change-of-coordinates determinant of `det_comp_eq_det_mul` is non-zero: `T ∘ b` is a basis
of `EuclideanSpace ℝ (Fin n)`, hence a unit of the ring of `Fin n × Fin n` matrices. -/
theorem det_ofLp_basis_ne_zero {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (b : Module.Basis (Fin n) ℝ F) :
    Matrix.det (fun i j => (T (b i)).ofLp j) ≠ 0 := by
  classical
  let G : AlternatingMap ℝ F ℝ (Fin n) :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det.compLinearMap
      (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hev : ∀ w : Fin n → F, G w = Matrix.det (fun i j => (T (w i)).ofLp j) := by
    intro w
    change (((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det.compLinearMap
        (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) w
      = Matrix.det (fun i j => (T (w i)).ofLp j)
    rw [AlternatingMap.compLinearMap_apply]
    exact (det_ofLp_eq_basisDet (fun i => (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (w i))).symm
  have hG : G ≠ 0 := by
    intro h0
    have h0' : (((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det.compLinearMap
        (T : F →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = 0 := h0
    have h1 : ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det = 0 :=
      (AlternatingMap.compLinearEquiv_eq_zero_iff
        (((EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det)
        (T : F ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))).mp h0'
    exact Module.Basis.det_ne_zero _ h1
  exact (hev b) ▸ (AlternatingMap.map_basis_ne_zero_iff b G).mpr hG

/-- The sign of `det (T ∘ v₁) * det (T ∘ v₂)` does not depend on the coordinate system: writing a
tuple `v : Fin n → F` of a finite-dimensional real inner product space as a matrix through a linear
identification `T : F ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)` and through an arbitrary basis `b` of `F`
differs by a *fixed* non-zero factor (the determinant of the change of coordinates), so the
*positivity* of the product of two such determinants is the same for the two descriptions.
`h : m = n` is the reindexing needed because a basis of `F` has `m = finrank ℝ F` vectors while `T`
uses `n` coordinates. -/
theorem detProductSignCast {m n : ℕ} (h : m = n) {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : F ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (b : Module.Basis (Fin m) ℝ F)
    (v₁ v₂ : Fin n → F) :
    (0 < Matrix.det (fun i j => (T (v₁ i)).ofLp j) * Matrix.det (fun i j => (T (v₂ i)).ofLp j))
      ↔ 0 < b.det (v₁ ∘ Fin.cast h) * b.det (v₂ ∘ Fin.cast h) := by
  classical
  set b' : Module.Basis (Fin n) ℝ F := b.reindex (finCongr h) with hb'
  have hb'det : ∀ v : Fin n → F, b'.det v = b.det (v ∘ Fin.cast h) := by
    intro v
    rw [hb']
    exact Module.Basis.det_reindex b v (finCongr h)
  have hkey : ∀ v : Fin n → F,
      Matrix.det (fun i j => (T (v i)).ofLp j)
        = Matrix.det (fun i j => (T (b' i)).ofLp j) * b'.det v :=
    fun v => det_comp_eq_det_mul T b' v
  have hc : Matrix.det (fun i j => (T (b' i)).ofLp j) ≠ 0 :=
    det_ofLp_basis_ne_zero T b'
  have hcpos : 0 < Matrix.det (fun i j => (T (b' i)).ofLp j)
      * Matrix.det (fun i j => (T (b' i)).ofLp j) := mul_self_pos.mpr hc
  rw [hkey v₁, hkey v₂, hb'det v₁, hb'det v₂,
    show ∀ x y : ℝ,
        (Matrix.det (fun i j => (T (b' i)).ofLp j) * x)
          * (Matrix.det (fun i j => (T (b' i)).ofLp j) * y)
        = (Matrix.det (fun i j => (T (b' i)).ofLp j)
            * Matrix.det (fun i j => (T (b' i)).ofLp j)) * (x * y) from fun x y => by ring,
    mul_pos_iff_of_pos_left hcpos]

end Work.Drive.PushDisc
