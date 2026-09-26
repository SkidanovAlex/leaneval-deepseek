import Mathlib
import Submission.Work.SG.Defs

/-! # Realisation constructions for `Work.SG.exists_realization`

Shared definitions used to build, for an integral datum `(P, τ)`, a group of Euclidean motions
whose affine image is `sgSet P τ` after conjugation by `x ↦ M⁻¹ x`.

Everything here is deliberately kept free of any hypothesis on `P`: the orthogonality of the
matrix `oConj M A = M · A · M⁻¹` is passed in as a proof argument, so a change of `M` never
changes the statements below.  `idxFun` is the (junk-valued off `P`) index function
`(A, n) ↦ (x ↦ M A M⁻¹ x + M (τ A + n))`. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open Matrix

/-- Real `3 × 3` matrices. -/
abbrev RMat := Matrix (Fin 3) (Fin 3) ℝ

/-- The real matrix underlying an integer matrix. -/
def realMat (A : IMat) : RMat := A.map (Int.cast : ℤ → ℝ)

@[simp] lemma realMat_mul (A B : IMat) : realMat (A * B) = realMat A * realMat B := by
  ext i j; simp [realMat, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

@[simp] lemma realMat_one : realMat (1 : IMat) = 1 := by
  ext i j; simp [realMat, Matrix.one_apply]

@[simp] lemma map_intCast_one : ((1 : IMat).map (Int.cast : ℤ → ℝ)) = 1 := by
  ext i j; simp [Matrix.one_apply]

lemma realMat_injective : Function.Injective realMat :=
  Matrix.map_injective Int.cast_injective

lemma realMat_det (A : IMat) : (realMat A).det = (A.det : ℝ) := by
  have h := RingHom.map_det (Int.castRingHom ℝ) A
  rw [show ((Int.castRingHom ℝ).mapMatrix A) = realMat A from rfl] at h
  exact h.symm

lemma realMat_mulVec_intVec (A : IMat) (n : Fin 3 → ℤ) :
    realMat A *ᵥ intVec n = intVec (A *ᵥ n) := by
  ext i
  simp only [realMat, intVec, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl

/-- Conjugate of an integer matrix by a real matrix. -/
noncomputable def oConj (M : RMat) (A : IMat) : RMat := M * realMat A * M⁻¹

lemma oConj_one (M : RMat) (hM : M * M⁻¹ = 1) : oConj M 1 = 1 := by
  simp [oConj, hM]

@[simp] lemma intVec_add_rz (n m : Fin 3 → ℤ) : intVec (n + m) = intVec n + intVec m := by
  funext i; simp [intVec]

@[simp] lemma intVec_neg_rz (n : Fin 3 → ℤ) : intVec (-n) = -intVec n := by
  funext i; simp [intVec]

@[simp] private lemma intVec_zero : intVec (0 : Fin 3 → ℤ) = 0 := by
  funext i; simp [intVec]

private lemma intVec_sub (n m : Fin 3 → ℤ) : intVec (n - m) = intVec n - intVec m := by
  funext i; simp [intVec]

/-! ### Orthogonal matrices give linear isometries of `E 3` -/

lemma inner_toEuclideanLin (O : RMat) (hO : Oᵀ * O = 1) (x y : E 3) :
    inner ℝ (Matrix.toEuclideanLin O x) (Matrix.toEuclideanLin O y) = inner ℝ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  simp only [star_trivial]
  rw [dotProduct_comm, ← dotProduct_transpose_mulVec O y.ofLp (O *ᵥ x.ofLp),
    mulVec_mulVec x.ofLp Oᵀ O, hO, Matrix.one_mulVec]

lemma toEuclideanLin_injective_of_orthogonal {O : RMat} (hO : Oᵀ * O = 1) :
    Function.Injective (Matrix.toEuclideanLin O) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h2 : O *ᵥ x.ofLp = 0 := by
    have h := congrArg WithLp.ofLp hx
    simpa [Matrix.toLpLin_apply] using h
  have h3 : x.ofLp = 0 := by
    calc x.ofLp = (Oᵀ * O) *ᵥ x.ofLp := by rw [hO, Matrix.one_mulVec]
      _ = Oᵀ *ᵥ (O *ᵥ x.ofLp) := by rw [mulVec_mulVec]
      _ = 0 := by rw [h2, Matrix.mulVec_zero]
  simpa using h3

/-- The linear isometry of `E 3` given by an orthogonal matrix. -/
noncomputable def orthLinIso (O : RMat) (hO : Oᵀ * O = 1) : E 3 ≃ₗᵢ[ℝ] E 3 :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofBijective (Matrix.toEuclideanLin O)
      ⟨toEuclideanLin_injective_of_orthogonal hO,
        LinearMap.injective_iff_surjective.mp (toEuclideanLin_injective_of_orthogonal hO)⟩)
    (inner_toEuclideanLin O hO)

lemma orthLinIso_apply (O : RMat) (hO : Oᵀ * O = 1) (x : E 3) :
    orthLinIso O hO x = WithLp.toLp 2 (O *ᵥ x.ofLp) := rfl

/-- The Euclidean motion `x ↦ O x + v`. -/
noncomputable def euclidIsom (O : RMat) (hO : Oᵀ * O = 1) (v : E 3) : EuclideanIsom 3 :=
  (AffineIsometryEquiv.constVAdd ℝ (E 3) v) * (orthLinIso O hO).toAffineIsometryEquiv

lemma euclidIsom_apply (O : RMat) (hO : Oᵀ * O = 1) (v : E 3) (x : E 3) :
    euclidIsom O hO v x = WithLp.toLp 2 (O *ᵥ x.ofLp) + v := by
  rw [euclidIsom, AffineIsometryEquiv.coe_mul, Function.comp_apply,
    AffineIsometryEquiv.coe_constVAdd, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
    orthLinIso_apply]
  simp [vadd_eq_add, add_comm]

/-- The Euclidean motion `x ↦ M A M⁻¹ x + M w` attached to `A : IMat` and `w : Fin 3 → ℝ`. -/
noncomputable def gOf (M : RMat) (A : IMat) (hO : (oConj M A)ᵀ * (oConj M A) = 1)
    (w : Fin 3 → ℝ) : EuclideanIsom 3 :=
  euclidIsom (oConj M A) hO (WithLp.toLp 2 (M *ᵥ w))

lemma gOf_apply (M : RMat) (A : IMat) (hO : (oConj M A)ᵀ * (oConj M A) = 1)
    (w : Fin 3 → ℝ) (x : E 3) :
    gOf M A hO w x = WithLp.toLp 2 ((oConj M A) *ᵥ x.ofLp) + WithLp.toLp 2 (M *ᵥ w) := by
  rw [gOf, euclidIsom_apply]

/-! ### The index function `(A, n) ↦ (x ↦ M A M⁻¹ x + M (τ A + n))` -/

/-- Junk-valued (off `P`) index function for the elements of the realising group. -/
noncomputable def idxFun (M : RMat) (P : Set IMat) (τ : IMat → Fin 3 → ℝ)
    (horth : ∀ A ∈ P, (oConj M A)ᵀ * (oConj M A) = 1) (i : IMat × (Fin 3 → ℤ)) :
    EuclideanIsom 3 := by
  classical
  exact if h : i.1 ∈ P then gOf M i.1 (horth i.1 h) (τ i.1 + intVec i.2) else 1

lemma idxFun_apply (M : RMat) (P : Set IMat) (τ : IMat → Fin 3 → ℝ)
    (horth : ∀ A ∈ P, (oConj M A)ᵀ * (oConj M A) = 1) {A : IMat} (hA : A ∈ P)
    (n : Fin 3 → ℤ) (x : E 3) :
    idxFun M P τ horth (A, n) x
      = WithLp.toLp 2 ((oConj M A) *ᵥ x.ofLp) + WithLp.toLp 2 (M *ᵥ (τ A + intVec n)) := by
  rw [idxFun, dite_eq_left hA, gOf_apply]

lemma idxFun_of_notMem (M : RMat) (P : Set IMat) (τ : IMat → Fin 3 → ℝ)
    (horth : ∀ A ∈ P, (oConj M A)ᵀ * (oConj M A) = 1) {A : IMat} (hA : A ∉ P)
    (n : Fin 3 → ℤ) : idxFun M P τ horth (A, n) = 1 := by
  rw [idxFun, dite_eq_right hA]

lemma idxFun_eq_gOf (M : RMat) (P : Set IMat) (τ : IMat → Fin 3 → ℝ)
    (horth : ∀ A ∈ P, (oConj M A)ᵀ * (oConj M A) = 1) {A : IMat} (hA : A ∈ P)
    (n : Fin 3 → ℤ) :
    idxFun M P τ horth (A, n) = gOf M A (horth A hA) (τ A + intVec n) := by
  rw [idxFun, dite_eq_left hA]

/-! ### The linear map `x ↦ M x` and the affine map `x ↦ M⁻¹ x` -/

lemma toEuclideanLin_injective_of_det_ne_zero {M : RMat} (hM : M.det ≠ 0) :
    Function.Injective (Matrix.toEuclideanLin M) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h2 : M *ᵥ x.ofLp = 0 := by
    have h := congrArg WithLp.ofLp hx
    simpa [Matrix.toLpLin_apply] using h
  have h3 : x.ofLp = 0 := by
    calc x.ofLp = (M⁻¹ * M) *ᵥ x.ofLp := by rw [Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec]
      _ = M⁻¹ *ᵥ (M *ᵥ x.ofLp) := by rw [mulVec_mulVec]
      _ = 0 := by rw [h2, Matrix.mulVec_zero]
  simpa using h3

lemma toEuclideanLin_bijective_of_det_ne_zero {M : RMat} (hM : M.det ≠ 0) :
    Function.Bijective (Matrix.toEuclideanLin M) :=
  ⟨toEuclideanLin_injective_of_det_ne_zero hM,
    LinearMap.injective_iff_surjective.mp (toEuclideanLin_injective_of_det_ne_zero hM)⟩

/-- The affine map `x ↦ M⁻¹ x`. -/
noncomputable def affInvLin (M : RMat) (hM : M.det ≠ 0) : AffineGroup 3 :=
  (LinearEquiv.toAffineEquiv
    (LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
      (toEuclideanLin_bijective_of_det_ne_zero hM)))⁻¹

lemma affInvLin_apply (M : RMat) (hM : M.det ≠ 0) (y : E 3) :
    affInvLin M hM y = WithLp.toLp 2 (M⁻¹ *ᵥ y.ofLp) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMr : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have key : (LinearEquiv.toAffineEquiv
      (LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
        (toEuclideanLin_bijective_of_det_ne_zero hM)))
      (WithLp.toLp 2 (M⁻¹ *ᵥ y.ofLp)) = y := by
    rw [LinearEquiv.coe_toAffineEquiv]
    show WithLp.toLp 2 (M *ᵥ (M⁻¹ *ᵥ y.ofLp)) = y
    rw [mulVec_mulVec, hMr, Matrix.one_mulVec, WithLp.toLp_ofLp]
  rw [affInvLin, AffineEquiv.inv_def]
  rw [show (LinearEquiv.toAffineEquiv (LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
        (toEuclideanLin_bijective_of_det_ne_zero hM))).symm y
      = WithLp.toLp 2 (M⁻¹ *ᵥ y.ofLp) ↔ y = (LinearEquiv.toAffineEquiv
        (LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
          (toEuclideanLin_bijective_of_det_ne_zero hM)))
        (WithLp.toLp 2 (M⁻¹ *ᵥ y.ofLp)) from AffineEquiv.symm_apply_eq _]
  exact key.symm

lemma affInvLin_symm_apply (M : RMat) (hM : M.det ≠ 0) (x : E 3) :
    (affInvLin M hM)⁻¹ x = WithLp.toLp 2 (M *ᵥ x.ofLp) := by
  rw [AffineEquiv.inv_def]
  rw [show (affInvLin M hM).symm x = WithLp.toLp 2 (M *ᵥ x.ofLp)
      ↔ x = (affInvLin M hM) (WithLp.toLp 2 (M *ᵥ x.ofLp)) from
    AffineEquiv.symm_apply_eq (e := affInvLin M hM)]
  rw [affInvLin_apply]
  show x = WithLp.toLp 2 (M⁻¹ *ᵥ (M *ᵥ x.ofLp))
  rw [mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
    Matrix.one_mulVec, WithLp.toLp_ofLp]

lemma affInvLin_linear (M : RMat) (hM : M.det ≠ 0) :
    (affInvLin M hM).linear
      = (LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
          (toEuclideanLin_bijective_of_det_ne_zero hM))⁻¹ := by
  rw [affInvLin, AffineEquiv.inv_def, AffineEquiv.linear_symm]
  rfl

lemma affInvLin_det (M : RMat) (hM : M.det ≠ 0) :
    ((affInvLin M hM).linear.det : ℝ) = (M.det)⁻¹ := by
  rw [affInvLin_linear, map_inv, Units.val_inv_eq_inv_val, LinearEquiv.coe_det]
  rw [show ((LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
      (toEuclideanLin_bijective_of_det_ne_zero hM)) : E 3 →ₗ[ℝ] E 3)
      = Matrix.toEuclideanLin M from rfl]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

end Work.SG
