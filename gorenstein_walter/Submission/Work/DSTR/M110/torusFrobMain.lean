import Submission.Work.DSTR.M110.torusFrobDefs

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial Matrix

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
  (c : GaloisField p k) (hc : ¬ IsSquare c)

lemma delta_mul_companionMap (hodd : Odd p) :
    deltaMat p k c * (companionMat c).map (frobEquiv p k)
      = (c ^ ((p - 1) / 2) • companionMat c) * deltaMat p k c := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [show deltaMat p k c = !![1, 0; 0, c ^ ((p-1)/2)] from rfl,
      show companionMat c = !![0, c; 1, 0] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, frobEquiv_apply, hp0]
  rw [pow_eq_half_sq_mul p k hodd c]; ring

lemma delta_conj_companion (hc0 : c ≠ 0) (hodd : Odd p) :
    deltaMat p k c * (companionMat c).map (frobEquiv p k) * (deltaMat p k c)⁻¹
      = c ^ ((p - 1) / 2) • companionMat c := by
  have hdet : (deltaMat p k c).det = c ^ ((p - 1) / 2) := by
    simp [deltaMat, Matrix.det_fin_two]
  have hdinv : deltaMat p k c * (deltaMat p k c)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc0))
  calc deltaMat p k c * (companionMat c).map (frobEquiv p k) * (deltaMat p k c)⁻¹
      = ((c ^ ((p-1)/2) • companionMat c) * deltaMat p k c) * (deltaMat p k c)⁻¹ := by
        rw [delta_mul_companionMap p k c hodd]
    _ = (c ^ ((p-1)/2) • companionMat c) * (deltaMat p k c * (deltaMat p k c)⁻¹) := by
        rw [Matrix.mul_assoc]
    _ = (c ^ ((p-1)/2) • companionMat c) * 1 := by rw [hdinv]
    _ = c ^ ((p-1)/2) • companionMat c := by rw [mul_one]

/-- entrywise application of `σ` as a ring hom on `M₂`. -/
noncomputable def matMapRingHom :
    Matrix (Fin 2) (Fin 2) (GaloisField p k) →+* Matrix (Fin 2) (Fin 2) (GaloisField p k) where
  toFun M := M.map (frobEquiv p k)
  map_one' := Matrix.map_one (frobEquiv p k) (map_zero _) (map_one _)
  map_zero' := Matrix.map_zero (frobEquiv p k) (map_zero _)
  map_mul' := fun A B => Matrix.map_mul
  map_add' := fun A B => Matrix.map_add _ (fun a b => map_add (frobEquiv p k) a b) A B

@[simp] lemma matMapRingHom_apply (M : Matrix (Fin 2) (Fin 2) (GaloisField p k)) :
    matMapRingHom p k M = M.map (frobEquiv p k) := rfl

/-- conjugation by a unit matrix, as a ring hom on `M₂`. -/
noncomputable def conjRingHom (D : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
    Matrix (Fin 2) (Fin 2) (GaloisField p k) →+* Matrix (Fin 2) (Fin 2) (GaloisField p k) where
  toFun M := (D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * M *
    ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) : Matrix (Fin 2) (Fin 2) (GaloisField p k))
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_one' := by
    rw [Matrix.mul_one, Units.mul_inv]
  map_mul' := fun A B => by
    have h2 : ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
        Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        (D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) = 1 := Units.inv_mul D
    rw [show ((D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * A *
            ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k))) *
          ((D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * B *
            ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)))
        = (D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * A *
            (((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
              (D : Matrix (Fin 2) (Fin 2) (GaloisField p k))) * B *
            ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
              Matrix (Fin 2) (Fin 2) (GaloisField p k)) by noncomm_ring]
    rw [h2, mul_one]
    noncomm_ring
  map_add' := fun A B => by rw [Matrix.mul_add, Matrix.add_mul]

end Work.DSTR.M110

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
  (c : GaloisField p k) (hc : ¬ IsSquare c)

abbrev AA : Type := AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X])

lemma root_sq : (AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X])) ^ 2 =
    AdjoinRoot.of _ c := by
  have h : (AdjoinRoot.mk (X ^ 2 - C c : (GaloisField p k)[X])) (X ^ 2 - C c) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  exact h

lemma root_pow (hodd : Odd p) :
    (AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X])) ^ p =
      AdjoinRoot.of _ (c ^ ((p - 1) / 2)) *
        AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X]) := by
  have hp : (p - 1) / 2 * 2 + 1 = p := by
    rw [half_mul_two p hodd]; exact Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have key : (AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X])) ^ ((p - 1) / 2 * 2 + 1) =
      AdjoinRoot.of _ (c ^ ((p - 1) / 2)) *
        AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X]) := by
    conv_lhs => rw [pow_succ, pow_mul']
    rw [root_sq, map_pow]
  simpa only [hp] using key

end Work.DSTR.M110

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
  (c : GaloisField p k) (hc : ¬ IsSquare c)

lemma torusAlgHomB0_of (hc0 : c ≠ 0) (a : GaloisField p k) :
    torusAlgHomB0 p k c hc (AdjoinRoot.of _ a) = a • 1 := by
  rw [torusAlgHomB0_apply, ← AdjoinRoot.algebraMap_eq, torusAlgHom_of]

lemma matMap_smul_one (a : GaloisField p k) :
    ((a • 1 : Matrix (Fin 2) (Fin 2) (GaloisField p k))).map (frobEquiv p k) =
      frobEquiv p k a • 1 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, h, hp0]

lemma conjRingHom_smul_one (D : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ)
    (a : GaloisField p k) : conjRingHom p k D (a • 1) = a • 1 := by
  rw [show conjRingHom p k D (a • 1) = (D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * (a • 1) *
      ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
        Matrix (Fin 2) (Fin 2) (GaloisField p k)) from rfl,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]

end Work.DSTR.M110

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
  (c : GaloisField p k) (hc : ¬ IsSquare c)

@[simp] lemma conjRingHom_apply (D : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField p k)) :
    conjRingHom p k D M = (D : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * M *
      ((D⁻¹ : (Matrix (Fin 2) (Fin 2) (GaloisField p k))ˣ) :
        Matrix (Fin 2) (Fin 2) (GaloisField p k)) := rfl

lemma torusAlgHomB0_root (hc0 : c ≠ 0) :
    torusAlgHomB0 p k c hc (AdjoinRoot.root (X ^ 2 - C c : (GaloisField p k)[X])) =
      companionMat c := by
  rw [torusAlgHomB0_apply, torusAlgHom_root]
  exact B0_coe c hc

lemma torusAlgHomFrob (hodd : Odd p) :
    ∀ μ : AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X]),
      deltaMat p k c * ((torusAlgHomB0 p k c hc μ).map (frobEquiv p k)) * (deltaMat p k c)⁻¹
        = torusAlgHomB0 p k c hc (μ ^ p) := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  haveI : ExpChar (AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X])) p := by
    have hmonic : (X ^ 2 - C c : (GaloisField p k)[X]).Monic :=
      monic_X_pow_sub_C c (by norm_num)
    have hdeg : 0 < (X ^ 2 - C c : (GaloisField p k)[X]).degree := by
      rw [degree_X_pow_sub_C (by norm_num : 0 < 2) c]; norm_num
    have hf : Function.Injective (algebraMap (GaloisField p k)
        (AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X]))) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.of.injective_of_monic_of_degree_pos hmonic hdeg
    exact expChar_of_injective_algebraMap hf p
  have hGH : (conjRingHom p k (deltaGL p k c hc0)).comp
        ((matMapRingHom p k).comp (torusAlgHomB0 p k c hc))
      = (torusAlgHomB0 p k c hc).comp
        (frobenius (AdjoinRoot (X ^ 2 - C c : (GaloisField p k)[X])) p) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext; intro a
      simp only [RingHom.comp_apply, matMapRingHom_apply]
      rw [torusAlgHomB0_of p k c hc hc0 a, matMap_smul_one p k a, conjRingHom_smul_one]
      rw [frobenius_def, ← map_pow, torusAlgHomB0_of p k c hc hc0 (a ^ p), frobEquiv_apply]
    · simp only [RingHom.comp_apply, matMapRingHom_apply]
      rw [torusAlgHomB0_root p k c hc hc0, conjRingHom_apply,
        Matrix.GeneralLinearGroup.coe_inv, deltaGL_coe,
        delta_conj_companion p k c hc0 hodd, frobenius_def, root_pow p k c hodd, map_mul,
        torusAlgHomB0_of p k c hc hc0 (c ^ ((p - 1) / 2)), torusAlgHomB0_root p k c hc hc0,
        Matrix.smul_mul, Matrix.one_mul]
  intro μ
  have h := congrFun (congrArg DFunLike.coe hGH) μ
  simpa [RingHom.comp_apply, conjRingHom_apply, matMapRingHom, frobenius_def, deltaGL_coe,
    Matrix.GeneralLinearGroup.coe_inv] using h

end Work.DSTR.M110
