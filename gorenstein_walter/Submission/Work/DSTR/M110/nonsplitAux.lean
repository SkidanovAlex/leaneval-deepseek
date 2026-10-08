/-
Auxiliary development for the non-split case of Bender 1.10(ii) in the `ℙ¹` model
(`Work.DSTR.M110.nonsplitCase`).
-/
import Mathlib
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.DSTR.M110.SylowGen
import Submission.Work.DSTR.M110.Aut.pglIndex
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.arithOrbitSubOne
import Submission.Work.DSTR.M110.pglInvolutionFixedPoints

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial

namespace Work.DSTR.M110

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Fixed vectors and fixed points of elements of `PGL(2,F)` -/


/-- A matrix `A` with `A * A = 1` has a non-zero fixed vector, unless `A = -1`. -/
lemma exists_mulVec_eq_self_of_mul_self_eq_one (A : Matrix (Fin 2) (Fin 2) F) (hA : A * A = 1)
    (h : A ≠ -1) : ∃ v : Fin 2 → F, v ≠ 0 ∧ A.mulVec v = v := by
  have hfac : (A - 1) * (A + 1) = 0 := by
    have h1 : (A - 1) * (A + 1) = A * A - 1 := by noncomm_ring
    rw [h1, hA, sub_self]
  have hne : A + 1 ≠ 0 := by
    intro hc
    exact h ((add_eq_zero_iff_eq_neg).mp hc)
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, (A + 1).col j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Matrix.ext fun i j => by
      have := congrFun (hc j) i
      simpa using this)
  refine ⟨(A + 1).col j, hj, ?_⟩
  have h0 : (A - 1).mulVec ((A + 1).col j) = 0 := by
    rw [← Matrix.mulVec_single_one (A + 1) j, Matrix.mulVec_mulVec, hfac, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

/-- A matrix with a non-zero fixed vector fixes a point of `ℙ¹(F)`. -/
lemma exists_fixed_point_of_mulVec_eq_self (B : GL (Fin 2) F) (v : Fin 2 → F) (hv : v ≠ 0)
    (hBv : (B : Matrix (Fin 2) (Fin 2) F).mulVec v = v) :
    ∃ p : Work.AUTL2.P1 F,
      Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) p = p := by
  refine ⟨(OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv), ?_⟩
  rw [Work.AUTL2.Galois.pglHom_mk_apply]
  refine (OnePoint.equivProjectivization F).injective ?_
  rw [OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  conv_lhs => rw [Projectivization.smul_mk]
  refine (Projectivization.mk_eq_mk_iff' F _ v _ hv).mpr ⟨1, ?_⟩
  rw [one_smul, gl_smul_eq_mulVec, hBv]

/-- If `t = pglHom (mk B)` with `B * B = c • 1` has no fixed point on `ℙ¹(F)`, then `c` is not a
square. -/
lemma not_isSquare_of_fixedPointFree (B : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)
    (hfpf : ∀ p : Work.AUTL2.P1 F,
      Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) p ≠ p) :
    ¬ IsSquare c := by
  intro hc
  obtain ⟨s, hs⟩ := hc
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    have h0 : (B : Matrix (Fin 2) (Fin 2) F) * B = 0 := by rw [hB, hs]; simp
    have hdet : (B : Matrix (Fin 2) (Fin 2) F).det * (B : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [← Matrix.det_mul, h0, Matrix.det_zero]
    exact B.det_ne_zero (mul_self_eq_zero.mp hdet)
  -- `B' = s⁻¹ • B` satisfies `B' * B' = 1`
  set B' : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (s⁻¹ • (B : Matrix (Fin 2) (Fin 2) F)) (by
        rw [Matrix.det_smul, Fintype.card_fin]
        exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hs0)) B.det_ne_zero) with hB'def
  have hB'mat : (B' : Matrix (Fin 2) (Fin 2) F) = s⁻¹ • (B : Matrix (Fin 2) (Fin 2) F) :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hBsq : (B' : Matrix (Fin 2) (Fin 2) F) * B' = 1 := by
    have hss : s⁻¹ * s⁻¹ * (s * s) = 1 := by field_simp
    rw [hB'mat, smul_mul_smul, hB, hs, smul_smul, hss, one_smul]
  have hB'ne : (B' : Matrix (Fin 2) (Fin 2) F) ≠ -1 := by
    intro hcon
    have hBs : (B : Matrix (Fin 2) (Fin 2) F) = -(s • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      have h3 : s⁻¹ • (B : Matrix (Fin 2) (Fin 2) F) = -1 := by rw [← hB'mat, hcon]
      have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => s • M) h3
      rw [smul_neg, smul_smul, mul_inv_cancel₀ hs0, one_smul] at h4
      exact h4
    have hcent : B ∈ Subgroup.center (GL (Fin 2) F) := by
      refine Subgroup.mem_center_iff.mpr fun h => ?_
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hBs, mul_neg,
        neg_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, one_mul]
    have h4 : Matrix.ProjGenLinGroup.mk B = 1 := Matrix.ProjGenLinGroup.mk_eq_one.mpr hcent
    exact hfpf (OnePoint.infty : Work.AUTL2.P1 F) (by rw [h4, map_one, Equiv.Perm.one_apply])
  obtain ⟨v, hv, hBv⟩ := exists_mulVec_eq_self_of_mul_self_eq_one _ hBsq hB'ne
  obtain ⟨p, hp⟩ := exists_fixed_point_of_mulVec_eq_self B' v hv hBv
  have hmk : Matrix.ProjGenLinGroup.mk B' = Matrix.ProjGenLinGroup.mk B := by
    rw [hB'def, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 s hs0, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun b _ hbj => by rw [if_neg hbj, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), if_pos rfl]
    rw [mul_assoc, mul_comm ((B : Matrix (Fin 2) (Fin 2) F) i j) s, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul]
  exact hfpf p (by rw [← hmk]; exact hp)

/-- The unit group of the quadratic algebra `F[X]/(X²-c)`. -/
abbrev TorUnits (F : Type*) [Field F] (c : F) : Type _ := (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ

/-! ## Extracting a matrix representative -/

section Torus

variable {F : Type*} [Field F] [DecidableEq F]

/-- `X ^ 2 - C c` is irreducible when `c` is not a square. -/
lemma irreducible_X_sq_sub_C {c : F} (hc : ¬ IsSquare c) :
    Irreducible (X ^ 2 - C c : F[X]) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_X_pow_sub_C]; norm_num
  · intro x hx
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
    exact hc ⟨x, by rw [← hx, sq]⟩

variable (B : GL (Fin 2) F) (c : F) (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)

/-- The `F`-algebra map `F[X]/(X²-c) →+* M₂(F)`, `X ↦ B`. -/
noncomputable def torusAlgHom : AdjoinRoot (X ^ 2 - C c : F[X]) →+* Matrix (Fin 2) (Fin 2) F :=
  Ideal.Quotient.lift (Ideal.span {(X ^ 2 - C c : F[X])})
    ((Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F) :
      F[X] →ₐ[F] Matrix (Fin 2) (Fin 2) F)).toRingHom
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨y, rfl⟩ := ha
      rw [map_mul, show ((Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F) :
              F[X] →ₐ[F] Matrix (Fin 2) (Fin 2) F)).toRingHom (X ^ 2 - C c : F[X]) = 0 from by
          change (Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F)) (X ^ 2 - C c : F[X]) = 0
          simp only [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, pow_two, hB,
            Algebra.algebraMap_eq_smul_one, sub_self],
        zero_mul])

@[simp] lemma torusAlgHom_root :
    torusAlgHom B c hB (AdjoinRoot.root (X ^ 2 - C c : F[X])) = (B : Matrix (Fin 2) (Fin 2) F) := by
  rw [AdjoinRoot.root]
  change (Ideal.Quotient.lift (Ideal.span {(X ^ 2 - C c : F[X])})
      ((Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F) :
        F[X] →ₐ[F] Matrix (Fin 2) (Fin 2) F)).toRingHom _)
    (Ideal.Quotient.mk _ (X : F[X])) = (B : Matrix (Fin 2) (Fin 2) F)
  rw [Ideal.Quotient.lift_mk]
  change (Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F) : F[X] →ₐ[F] Matrix (Fin 2) (Fin 2) F)
    (X : F[X]) = (B : Matrix (Fin 2) (Fin 2) F)
  rw [Polynomial.aeval_X]

@[simp] lemma torusAlgHom_of (a : F) :
    torusAlgHom B c hB (algebraMap F (AdjoinRoot (X ^ 2 - C c : F[X])) a) = a • 1 := by
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk]
  change (Ideal.Quotient.lift (Ideal.span {(X ^ 2 - C c : F[X])})
      ((Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F) :
        F[X] →ₐ[F] Matrix (Fin 2) (Fin 2) F)).toRingHom _)
    (Ideal.Quotient.mk _ (C a)) = a • 1
  rw [Ideal.Quotient.lift_mk]
  change (Polynomial.aeval (B : Matrix (Fin 2) (Fin 2) F) : F[X] →ₐ[F] Matrix (Fin 2) (Fin 2) F)
    (C a) = a • 1
  rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

lemma torusAlgHom_injective (hc : ¬ IsSquare c) : Function.Injective (torusAlgHom B c hB) := by
  haveI : Fact (Irreducible (X ^ 2 - C c : F[X])) := ⟨irreducible_X_sq_sub_C hc⟩
  intro x y hxy
  by_contra hne
  have h0 : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hne h)
  have hunit : IsUnit (x - y) := ⟨Units.mk0 (x - y) h0, rfl⟩
  have hmap : IsUnit (torusAlgHom B c hB (x - y)) := hunit.map (torusAlgHom B c hB)
  rw [map_sub, hxy, sub_self] at hmap
  exact not_isUnit_zero hmap

/-- The torus, as a monoid of units. -/
noncomputable def torusGL : (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ →* GL (Fin 2) F :=
  Units.map (torusAlgHom B c hB).toMonoidHom

/-- The non-split torus as a subgroup of `Sym(ℙ¹(F))`. -/
noncomputable def torusPerm : (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ →* Equiv.Perm (Work.AUTL2.P1 F) :=
  (Work.AUTL2.pglHom F).comp (Matrix.ProjGenLinGroup.mk.comp (torusGL B c hB))

/-- The non-split torus `T ≤ pglImage F`. -/
noncomputable def theTorus : Subgroup (Equiv.Perm (Work.AUTL2.P1 F)) := (torusPerm B c hB).range

@[simp] lemma torusPerm_apply (u : (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ) :
    torusPerm B c hB u = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk (torusGL B c hB u)) := rfl

lemma theTorus_le_pglImage : theTorus B c hB ≤ Work.AUTL2.pglImage F := by
  rintro x ⟨u, rfl⟩
  exact ⟨_, rfl⟩

/-- The odd part of the non-split torus: generated by the `2 ^ v_2(q+1)`-th power of the image of
a generator of `F[B]^×`. -/
noncomputable def theTorusOdd (v : ℕ) (ζ : (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ) :
    Subgroup (Equiv.Perm (Work.AUTL2.P1 F)) :=
  Subgroup.zpowers (torusPerm B c hB (ζ ^ (2 ^ v)))

lemma theTorusOdd_le_theTorus (v : ℕ) (ζ : (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ) :
    theTorusOdd B c hB v ζ ≤ theTorus B c hB := by
  rintro x hx
  rw [theTorusOdd, Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  exact ⟨(ζ ^ 2 ^ v) ^ n, by rw [map_zpow]⟩

end Torus

/-- Every involution of order two in `pglImage F` is the image of a matrix `B` with
`B * B = c • 1`, which is moreover not a scalar matrix. -/
theorem exists_mat_of_mem_pglImage {F : Type*} [Field F] [DecidableEq F]
    (t : Equiv.Perm (Work.AUTL2.P1 F)) (ht : t ∈ Work.AUTL2.pglImage F) (ht2 : orderOf t = 2) :
    ∃ (B : GL (Fin 2) F) (c : F),
      t = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) ∧
        (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1 ∧
        (∀ s : F, (B : Matrix (Fin 2) (Fin 2) F) ≠ s • 1) := by
  obtain ⟨g, rfl⟩ := ht
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have ht2' : (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B))
    rwa [ht2] at h
  have hg2 : Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk B = 1 := by
    refine Work.AUTL2.Aut.pglHomInjective F ?_
    rw [map_mul, map_one, ← pow_two, ht2']
  have hB2 : B * B ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    exact hg2
  obtain ⟨u, hu⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hB2
  refine ⟨B, (u : F), rfl, ?_, ?_⟩
  · rw [← Matrix.GeneralLinearGroup.coe_mul, ← hu, Matrix.scalar_apply]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.smul_apply, h]
  · intro s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hs
      exact B.ne_zero hs
    have hBmem : B ∈ Subgroup.center (GL (Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨Units.mk0 s hs0, ?_⟩
      rw [hs, Matrix.scalar_apply]
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.smul_apply, h]
    have h1 : Matrix.ProjGenLinGroup.mk B = 1 := Matrix.ProjGenLinGroup.mk_eq_one.mpr hBmem
    rw [h1, map_one, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)

/-- An element of `pglImage F` of odd order lies in `pslImage F` (copy of
`Work.DSTR.M110.oddPglImageMemPslImage`, kept here to avoid an import cycle). -/
theorem oddPglImageMemPslImage' (p k : ℕ) [Fact p.Prime] [DecidableEq (GaloisField p k)]
    (x : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (hx : x ∈ Work.AUTL2.pglImage (GaloisField p k)) (hodd : Odd (orderOf x)) :
    x ∈ Work.AUTL2.pslImage (GaloisField p k) := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  set y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
    Work.AUTL2.pglHom _ (Matrix.ProjGenLinGroup.mk B) with hydef
  have hsq : y * y ∈ Work.AUTL2.pslImage (GaloisField p k) := by
    have hyy : y * y = Work.AUTL2.pglHom _ (Matrix.ProjGenLinGroup.mk (B * B)) := by
      rw [hydef, ← map_mul, ← map_mul]
    rw [hyy, Work.AUTL2.Aut.mem_pslImage_iff_isSquare_det]
    exact ⟨B.det, by rw [map_mul]⟩
  have hm : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  obtain ⟨t, ht⟩ := hodd
  have h2 : 2 * ((orderOf y + 1) / 2) = orderOf y + 1 := by omega
  have hsplit : y = (y * y) ^ ((orderOf y + 1) / 2) := by
    calc y = y ^ (orderOf y + 1) := by rw [pow_succ, hm, one_mul]
      _ = y ^ (2 * ((orderOf y + 1) / 2)) := by rw [h2]
      _ = (y * y) ^ ((orderOf y + 1) / 2) := by rw [pow_mul, pow_two]
  rw [hsplit]
  exact Subgroup.pow_mem _ hsq _

end Work.DSTR.M110
