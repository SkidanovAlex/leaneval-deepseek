import Mathlib
import Submission.Work.SG.Defs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# exists_conj_of_intEquiv — integral equivalence ⇒ affine conjugacy (medium, ~300–600 lines)

**Claim.** Given `U` unimodular, `s`, and `IntEquiv P τ P' τ' U s`, the affine map
`φ x = U x + s` satisfies `det φ.linear = det U` and `φ (sgSet P τ) φ⁻¹ = sgSet P' τ'`.

**Sketch.** Build `φ` from `Matrix.toLin'` of `U.map Int.cast` (a `LinearEquiv` since the det is
a unit) plus `AffineEquiv.constVAdd`. `det` via `LinearMap.det_toLin'` and `RingHom.map_det`.
The same unfolding as in `conj_sgSet_integral` computes `φ (A, τ A + n) φ⁻¹`. `⊆` uses the
second `IntEquiv` clause. `⊇` uses the first clause to write `A' = U B U⁻¹`, then the second
clause, with `U` bijective on `ℤ³` to produce the integer shift.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

namespace ConjOfIntEquiv

/-! ## Elementary matrix and vector facts -/

/-- Casting an integer matrix product. -/
lemma castMat_mul (A B : IMat) :
    (A * B).map (Int.cast : ℤ → ℝ) = (A.map (Int.cast : ℤ → ℝ)) * (B.map (Int.cast : ℤ → ℝ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  push_cast
  rfl

/-- The identity matrix casts to the identity. -/
lemma castMat_one : ((1 : IMat).map (Int.cast : ℤ → ℝ)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- The determinant of a cast matrix is the cast determinant. -/
lemma castMat_det (A : IMat) : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := by
  simpa [RingHom.mapMatrix_apply] using (RingHom.map_det (Int.castRingHom ℝ) A).symm

lemma intVec_add (a b : Fin 3 → ℤ) : intVec (a + b) = intVec a + intVec b := by
  ext i; simp [intVec]

lemma intVec_sub (a b : Fin 3 → ℤ) : intVec (a - b) = intVec a - intVec b := by
  ext i; simp [intVec]

lemma intVec_neg (a : Fin 3 → ℤ) : intVec (-a) = -intVec a := by
  ext i; simp [intVec]

/-- The cast matrix acts on cast integer vectors as the integer matrix does. -/
lemma intVec_mulVec (U : IMat) (n : Fin 3 → ℤ) :
    (U.map (Int.cast : ℤ → ℝ)).mulVec (intVec n) = intVec (U.mulVec n) := by
  funext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) U n i).symm

/-- The computation of a conjugate `x ↦ U (A (U⁻¹ (x - s))) + s` in coordinates. This is the
coordinate form of "the conjugate of the element `A x + τ A + n` of `sgSet P τ`". -/
lemma castMat_conj_mulVec (U V A : IMat) (τ s x : Fin 3 → ℝ) (n : Fin 3 → ℤ) :
    (U.map (Int.cast : ℤ → ℝ)).mulVec
        ((A.map (Int.cast : ℤ → ℝ)).mulVec
            ((V.map (Int.cast : ℤ → ℝ)).mulVec (x - s)) + τ + intVec n) + s
      = ((U * A * V).map (Int.cast : ℤ → ℝ)).mulVec x
        + ((U.map (Int.cast : ℤ → ℝ)).mulVec τ + s
            - ((U * A * V).map (Int.cast : ℤ → ℝ)).mulVec s)
        + intVec (U.mulVec n) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  rw [← castMat_mul, ← castMat_mul, ← Matrix.mul_assoc, ← intVec_mulVec]
  abel

/-! ## The affine map `x ↦ M x + a` of `ℝ³` -/

lemma mulVecLin_eq_toLin' (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.mulVecLin M = Matrix.toLin' M :=
  LinearMap.ext fun v => by rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply]

/-- The linear equivalence `x ↦ M x` of the coordinate space, for `M` with a two-sided inverse
`W`. -/
noncomputable def coordLinEquiv (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1)
    (hWM : W * M = 1) : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toLinearMap := Matrix.mulVecLin M
  invFun := W.mulVec
  left_inv := by
    intro x
    change W.mulVec (M.mulVec x) = x
    rw [Matrix.mulVec_mulVec, hWM, Matrix.one_mulVec]
  right_inv := by
    intro x
    change M.mulVec (W.mulVec x) = x
    rw [Matrix.mulVec_mulVec, hMW, Matrix.one_mulVec]

@[simp]
lemma coordLinEquiv_apply (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1)
    (v : Fin 3 → ℝ) : coordLinEquiv M W hMW hWM v = M.mulVec v := rfl

lemma det_coordLinEquiv (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1) :
    ((LinearEquiv.det (coordLinEquiv M W hMW hWM) : ℝˣ) : ℝ) = M.det := by
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.mulVecLin M) = M.det
  rw [mulVecLin_eq_toLin', LinearMap.det_toLin']

/-- Passing a linear equivalence of the coordinate space to `E 3 = ℝ³` does not change its
determinant. -/
lemma det_withLpCongr (B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
    ((LinearEquiv.det (LinearEquiv.withLpCongr 2 B) : ℝˣ) : ℝ) = (LinearEquiv.det B : ℝ) := by
  have h : LinearEquiv.det (LinearEquiv.withLpCongr 2 B) = LinearEquiv.det B := by
    rw [show LinearEquiv.withLpCongr 2 B =
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.symm ≪≫ₗ B ≪≫ₗ
          (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm from rfl,
      LinearEquiv.det_conj]
  rw [h]

/-- The affine map `x ↦ M x + a` of `ℝ³`, as an element of `Aff(ℝ³)`. -/
noncomputable def affOfMat (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1)
    (a : Fin 3 → ℝ) : AffineGroup 3 :=
  AffineEquiv.mk' (fun x : E 3 => WithLp.toLp 2 (M.mulVec x.ofLp + a))
    (LinearEquiv.withLpCongr 2 (coordLinEquiv M W hMW hWM)) 0
    (fun _ => by
      rw [vsub_eq_sub, sub_zero, LinearEquiv.coe_withLpCongr, WithLp.map, coordLinEquiv_apply,
        vadd_eq_add, WithLp.ofLp_zero, Matrix.mulVec_zero, zero_add, ← WithLp.toLp_add])

@[simp]
lemma affOfMat_apply (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1)
    (a : Fin 3 → ℝ) (x : E 3) :
    affOfMat M W hMW hWM a x = WithLp.toLp 2 (M.mulVec x.ofLp + a) := rfl

@[simp]
lemma affOfMat_linear (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1)
    (a : Fin 3 → ℝ) :
    (affOfMat M W hMW hWM a).linear = LinearEquiv.withLpCongr 2 (coordLinEquiv M W hMW hWM) :=
  rfl

lemma affOfMat_det (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1)
    (a : Fin 3 → ℝ) : ((affOfMat M W hMW hWM a).linear.det : ℝ) = M.det := by
  rw [affOfMat_linear, det_withLpCongr, det_coordLinEquiv]

/-- The inverse of `x ↦ M x + a` is `y ↦ W (y - a)`. -/
lemma affOfMat_symm_apply (M W : Matrix (Fin 3) (Fin 3) ℝ) (hMW : M * W = 1) (hWM : W * M = 1)
    (a : Fin 3 → ℝ) (y : E 3) :
    (affOfMat M W hMW hWM a).symm y = WithLp.toLp 2 (W.mulVec (y.ofLp - a)) := by
  rw [AffineEquiv.symm_apply_eq]
  rw [affOfMat_apply, Matrix.mulVec_mulVec, hMW, Matrix.one_mulVec, sub_add_cancel,
    WithLp.toLp_ofLp]

end ConjOfIntEquiv

open ConjOfIntEquiv

/-! ## The main theorem -/

/-- Converse of `conj_sgSet_integral`: an integral equivalence of data is realised by an affine
conjugacy `x ↦ U x + s` of the same determinant. -/
theorem exists_conj_of_intEquiv {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ}
    (hP : IsIntPointGroup P) (hτ : IsIntCocycle P τ) {U : IMat} (hU : IsUnit U.det)
    {s : Fin 3 → ℝ} (h : IntEquiv P τ P' τ' U s) :
    ∃ φ : AffineGroup 3, (φ.linear.det : ℝ) = (U.det : ℝ) ∧
      conjSet φ (sgSet P τ) = sgSet P' τ' := by
  classical
  obtain ⟨hPmem, hPcoc⟩ := h
  have hunit : ∀ A ∈ P, IsUnit A.det := hP.2.2.2
  have hUmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hU
  have hVmul : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hU
  have hMW : (U.map (Int.cast : ℤ → ℝ)) * ((U⁻¹).map (Int.cast : ℤ → ℝ)) = 1 := by
    rw [← castMat_mul, hUmul, castMat_one]
  have hWM : ((U⁻¹).map (Int.cast : ℤ → ℝ)) * (U.map (Int.cast : ℤ → ℝ)) = 1 := by
    rw [← castMat_mul, hVmul, castMat_one]
  set φ : AffineGroup 3 :=
    affOfMat (U.map (Int.cast : ℤ → ℝ)) ((U⁻¹).map (Int.cast : ℤ → ℝ)) hMW hWM s with hφdef
  have hφapply : ∀ x : E 3, φ x = WithLp.toLp 2 ((U.map (Int.cast : ℤ → ℝ)).mulVec x.ofLp + s) := by
    intro x
    rw [hφdef, affOfMat_apply]
  have hφsymm : ∀ y : E 3,
      φ⁻¹ y = WithLp.toLp 2 (((U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec (y.ofLp - s)) := by
    intro y
    rw [show φ⁻¹ = φ.symm from rfl, hφdef, affOfMat_symm_apply]
  have hφdet : (φ.linear.det : ℝ) = (U.det : ℝ) := by
    rw [hφdef, affOfMat_det, castMat_det]
  refine ⟨φ, hφdet, ?_⟩
  apply Set.Subset.antisymm
  · rintro h' ⟨g, hg, rfl⟩
    obtain ⟨A, hA, n, hgA⟩ := hg
    obtain ⟨n₂, hn₂⟩ := hPcoc A hA
    refine ⟨U * A * U⁻¹, (hPmem (U * A * U⁻¹)).mpr ⟨A, hA, rfl⟩, U.mulVec n - n₂, ?_⟩
    intro x
    have hstep : (φ * g * φ⁻¹) x = WithLp.toLp 2 ((U.map (Int.cast : ℤ → ℝ)).mulVec
        ((A.map (Int.cast : ℤ → ℝ)).mulVec
            (((U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec (x.ofLp - s)) + τ A + intVec n) + s) := by
      rw [AffineEquiv.mul_def, AffineEquiv.mul_def, AffineEquiv.trans_apply,
        AffineEquiv.trans_apply, hφsymm x,
        hgA (WithLp.toLp 2 (((U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec (x.ofLp - s))), hφapply]
    rw [hstep, castMat_conj_mulVec U U⁻¹ A (τ A) s x.ofLp n]
    have hmiddle : (U.map (Int.cast : ℤ → ℝ)).mulVec (τ A) + s
        - ((U * A * U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec s
        = τ' (U * A * U⁻¹) - intVec n₂ := by
      rw [hn₂]; abel
    rw [hmiddle, intVec_sub]
    congr 1
    abel
  · rintro h' ⟨A₂, hA₂, n', hh'⟩
    obtain ⟨B, hB, hBA⟩ := (hPmem A₂).mp hA₂
    obtain ⟨n₂, hn₂⟩ := hPcoc B hB
    have hB1 : (B.map (Int.cast : ℤ → ℝ)) * ((B⁻¹).map (Int.cast : ℤ → ℝ)) = 1 := by
      rw [← castMat_mul, Matrix.mul_nonsing_inv B (hunit B hB), castMat_one]
    have hB2 : ((B⁻¹).map (Int.cast : ℤ → ℝ)) * (B.map (Int.cast : ℤ → ℝ)) = 1 := by
      rw [← castMat_mul, Matrix.nonsing_inv_mul B (hunit B hB), castMat_one]
    set g : AffineGroup 3 := affOfMat (B.map (Int.cast : ℤ → ℝ)) ((B⁻¹).map (Int.cast : ℤ → ℝ))
      hB1 hB2 (τ B + intVec ((U⁻¹).mulVec (n₂ + n'))) with hgdef
    have hg_apply : ∀ y : E 3, g y = WithLp.toLp 2 ((B.map (Int.cast : ℤ → ℝ)).mulVec y.ofLp
        + τ B + intVec ((U⁻¹).mulVec (n₂ + n'))) := by
      intro y
      rw [hgdef, affOfMat_apply]
      congr 1
      abel
    refine ⟨g, ⟨B, hB, (U⁻¹).mulVec (n₂ + n'), hg_apply⟩, ?_⟩
    apply AffineEquiv.ext
    intro x
    have hstep : (φ * g * φ⁻¹) x = WithLp.toLp 2 ((U.map (Int.cast : ℤ → ℝ)).mulVec
        ((B.map (Int.cast : ℤ → ℝ)).mulVec
            (((U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec (x.ofLp - s)) + τ B
          + intVec ((U⁻¹).mulVec (n₂ + n'))) + s) := by
      rw [AffineEquiv.mul_def, AffineEquiv.mul_def, AffineEquiv.trans_apply,
        AffineEquiv.trans_apply, hφsymm x,
        hg_apply (WithLp.toLp 2 (((U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec (x.ofLp - s))), hφapply]
    rw [hstep, castMat_conj_mulVec U U⁻¹ B (τ B) s x.ofLp ((U⁻¹).mulVec (n₂ + n'))]
    have hm : U.mulVec ((U⁻¹).mulVec (n₂ + n')) = n₂ + n' := by
      rw [Matrix.mulVec_mulVec, hUmul, Matrix.one_mulVec]
    have hmiddle : (U.map (Int.cast : ℤ → ℝ)).mulVec (τ B) + s
        - ((U * B * U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec s
        = τ' (U * B * U⁻¹) - intVec n₂ := by
      rw [hn₂]; abel
    rw [hm, hmiddle, intVec_add, ← hBA]
    rw [hh' x]
    congr 1
    abel

end Work.SG
