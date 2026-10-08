import Mathlib

/-!
# `lamFixedOfSemilinear`

Let `F` be a field, `σ : F ≃+* F` an involution (`σ (σ x) = x`), `A ∈ GL(2,F)` and `lam ∈ F`
with `A * σ(A) = lam • 1`, where `σ(A)` is the entrywise image of `A` under `σ`.  Then the
"norm factor" `lam` is fixed by `σ` and non-zero:

`σ lam = lam` and `lam ≠ 0`.

This is the elementary bootstrap for the study of semilinear maps of `ℙ¹(F)`: it says that an
element `A·σ(–)` of `PΓL(2,F)` which acts through a scalar matrix (i.e. lies in `PGL(2,F)` in
the involution case) has a fixed "norm factor".

The proof is elementary.  Applying `σ` entrywise to `A·σ(A) = lam • 1` and using `σ² = id`
gives `σ(A)·A = σ lam • 1`.  Hence, computing the triple product `A·σ(A)·A` in two ways,

  `lam • A = (A·σ(A))·A = A·(σ(A)·A) = σ lam • A`,

and cancelling `A` on the right (`A` is invertible) yields `lam = σ lam`.  Taking determinants
in `A·σ(A) = lam • 1` gives `det A · σ(det A) = lam²`; since `det A ≠ 0` and `σ(det A) ≠ 0`,
we get `lam ≠ 0`.
-/

namespace Work.DSTR.M110

theorem lamFixedOfSemilinear (F : Type*) [Field F] (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x)
    (A : GL (Fin 2) F) (lam : F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.GeneralLinearGroup.map (σ : F →+* F) A = lam • 1) :
    σ lam = lam ∧ lam ≠ 0 := by
  -- `Mm` is the entrywise image of `A` under `σ`.
  have hMm : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = ((A : Matrix (Fin 2) (Fin 2) F)).map (σ : F →+* F) := rfl
  -- `σ² = id` on matrices.
  have hmapmap : (((Matrix.GeneralLinearGroup.map (σ : F →+* F) A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).map (σ : F →+* F) = (A : Matrix (Fin 2) (Fin 2) F) := by
    rw [hMm, Matrix.map_map]
    ext i j
    simp [Function.comp_apply, hσ2]
  -- `σ` acts on the scalar matrix `lam • 1` by replacing `lam` with `σ lam`.
  have hRHS : (lam • 1 : Matrix (Fin 2) (Fin 2) F).map (σ : F →+* F) = σ lam • 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp [smul_eq_mul]
    · simp [h]
  -- Applying `σ` to `hA` gives `σ(A) * A = σ lam • 1`.
  have hMA : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) A : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F)) = σ lam • 1 := by
    have hmap := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M.map (σ : F →+* F)) hA
    rw [Matrix.map_mul, ← hMm, hmapmap, hRHS] at hmap
    exact hmap
  -- Compare `A * σ(A) * A` computed associatively in the two ways.
  have hkey : lam • (A : Matrix (Fin 2) (Fin 2) F) = σ lam • (A : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : ((A : Matrix (Fin 2) (Fin 2) F) *
          (Matrix.GeneralLinearGroup.map (σ : F →+* F) A : Matrix (Fin 2) (Fin 2) F)) *
        (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          ((Matrix.GeneralLinearGroup.map (σ : F →+* F) A : Matrix (Fin 2) (Fin 2) F) *
        (A : Matrix (Fin 2) (Fin 2) F)) := mul_assoc _ _ _
    rw [hA, hMA, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one] at h1
    exact h1
  -- `A` is invertible.
  have hAi : (A : Matrix (Fin 2) (Fin 2) F) *
      ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hlam_eq : lam = σ lam := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F =>
      M * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hkey
    rw [Matrix.smul_mul, Matrix.smul_mul, hAi] at h
    have h2 := congrFun (congrFun h 0) 0
    simpa using h2
  -- Determinants: `det A * σ (det A) = lam ^ 2`.
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul] at hdet
  have hdetM : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = σ ((A : Matrix (Fin 2) (Fin 2) F).det) := by
    rw [hMm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hdetL : (lam • 1 : Matrix (Fin 2) (Fin 2) F).det = lam ^ 2 := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  rw [hdetM, hdetL] at hdet
  have hne : (A : Matrix (Fin 2) (Fin 2) F).det * σ ((A : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 := by
    apply mul_ne_zero
    · exact Matrix.GeneralLinearGroup.det_ne_zero A
    · intro h
      exact Matrix.GeneralLinearGroup.det_ne_zero A (σ.injective (by rw [h, map_zero]))
  have hlam2 : lam ^ 2 ≠ 0 := by rw [← hdet]; exact hne
  have hlam : lam ≠ 0 := fun h0 => hlam2 (by rw [h0]; norm_num)
  exact ⟨hlam_eq.symm, hlam⟩

end Work.DSTR.M110
