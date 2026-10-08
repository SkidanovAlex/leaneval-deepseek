import Mathlib
import Submission.Work.DSTR.M110.Defs

/-!
# A semilinear involution of `ℙ¹(F)` has a fixed point

Let `F` be a field, `σ : F ≃+* F` an involution (`σ (σ x) = x`), `A ∈ GL(2,F)` and `lam ∈ F`
with `A * σ(A) = lam • 1`, where `σ(A)` is the entrywise image of `A` under `σ`, and suppose
`lam = μ * σ μ` for some `μ ∈ F`.

Then the "semilinear" permutation `y ↦ A · (σ y)` of the projective line `ℙ¹(F) = OnePoint F`
has a fixed point, i.e. the permutation `pglHom (mk A) * galHom σ` fixes a point.

The proof is elementary.  Renormalising `A` by `μ⁻¹` we may assume `A σ(A) = 1`, so that the
semilinear map `S : v ↦ A · σ(v)` on `F²` satisfies `S² = id`.  For any non-zero `v`, the vector
`w = v + S v` is fixed by `S`; if `w = 0` then `v` is an eigenvector of `S` with eigenvalue `-1`.
Passing to the projective line, an eigenvector of `A · σ(–)` is exactly a fixed point of
`pglHom (mk A) * galHom σ`.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Matrix

namespace Work.DSTR.M110

variable {F : Type*} [Field F] [DecidableEq F]

/-- The action of the `PGL`-element `mk A` on `ℙ¹(F)` is the action of the matrix `A`. -/
lemma semilinear_pglHom_mk_apply (A : GL (Fin 2) F) (x : Work.AUTL2.P1 F) :
    Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) x = A • x := by
  show (Matrix.ProjGenLinGroup.mk A) • x = A • x
  rw [Matrix.ProjGenLinGroup.mk_smul (fun u a => Work.AUTL2.scalar_smul_eq_self F u a)]

/-- The action of `GL(2,F)` on `F²` is matrix--vector multiplication. -/
lemma semilinear_gl_smul_eq_mulVec (A : GL (Fin 2) F) (v : Fin 2 → F) :
    A • v = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
  rw [Matrix.GeneralLinearGroup.fin_two_smul]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Applying the field automorphism `σ` to the coordinates of a projective point. -/
lemma semilinear_equivProjectivization_map (σ : F ≃+* F) (v : Fin 2 → F) (hv : v ≠ 0)
    (hσv : (fun i => σ (v i)) ≠ 0) :
    OnePoint.equivProjectivization F
        (OnePoint.map σ ((OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv)))
      = Projectivization.mk F (fun i => σ (v i)) hσv := by
  rw [OnePoint.equivProjectivization_symm_apply_mk]
  split_ifs with h1
  · rw [OnePoint.map_infty, OnePoint.equivProjectivization_apply_infinity]
    have hv0 : v 0 ≠ 0 := by
      intro h; exact hv (by funext i; fin_cases i <;> simp [h, h1])
    have hσv0 : σ (v 0) ≠ 0 := by
      intro h; exact hv0 (σ.injective (by rw [h, map_zero]))
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨(σ (v 0))⁻¹, ?_⟩
    funext i
    fin_cases i
    · simp [inv_mul_cancel₀ hσv0]
    · simp [h1]
  · simp only [OnePoint.map_some, OnePoint.equivProjectivization_apply_coe]
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨(σ (v 1))⁻¹, ?_⟩
    funext i
    fin_cases i <;> simp [map_inv₀, h1]

/-- A `σ`-eigenvector of the semilinear map `A · σ(–)` on `F²` yields a fixed point of the
projective permutation `pglHom (mk A) * galHom σ` on `ℙ¹(F)`. -/
lemma semilinear_eigenvector_fixed (A : GL (Fin 2) F) (σ : F ≃+* F)
    (v : Fin 2 → F) (hv : v ≠ 0) (c : F)
    (hAv : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) = c • v) :
    (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) * Work.AUTL2.galHom F σ)
        ((OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv)) =
      (OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv) := by
  have hσv : (fun i => σ (v i)) ≠ 0 := by
    intro h; apply hv; funext i
    have hh := congrFun h i
    simpa using congrArg (⇑σ.symm) hh
  have hgal : Work.AUTL2.galHom F σ
        ((OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv))
      = OnePoint.map σ ((OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv)) :=
    rfl
  rw [Equiv.Perm.mul_apply, hgal, semilinear_pglHom_mk_apply, Equiv.smul_def,
      semilinear_equivProjectivization_map σ v hv hσv]
  refine congrArg (⇑(OnePoint.equivProjectivization F).symm) ?_
  rw [Projectivization.smul_mk]
  refine (Projectivization.mk_eq_mk_iff' F (A • (fun i => σ (v i))) v _ hv).mpr ⟨c, ?_⟩
  rw [semilinear_gl_smul_eq_mulVec]
  exact hAv.symm

/-- `v ↦ B · σ(v)` is an involution of `F²` as soon as `B · σ(B) = 1`. -/
lemma semilinear_sq (B : Matrix (Fin 2) (Fin 2) F) (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) (hB : B * B.map ⇑σ = 1) (v : Fin 2 → F) :
    B *ᵥ (fun i => σ ((B *ᵥ fun j => σ (v j)) i)) = v := by
  have h1 : (fun i => σ ((B *ᵥ fun j => σ (v j)) i))
      = (B.map ⇑σ) *ᵥ (fun i => σ (σ (v i))) := by
    funext i
    simpa using RingHom.map_mulVec (σ : F →+* F) B (fun j => σ (v j)) i
  rw [h1]
  have h2 : (fun i => σ (σ (v i))) = v := funext fun i => hσ2 (v i)
  rw [h2, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

/-- `v ↦ B · σ(v)` is additive. -/
lemma semilinear_add (B : Matrix (Fin 2) (Fin 2) F) (σ : F ≃+* F) (a b : Fin 2 → F) :
    B *ᵥ (fun i => σ ((a + b) i))
      = B *ᵥ (fun i => σ (a i)) + B *ᵥ (fun i => σ (b i)) := by
  have h : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + (fun i => σ (b i)) := by
    funext i; simp [map_add]
  rw [h, Matrix.mulVec_add]

theorem semilinearFixedPoint {F : Type*} [Field F] [DecidableEq F]
    (σ : F ≃+* F) (hσ2 : ∀ x : F, σ (σ x) = x)
    (A : GL (Fin 2) F) (lam : F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.GeneralLinearGroup.map (σ : F →+* F) A = lam • 1)
    (hμ : ∃ μ : F, μ * σ μ = lam) :
    ∃ y : Work.AUTL2.P1 F,
      (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) * Work.AUTL2.galHom F σ) y = y := by
  obtain ⟨μ, hμ⟩ := hμ
  -- The entrywise-image form of the hypothesis.
  have hcoe : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) A : GL (Fin 2) F)
      : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F).map ⇑σ := by simp
  have hAcoe : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F).map ⇑σ
      = lam • 1 := by
    rw [← hcoe]; exact hA
  have hdetA : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero A
  have hσdetA : σ ((A : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 := by
    simpa using σ.injective.ne hdetA
  have hmd : ((A : Matrix (Fin 2) (Fin 2) F).map ⇑σ).det
      = σ ((A : Matrix (Fin 2) (Fin 2) F).det) := by
    simpa using (RingEquiv.map_det σ (A : Matrix (Fin 2) (Fin 2) F)).symm
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det * σ ((A : Matrix (Fin 2) (Fin 2) F).det)
      = lam ^ 2 := by
    have h := congrArg Matrix.det hA
    rw [Matrix.det_mul, hcoe, hmd, Matrix.det_smul, Fintype.card_fin, Matrix.det_one,
        mul_one] at h
    exact h
  have hlam : lam ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero hdetA hσdetA) (by simpa using hdet)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hlam (by simpa using hμ.symm)
  -- Normalise: `B = μ⁻¹ • A` is a `σ`-semilinear involution of `F²`.
  set B : Matrix (Fin 2) (Fin 2) F := μ⁻¹ • (A : Matrix (Fin 2) (Fin 2) F) with hBdef
  have hAmulB : (A : Matrix (Fin 2) (Fin 2) F) = μ • B := by
    rw [hBdef, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hBmap : B.map ⇑σ = σ (μ⁻¹) • (A : Matrix (Fin 2) (Fin 2) F).map ⇑σ := by
    rw [hBdef, Matrix.map_smul' ⇑σ μ⁻¹ (A : Matrix (Fin 2) (Fin 2) F)
      (fun a b => map_mul σ a b)]
  have hσμ0 : σ μ ≠ 0 := by simpa using σ.injective.ne hμ0
  have hsc : μ⁻¹ * σ μ⁻¹ * lam = 1 := by
    rw [map_inv₀, ← hμ]
    rw [show μ⁻¹ * (σ μ)⁻¹ * (μ * σ μ) = (μ⁻¹ * μ) * ((σ μ)⁻¹ * σ μ) by ring,
        inv_mul_cancel₀ hμ0, one_mul, inv_mul_cancel₀ hσμ0]
  have hB : B * B.map ⇑σ = 1 := by
    rw [hBmap, hBdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAcoe, smul_smul, hsc,
        one_smul]
  -- The semilinear involution `S : v ↦ B · σ(v)`.
  have hSS : ∀ v : Fin 2 → F, B *ᵥ (fun i => σ ((B *ᵥ fun j => σ (v j)) i)) = v :=
    fun v => semilinear_sq B σ hσ2 hB v
  have hSadd : ∀ a b : Fin 2 → F,
      B *ᵥ (fun i => σ ((a + b) i))
        = B *ᵥ (fun i => σ (a i)) + B *ᵥ (fun i => σ (b i)) :=
    fun a b => semilinear_add B σ a b
  -- A non-zero eigenvector of the semilinear map `A · σ(–)`.
  set e : Fin 2 → F := ![1, 0] with hedef
  have he : e ≠ 0 := by
    intro h
    have h0 : e 0 = 0 := congrFun h 0
    rw [hedef] at h0
    simp only [Matrix.cons_val_zero] at h0
    exact (one_ne_zero : (1 : F) ≠ 0) h0
  obtain ⟨v, hv, c, hvc⟩ : ∃ v : Fin 2 → F, v ≠ 0 ∧ ∃ c : F,
      (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) = c • v := by
    by_cases hu : e + B *ᵥ (fun i => σ (e i)) = 0
    · have hSe : B *ᵥ (fun i => σ (e i)) = -e := eq_neg_of_add_eq_zero_right hu
      refine ⟨e, he, -μ, ?_⟩
      rw [hAmulB, Matrix.smul_mulVec, hSe, smul_neg, neg_smul]
    · have hSu : B *ᵥ (fun i => σ ((e + B *ᵥ fun j => σ (e j)) i))
          = e + B *ᵥ (fun i => σ (e i)) := by
        rw [hSadd e (B *ᵥ fun j => σ (e j)), hSS e]
        abel
      refine ⟨e + B *ᵥ (fun i => σ (e i)), hu, μ, ?_⟩
      rw [hAmulB, Matrix.smul_mulVec, hSu]
  exact ⟨(OnePoint.equivProjectivization F).symm (Projectivization.mk F v hv),
    semilinear_eigenvector_fixed A σ v hv c hvc⟩

end Work.DSTR.M110
