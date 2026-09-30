import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Matrix

section SectionFactor

open scoped MatrixOrder

/-- **Matrix factorisation.**  If `Aᵀ * A` is invertible (i.e. `A` has full column rank) then `A`
factors as `A = B * S` with `Bᵀ * B = 1` (orthonormal columns) and `S` invertible with
`S.det = √(Aᵀ * A).det`.

The construction takes `S` to be the positive semidefinite square root of the Gram matrix
`Aᵀ * A` and `B = A * S⁻¹`; then `Bᵀ * B = S⁻¹ (Aᵀ A) S⁻¹ = S⁻¹ S S S⁻¹ = 1`. -/
theorem sectionFactor {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : (A.transpose * A).det ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin k) ℝ, ∃ S : Matrix (Fin k) (Fin k) ℝ,
      B.transpose * B = 1 ∧ A = B * S ∧ S.det = Real.sqrt (A.transpose * A).det ∧ S.det ≠ 0 := by
  classical
  have hG : (A.transpose * A).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self A
    have hc : Aᴴ = A.transpose := by ext i j; simp [Matrix.conjTranspose_apply]
    rwa [hc] at h
  set S : Matrix (Fin k) (Fin k) ℝ := CFC.sqrt (A.transpose * A) with hS
  have hS2 : S * S = A.transpose * A := by
    rw [hS]
    have := CFC.sq_sqrt (A.transpose * A)
    simpa [sq] using this
  have hSt : Sᵀ = S := by
    rw [hS]
    have h : IsSelfAdjoint (CFC.sqrt (A.transpose * A)) :=
      IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
    have h' : (CFC.sqrt (A.transpose * A))ᴴ = CFC.sqrt (A.transpose * A) := h
    simpa using h'
  have hSsig : S.det * S.det = (A.transpose * A).det := by
    rw [← Matrix.det_mul, hS2]
  have hSdet_ne : S.det ≠ 0 := fun h => hA (by rw [← hSsig]; simp [h])
  have hSdet_eq : S.det = Real.sqrt (A.transpose * A).det := by
    rw [hS]
    have := Matrix.PosSemidef.det_sqrt hG
    simpa using this
  have h1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hSdet_ne)
  have h2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hSdet_ne)
  refine ⟨A * S⁻¹, S, ?_, ?_, hSdet_eq, hSdet_ne⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hSt]
    calc (S⁻¹ * Aᵀ) * (A * S⁻¹)
        = S⁻¹ * (Aᵀ * (A * S⁻¹)) := by rw [Matrix.mul_assoc (S⁻¹) Aᵀ (A * S⁻¹)]
      _ = S⁻¹ * ((Aᵀ * A) * S⁻¹) := by rw [← Matrix.mul_assoc Aᵀ A S⁻¹]
      _ = S⁻¹ * ((S * S) * S⁻¹) := by rw [hS2]
      _ = S⁻¹ * (S * (S * S⁻¹)) := by rw [Matrix.mul_assoc S S S⁻¹]
      _ = S⁻¹ * (S * 1) := by rw [h2]
      _ = S⁻¹ * S := by rw [Matrix.mul_one]
      _ = 1 := h1
  · rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end SectionFactor

/-- **Change of variables for an invertible matrix.**  For `S : Matrix (Fin k) (Fin k) ℝ` with
`S.det ≠ 0` and any measurable `g`, the integral of `g ∘ (fun x ↦ S *ᵥ x)` against Lebesgue
measure on `ℝᵏ` is `|S.det|⁻¹` times the integral of `g`.

This is `Real.map_matrix_volume_pi_eq_smul_volume_pi` composed with `MeasureTheory.integral_map`
and `MeasureTheory.integral_smul_measure`. -/
theorem integral_comp_mulVec {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.det ≠ 0)
    (g : (Fin k → ℝ) → ℝ) (hg : Measurable g) :
    ∫ x : Fin k → ℝ, g (S *ᵥ x) = |S.det|⁻¹ * ∫ x : Fin k → ℝ, g x := by
  have hφ : AEMeasurable (Matrix.toLin' S) (volume : Measure (Fin k → ℝ)) :=
    ((Matrix.toLin' S).continuous_of_finiteDimensional.measurable).aemeasurable
  calc ∫ x : Fin k → ℝ, g (S *ᵥ x)
      = ∫ x : Fin k → ℝ, g ((Matrix.toLin' S) x) := by simp [Matrix.toLin'_apply]
    _ = ∫ y : Fin k → ℝ, g y ∂(Measure.map (Matrix.toLin' S) volume) :=
        (integral_map hφ hg.aestronglyMeasurable).symm
    _ = ∫ y : Fin k → ℝ, g y ∂(ENNReal.ofReal |S.det⁻¹| • volume) := by
        rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hS]
    _ = (ENNReal.ofReal |S.det⁻¹|).toReal * ∫ y : Fin k → ℝ, g y := by
        rw [integral_smul_measure, smul_eq_mul]
    _ = |S.det|⁻¹ * ∫ y : Fin k → ℝ, g y := by
        rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

/-- **Section reduction.**  For a real `n × k` matrix `A` whose Gram matrix `Aᵀ * A` is invertible,
there is an `n × k` matrix `B` with orthonormal columns (`Bᵀ * B = 1`) such that the volume of
`{x : ℝᵏ | |(A x)ᵢ| ≤ 1/2 for all i}` equals `(det (Aᵀ * A))^{-1/2}` times the volume of
`{z : ℝᵏ | |(B z)ᵢ| ≤ 1/2 for all i}`.

Indeed, writing `A = B * S` with `S` invertible (`sectionFactor`), the left-hand side is the
integral of `1_C ∘ (fun x ↦ A *ᵥ x) = (1_C ∘ (fun w ↦ B *ᵥ w)) ∘ (fun x ↦ S *ᵥ x)` where `C` is
the cube `{y : ℝⁿ | |yᵢ| ≤ 1/2}`, so the change-of-variables formula `integral_comp_mulVec` turns
it into `|S.det|⁻¹` times the right-hand side, and `|S.det| = S.det = √(det (Aᵀ * A))`. -/
theorem sectionReduction {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : (A.transpose * A).det ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin k) ℝ, B.transpose * B = 1 ∧
      ∫ x : Fin k → ℝ, (if ∀ i, |(A.mulVec x) i| ≤ 1/2 then (1:ℝ) else 0)
        = (Real.sqrt (A.transpose*A).det)⁻¹ * ∫ z : Fin k → ℝ, (if ∀ i, |(B.mulVec z) i| ≤ 1/2 then (1:ℝ) else 0) := by
  obtain ⟨B, S, hB, hAeq, hSdet_eq, hSdet_ne⟩ := sectionFactor A hA
  refine ⟨B, hB, ?_⟩
  set C : Set (Fin n → ℝ) := {y | ∀ i, |y i| ≤ 1/2} with hC
  have hCmeas : MeasurableSet C := by
    rw [hC, show {y : Fin n → ℝ | ∀ i, |y i| ≤ 1/2} = ⋂ i, {y | |y i| ≤ 1/2} by ext y; simp]
    exact MeasurableSet.iInter fun i =>
      (isClosed_le (continuous_apply i).abs continuous_const).measurableSet
  have hg : Measurable (fun w : Fin k → ℝ => C.indicator (fun _ => (1:ℝ)) (B.mulVec w)) := by
    fun_prop
  have step1 : ∫ x : Fin k → ℝ, (if ∀ i, |(A.mulVec x) i| ≤ 1/2 then (1:ℝ) else 0)
      = ∫ x : Fin k → ℝ, (fun w => C.indicator (fun _ => (1:ℝ)) (B.mulVec w)) (S.mulVec x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hAeq, Matrix.mulVec_mulVec, hC]
    simp [Set.indicator_apply]
  rw [step1, integral_comp_mulVec S hSdet_ne _ hg]
  have key : |S.det|⁻¹ = (Real.sqrt (A.transpose * A).det)⁻¹ := by
    rw [hSdet_eq, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [key]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [hC]
  simp [Set.indicator_apply]

end Work.BW
