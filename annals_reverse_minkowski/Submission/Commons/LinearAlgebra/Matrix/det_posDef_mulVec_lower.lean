import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub
import Submission.Commons.LinearAlgebra.Matrix.posDef_lower_bound_quadratic

open scoped Matrix BigOperators
open Matrix

namespace Commons.LinearAlgebra.Matrix

/-- `Aᵀ (G - c·1) A = AᵀGA - c · AᵀA` for real matrices. -/
lemma det_posDef_mulVec_lower_congalg {n r : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin r) ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) :
    Aᵀ * (G - c • (1 : Matrix (Fin n) (Fin n) ℝ)) * A
      = Aᵀ * G * A - c • (Aᵀ * A) := by
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.mul_one]

/-- If `c · ‖x‖² ≤ xᵀGx` for every `x`, then `G - c·1` is positive semidefinite. -/
lemma det_posDef_mulVec_lower_gminus_psd {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (c : ℝ) (hquad : ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G *ᵥ x)) :
    (G - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?herm ?ineq
  · rw [Matrix.isHermitian_iff_isSymm]
    exact (Matrix.isHermitian_iff_isSymm.mp hG.isHermitian).sub (Matrix.isSymm_one.smul c)
  · intro x
    have hexp : x ⬝ᵥ ((G - c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)
        = x ⬝ᵥ (G *ᵥ x) - c * (x ⬝ᵥ x) := by
      calc
        x ⬝ᵥ ((G - c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)
            = x ⬝ᵥ (G *ᵥ x - (c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) := by
                rw [sub_mulVec]
        _ = x ⬝ᵥ (G *ᵥ x - c • x) := by
                rw [smul_mulVec, one_mulVec]
        _ = x ⬝ᵥ (G *ᵥ x) - c * (x ⬝ᵥ x) := by simp
    simpa [hexp] using (sub_nonneg.mpr (hquad x))

theorem det_posDef_mulVec_lower {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ {r : ℕ} (A : Matrix (Fin n) (Fin r) ℝ),
      (c : ℝ) ^ r * ((A.transpose * A).det) ≤ ((A.transpose * G * A).det) := by
  classical
  obtain ⟨c, hc0, hc⟩ := posDef_lower_bound_quadratic G hG
  refine ⟨c, hc0, ?_⟩
  intro r A
  -- Rewrite the quadratic bound in dot-product form: `c · (x ⬝ᵥ x) ≤ x ⬝ᵥ (G *ᵥ x)`.
  have hquad : ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G *ᵥ x) := by
    intro x
    have hxnorm : (∑ i : Fin n, (x i) ^ 2) = x ⬝ᵥ x := by
      simp [dotProduct, pow_two]
    simpa [hxnorm] using hc x
  -- Then `G - c·1` is positive semidefinite, so by congruence
  -- `AᵀGA - c·(AᵀA) = Aᵀ (G - c·1) A` is positive semidefinite.
  have hGm : (G - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    det_posDef_mulVec_lower_gminus_psd G hG c hquad
  have hcong0 : (Aᴴ * (G - c • (1 : Matrix (Fin n) (Fin n) ℝ)) * A).PosSemidef :=
    hGm.conjTranspose_mul_mul_same A
  have hcong1 : (Aᵀ * (G - c • (1 : Matrix (Fin n) (Fin n) ℝ)) * A).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hcong0
  have hsub_psd : (Aᵀ * G * A - c • (Aᵀ * A)).PosSemidef := by
    simpa [det_posDef_mulVec_lower_congalg c A G] using hcong1
  -- `c·(AᵀA)` is positive semidefinite (as `c ≥ 0` and `AᵀA` is).
  have hA0 : (c • (Aᵀ * A)).PosSemidef := by
    have hpsd : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) A
    have hpsdT : (Aᵀ * A).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hpsd
    exact hpsdT.smul (le_of_lt hc0)
  -- Determinants of ordered positive semidefinite matrices are ordered.
  have hdet : (c • (Aᵀ * A)).det ≤ (Aᵀ * G * A).det := by
    exact det_mono_posSemidef_sub hA0 hsub_psd
  -- Finally `det (c • (AᵀA)) = c ^ r · det (AᵀA)`.
  simpa [Matrix.det_smul] using hdet

end Commons.LinearAlgebra.Matrix
