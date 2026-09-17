import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.posSemidef_spectral

open Matrix

namespace Commons.LinearAlgebra.Matrix

open scoped BigOperators

/-- The trace of the product of two positive semidefinite real matrices is non-negative.

This is proved by diagonalizing the first matrix: writing `A = Vᵀ ⬝ diagonal d ⬝ V` with
`d i ≥ 0`, cyclicity of the trace gives `trace (A * B) = ∑ i, d i * (V * B * Vᵀ) i i`, and each
summand is non-negative because `d i ≥ 0` and `V * B * Vᵀ` is positive semidefinite. -/
lemma posSemidef_trace_mul_nonneg {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨V, d, _hV, hd, hAeq⟩ := posSemidef_spectral A hA
  rw [hAeq]
  have hVBV : (V * B * Vᵀ).PosSemidef := by
    have h := hB.conjTranspose_mul_mul_same (Vᵀ)
    simpa using h
  have htrace : (Vᵀ * Matrix.diagonal d * V * B).trace
      = (Matrix.diagonal d * (V * B * Vᵀ)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htrace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hd i) hVBV.diag_nonneg)

/-- If the quadratic form of a symmetric matrix `C` is bounded below by `c₁ * ‖·‖²`, then
`c₁ * trace N ≤ trace (C * N)` for every positive semidefinite `N`. -/
theorem trace_mul_ge_of_quadform_ge {d : ℕ} (C N : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.IsSymm) (hN : N.IsSymm) (hNpsd : N.PosSemidef) {c₁ : ℝ}
    (h1 : ∀ v : Fin d → ℝ, c₁ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (C.mulVec v)) :
    c₁ * N.trace ≤ (C * N).trace := by
  classical
  -- `C - c₁ • 1` is positive semidefinite.
  have hApsd : (C - c₁ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · exact (Matrix.isHermitian_iff_isSymm).mpr
        (hC.sub ((isSymm_one (α := ℝ) (n := Fin d)).smul c₁))
    · intro v
      have hv : c₁ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (C *ᵥ v) := h1 v
      have hcalc : star v ⬝ᵥ ((C - c₁ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v)
          = v ⬝ᵥ (C *ᵥ v) - c₁ * (v ⬝ᵥ v) := by
        simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
      rw [hcalc]
      linarith
  have hkey : 0 ≤ ((C - c₁ • (1 : Matrix (Fin d) (Fin d) ℝ)) * N).trace :=
    posSemidef_trace_mul_nonneg hApsd hNpsd
  -- Split `C * N = (C - c₁ • 1) * N + (c₁ • 1) * N` and compute the second trace.
  have hdecomp : (C - c₁ • (1 : Matrix (Fin d) (Fin d) ℝ)) * N
      + (c₁ • (1 : Matrix (Fin d) (Fin d) ℝ)) * N = C * N := by
    rw [← Matrix.add_mul, sub_add_cancel]
  have htrace : (C * N).trace = ((C - c₁ • (1 : Matrix (Fin d) (Fin d) ℝ)) * N).trace
      + c₁ * N.trace := by
    rw [← hdecomp, Matrix.trace_add, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul]
  rw [htrace]
  linarith

end Commons.LinearAlgebra.Matrix
