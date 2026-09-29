import Mathlib

/-!
# `Work.TMC14Core.traceUnitaryLe`

For a rank-one matrix `M = c • vecMulVec v (star v)` and a unitary matrix `W`,
the trace of `M * W` is controlled by the trace of `M`:

  `‖(M * W).trace‖ ≤ ‖M.trace‖`.

Proof sketch. Writing `M = c • (v *ᵥ v†)`, one has
`(M * W).trace = c * ⟪v, W v⟫` (with `⟪·,·⟫` the hermitian inner product on
`EuclideanSpace ℂ (Fin n)`) and `M.trace = c * ⟪v, v⟫ = c * ‖v‖²`.  Since `W` is
unitary it is an isometry of `EuclideanSpace ℂ (Fin n)`, so Cauchy–Schwarz gives
`‖⟪v, W v⟫‖ ≤ ‖v‖ * ‖W v‖ = ‖v‖² = ‖⟪v, v⟫‖`.  Multiplying by `‖c‖` finishes.
-/

open Matrix WithLp

namespace Work.TMC14Core

theorem traceUnitaryLe {n : ℕ} (c : ℂ) (v : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖((c • Matrix.vecMulVec v (star v)) * W).trace‖ ≤ ‖(c • Matrix.vecMulVec v (star v)).trace‖ := by
  -- `W` acts on `EuclideanSpace ℂ (Fin n)` by an isometry.
  have hU : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) W ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
    rw [Unitary.mem_iff]
    exact ⟨by rw [← map_star, ← map_mul, Matrix.mem_unitaryGroup_iff'.mp hW, map_one],
           by rw [← map_star, ← map_mul, Matrix.mem_unitaryGroup_iff.mp hW, map_one]⟩
  have hnorm : ‖WithLp.toLp 2 (W *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
    have h2 := Unitary.norm_map
      ⟨(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) W, hU⟩ (WithLp.toLp 2 v)
    rwa [Matrix.toEuclideanCLM_toLp] at h2
  -- Rewrite both traces as `c` times an inner product.
  have hL : ((c • Matrix.vecMulVec v (star v)) * W).trace
      = c * inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 (W *ᵥ v)) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
      Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct]
  have hR : (c • Matrix.vecMulVec v (star v)).trace
      = c * inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_vecMulVec,
      EuclideanSpace.inner_eq_star_dotProduct]
  rw [hL, hR, norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  calc ‖inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 (W *ᵥ v))‖
      ≤ ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 (W *ᵥ v)‖ := norm_inner_le_norm _ _
    _ = ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 v‖ := by rw [hnorm]
    _ = ‖WithLp.toLp 2 v‖ ^ 2 := by ring
    _ = ‖inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v)‖ := by
        rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]

end Work.TMC14Core
