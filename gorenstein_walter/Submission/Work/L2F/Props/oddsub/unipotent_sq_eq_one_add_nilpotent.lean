import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

/-!
# A unipotent `SL(2,F)` matrix in odd characteristic has `g * g = 1 + N`, `N` nilpotent non-zero

If `g = a • 1 + N₀` with `N₀ * N₀ = 0` and `N₀ ≠ 0` (i.e. `g` is unipotent) and `g.det = 1`,
then `a ^ 2 = 1` (because `det (a • 1 + N₀) = a ^ 2`, the trace and determinant of a square-zero
`2 × 2` matrix being `0`), so `g * g = 1 + 2 * a • N₀` with `2 * a ≠ 0` in odd characteristic.
Hence `g * g = 1 + N` for the non-zero square-zero matrix `N = 2 * a • N₀`.

The two auxiliary lemmas are the two ingredients: `trace`/`det` of a square-zero `2 × 2` matrix,
and the expansion of `(x + y) * (x + y)` when `y` commutes with `x` and `y * y = 0`.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

/-- A `2 × 2` matrix over a field satisfying `N * N = 0` has zero trace and zero determinant.

Indeed Cayley–Hamilton (`Work.L2F.Mat2.sq_eq_trace_smul_sub_det`) reads
`N * N = N.trace • N - N.det • 1`, so `N.trace • N = N.det • 1`.  Taking traces gives
`N.trace ^ 2 = N.det * 2` and taking determinants gives `N.trace ^ 2 * N.det = N.det ^ 2`;
combining, `N.det ^ 2 = 0`, so `N.det = 0`, and then `N.trace ^ 2 = 0` forces `N.trace = 0`. -/
theorem trace_eq_zero_and_det_eq_zero_of_sq_zero (F : Type*) [Field F]
    (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N = 0) : N.trace = 0 ∧ N.det = 0 := by
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F N
  rw [hN] at hCH
  have hkey : N.trace • N = N.det • (1 : Matrix (Fin 2) (Fin 2) F) :=
    sub_eq_zero.mp hCH.symm
  have h1 := congrArg Matrix.trace hkey
  rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at h1
  have h2 := congrArg Matrix.det hkey
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h2
  simp only [smul_eq_mul] at h1
  have hdet0 : N.det = 0 := by
    have htr2 : N.trace ^ 2 = N.det * 2 := by rw [pow_two]; exact h1
    rw [htr2] at h2
    have h5 : N.det * 2 * N.det - N.det ^ 2 = 0 := sub_eq_zero.mpr h2
    ring_nf at h5
    exact sq_eq_zero_iff.mp h5
  refine ⟨?_, hdet0⟩
  rw [hdet0] at h1
  simp at h1
  exact h1

/-- Expansion of a square with a square-zero summand: if `y * y = 0` and `y` commutes with `x`,
then `(x + y) * (x + y) = x * x + (x * y + x * y)`. -/
theorem add_mul_self_of_commute_of_sq_zero {R : Type*} [Ring R] (x y : R)
    (hyx : y * x = x * y) (hy : y * y = 0) :
    (x + y) * (x + y) = x * x + (x * y + x * y) := by
  rw [add_mul, mul_add, mul_add, hyx, hy, add_zero, ← add_assoc]

/-- A unipotent `g ∈ SL(2,F)` over a field of odd characteristic has a non-zero square-zero `N`
with `g * g = 1 + N`. -/
theorem unipotent_sq_eq_one_add_nilpotent (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) F) (hg : Work.L2F.Props.UnipotentMatrix g) (hdet : g.det = 1) :
    ∃ N : Matrix (Fin 2) (Fin 2) F, N ≠ 0 ∧ N * N = 0 ∧ g * g = 1 + N := by
  obtain ⟨a, hNne, hNsq⟩ := hg
  set N0 : Matrix (Fin 2) (Fin 2) F := g - a • 1 with hN0def
  obtain ⟨htrN, hdetN⟩ := trace_eq_zero_and_det_eq_zero_of_sq_zero F N0 hNsq
  -- `g = a • 1 + N₀`
  have hg_eq : g = a • 1 + N0 := by
    rw [hN0def]
    abel
  -- `a ^ 2 = 1`, from `1 = det g = det (a • 1 + N₀) = a ^ 2`
  have ha2 : a ^ 2 = 1 := by
    have h := Work.L2F.Mat2.det_smul_one_add_smul F N0 a 1
    rw [one_smul] at h
    rw [← hg_eq] at h
    rw [hdet, htrN, hdetN] at h
    simp at h
    exact h.symm
  have ha_ne : a ≠ 0 := by
    rintro rfl
    simp at ha2
  refine ⟨(2 * a) • N0, ?_, ?_, ?_⟩
  · exact smul_ne_zero (mul_ne_zero h2 ha_ne) hNne
  · simp only [Matrix.smul_mul, Matrix.mul_smul, hNsq, smul_zero]
  · rw [hg_eq]
    have hyx : N0 * (a • (1 : Matrix (Fin 2) (Fin 2) F)) = (a • 1) * N0 := by
      rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, one_mul]
    have hsq := add_mul_self_of_commute_of_sq_zero (a • (1 : Matrix (Fin 2) (Fin 2) F)) N0 hyx hNsq
    have hxx : (a • (1 : Matrix (Fin 2) (Fin 2) F)) * (a • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul]
      rw [← pow_two, ha2, one_smul]
    have hxy : (a • (1 : Matrix (Fin 2) (Fin 2) F)) * N0 = a • N0 := by
      rw [Matrix.smul_mul, one_mul]
    rw [hsq, hxx, hxy, ← add_smul, ← two_mul]

end Work.L2F.Props.oddsub
