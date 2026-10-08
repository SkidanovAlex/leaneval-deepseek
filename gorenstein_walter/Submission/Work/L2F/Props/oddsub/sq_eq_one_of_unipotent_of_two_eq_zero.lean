import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Mat2.trace_mul_self

namespace Work.L2F.Props.oddsub

open Matrix

/-- In characteristic `2`, a unipotent `2 × 2` matrix of determinant `1` is an involution
distinct from the identity.

Write `g = a • 1 + N` with `N ≠ 0` and `N * N = 0` (the definition of `UnipotentMatrix`).
A nonzero nilpotent `2 × 2` matrix has `det N = 0` (since `(det N)² = det (N * N) = 0`) and
`tr N = 0` (Newton's identity `tr (N * N) = (tr N)² - 2 det N` with `N * N = 0` and `det N = 0`).
Hence `tr g = 2 a + tr N = 0` because `2 = 0` in `F`, and Cayley–Hamilton
`g * g = tr g • g - det g • 1 = -1 = 1`.

If `g = 1` then `N = (1 - a) • 1` is a scalar matrix with `N * N = 0`, forcing `N = 0`, a
contradiction. -/
theorem sq_eq_one_of_unipotent_of_two_eq_zero (F : Type*) [Field F] (h2 : (2 : F) = 0)
    (g : Matrix (Fin 2) (Fin 2) F) (hg : Work.L2F.Props.UnipotentMatrix g) (hdet : g.det = 1) :
    g * g = 1 ∧ g ≠ 1 := by
  obtain ⟨a, hNne, hNsq⟩ := hg
  set N : Matrix (Fin 2) (Fin 2) F := g - a • (1 : Matrix (Fin 2) (Fin 2) F) with hN
  have hdecomp : g = a • (1 : Matrix (Fin 2) (Fin 2) F) + N := by rw [hN]; abel
  -- The nilpotent part `N` has zero determinant and zero trace.
  have hdetN : N.det = 0 := by
    have h : N.det * N.det = 0 := by
      rw [← Matrix.det_mul, hNsq, Matrix.det_zero]
    exact mul_self_eq_zero.mp h
  have htrN : N.trace = 0 := by
    have h := Work.L2F.Mat2.trace_mul_self F N
    rw [hNsq, Matrix.trace_zero, hdetN, mul_zero, sub_zero] at h
    have h' : N.trace * N.trace = 0 := by simpa [pow_two] using h.symm
    exact mul_self_eq_zero.mp h'
  -- `g` is traceless in characteristic two.
  have htrg : g.trace = 0 := by
    rw [hdecomp, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, htrN,
      add_zero, smul_eq_mul, Nat.cast_ofNat, h2, mul_zero]
  -- Cayley–Hamilton: `g * g = tr g • g - det g • 1 = -1 = 1`.
  have hgg : g * g = 1 := by
    rw [Work.L2F.Mat2.sq_eq_trace_smul_sub_det F g, htrg, hdet, zero_smul, one_smul, zero_sub]
    have hh : (1 : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := by
      rw [← two_smul F (1 : Matrix (Fin 2) (Fin 2) F), h2, zero_smul]
    exact neg_eq_of_add_eq_zero_right hh
  refine ⟨hgg, fun hone => ?_⟩
  -- If `g = 1`, then `N = (1 - a) • 1` is a scalar whose square vanishes.
  have hNc : N = (1 - a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hN, hone, sub_smul, one_smul]
  have hsq : (1 - a) * (1 - a) = 0 := by
    have h := hNsq
    rw [hNc] at h
    have h' : ((1 - a) * (1 - a)) • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
      simpa [Matrix.smul_mul, Matrix.one_mul, smul_smul] using h
    simpa [Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul] using
      congrFun (congrFun h' 0) 0
  rw [mul_self_eq_zero] at hsq
  exact hNne (by rw [hNc, hsq, zero_smul])

end Work.L2F.Props.oddsub
