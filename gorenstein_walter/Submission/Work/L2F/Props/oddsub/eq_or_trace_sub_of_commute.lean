import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

/-!
# Two matrices with the same trace and determinant commuting with a semisimple `g ∈ SL(2,F)`

The goal of this file is

`eq_or_trace_sub_of_commute`: if `g ∈ SL(2,F)` is *semisimple* (its characteristic polynomial
`X² - tr(g)·X + det(g)` is separable, see `Work.L2F.Props.SemisimpleSL`) and `z` commutes with `g`,
then `z` is determined up to the "reflection" `g ↦ tr(g)·1 - g` by the trace and the determinant:

  `z = g`  or  `z = tr(g)·1 - g`.

Note that `z` does **not** have to lie in `SL(2,F)` as far as the conclusion is concerned, but the
hypotheses `tr z = tr g`, `det z = det g = 1` do say exactly that.

## The proof

Write `A = z - g` and `B = z - (tr(g)·1 - g)`, so that `A = 0` is the first alternative and `B = 0`
the second.  Cayley–Hamilton for `2 × 2` matrices (`Work.L2F.Mat2.sq_eq_trace_smul_sub_det`)
together with `tr z = tr g`, `det z = det g` and the commutation relation gives

* `tr A = tr B = 0`  (both are traceless),
* `A * B = 0` and `B * A = 0`,
* `A - B = tr(g)·1 - 2·g`, hence `(A - B) * (A - B) = (tr(g)² - 4·det(g))·1` (again by
  Cayley–Hamilton for `g`).

If `A` and `B` were both nonzero, then from `A * A * B = 0` and the identity
`C² = -det C·1` for a traceless `C` we get `det A = 0` (as `B ≠ 0`), so `A * A = 0`; symmetrically
`B * B = 0`.  Then `(A - B) * (A - B) = A·A - A·B - B·A + B·B = 0`, so
`(tr(g)² - 4·det(g))·1 = 0` and hence `tr(g)² - 4·det(g) = 0`, contradicting separability of the
characteristic polynomial of `g` (for `SemisimpleSL` this holds in *every* characteristic: in
character `2` the inequality is simply `tr(g) ≠ 0`).
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

/-- Cayley–Hamilton for a traceless `2 × 2` matrix: `M * M = -det M • 1`. -/
theorem sq_eq_neg_det_smul_one (F : Type*) [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (htr : M.trace = 0) : M * M = -M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F M
  rw [htr] at h
  rw [h, zero_smul, zero_sub]
  exact (neg_smul M.det (1 : Matrix (Fin 2) (Fin 2) F)).symm

/-- If `A * A = A * B = B * A = B * B = 0` then also `(A - B) * (A - B) = 0`. -/
theorem sub_mul_self_eq_zero {F : Type*} [Field F] {A B : Matrix (Fin 2) (Fin 2) F}
    (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0) :
    (A - B) * (A - B) = 0 := by
  rw [sub_mul, mul_sub, mul_sub, hAA, hAB, hBA, hBB]
  simp

/-- A traceless `2 × 2` matrix `A` with `A * B = 0` and `B ≠ 0` has vanishing determinant
(equivalently `A * A = 0`). -/
theorem det_eq_zero_of_traceless_mul_eq_zero {F : Type*} [Field F] {A B : Matrix (Fin 2) (Fin 2) F}
    (htrA : A.trace = 0) (hAB : A * B = 0) (hB : B ≠ 0) : A.det = 0 := by
  have hAsq : A * A = -A.det • (1 : Matrix (Fin 2) (Fin 2) F) := sq_eq_neg_det_smul_one F A htrA
  have h2 : A * A * B = -A.det • B := by rw [hAsq, smul_mul, one_mul]
  have h1 : A * A * B = 0 := by rw [mul_assoc, hAB, mul_zero]
  have hz : -A.det • B = 0 := by rw [← h2, h1]
  rcases smul_eq_zero.mp hz with h' | h'
  · exact neg_eq_zero.mp h'
  · exact absurd h' hB

/-- The identity matrix is nonzero. -/
theorem one_matrix_ne_zero (F : Type*) [Field F] : (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
  intro hh
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hh
  simp at this

/-- A scalar matrix `r • 1` is zero only if `r = 0`. -/
theorem eq_zero_of_smul_one_eq_zero {F : Type*} [Field F] (r : F)
    (h : r • (1 : Matrix (Fin 2) (Fin 2) F) = 0) : r = 0 := by
  rcases smul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (one_matrix_ne_zero F)

/-- **`z` is determined by its trace and determinant among the matrices commuting with a semisimple
`g ∈ SL(2,F)`.**  If `g.det = 1`, `g` has separable characteristic polynomial, `z * g = g * z`,
`tr z = tr g` and `det z = det g`, then `z = g` or `z = tr(g) • 1 - g`. -/
theorem eq_or_trace_sub_of_commute (F : Type*) [Field F]
    (g z : Matrix (Fin 2) (Fin 2) F) (hg : g.det = 1) (ht : Work.L2F.Props.SemisimpleSL g)
    (hcomm : z * g = g * z) (htr : z.trace = g.trace) (hdet : z.det = g.det) :
    z = g ∨ z = g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g := by
  -- Separability of the characteristic polynomial, uniformly over the two cases of `SemisimpleSL`.
  have hsep : g.trace ^ 2 - 4 * g.det ≠ 0 := by
    rcases ht with ⟨_, h | h⟩
    · exact h.2
    · obtain ⟨h2, htne⟩ := h
      rw [hg, mul_one]
      have h4 : (4 : F) = 0 := by rw [show (4 : F) = 2 * 2 by norm_num, h2, mul_zero]
      rw [h4, sub_zero]
      exact pow_ne_zero 2 htne
  -- Cayley–Hamilton for `z` and for `g`.
  have hzz : z * z = g.trace • z - g.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F z
    rw [htr, hdet] at h
    exact h
  have hgg : g * g = g.trace • g - g.det • (1 : Matrix (Fin 2) (Fin 2) F) :=
    Work.L2F.Mat2.sq_eq_trace_smul_sub_det F g
  -- The two candidate differences are traceless.
  have htrA : (z - g).trace = 0 := by rw [Matrix.trace_sub, htr, sub_self]
  have htrB : (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g)).trace = 0 := by
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, htr]
    ring
  -- ... and they annihilate each other in both orders.
  have hAB : (z - g) * (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g)) = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, hcomm, hzz, hgg]
    module
  have hBA : (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g)) * (z - g) = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hcomm, hzz, hgg]
    module
  -- Their difference is `tr(g) • 1 - 2 • g`.
  have hsub : (z - g) - (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g))
      = g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - (2 : F) • g := by
    module
  have hC2 : (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - (2 : F) • g)
      * (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - (2 : F) • g)
      = (g.trace ^ 2 - 4 * g.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hgg]
    module
  -- Main step: one of the two differences must vanish.
  have key : z - g = 0 ∨ z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g) = 0 := by
    by_contra h
    simp only [not_or] at h
    obtain ⟨hA0, hB0⟩ := h
    have hdetA : (z - g).det = 0 := det_eq_zero_of_traceless_mul_eq_zero htrA hAB hB0
    have hdetB : (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g)).det = 0 :=
      det_eq_zero_of_traceless_mul_eq_zero htrB hBA hA0
    have hAA : (z - g) * (z - g) = 0 := by
      rw [sq_eq_neg_det_smul_one F (z - g) htrA, hdetA, neg_zero, zero_smul]
    have hBB : (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g))
        * (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g)) = 0 := by
      rw [sq_eq_neg_det_smul_one F (z - (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - g)) htrB,
        hdetB, neg_zero, zero_smul]
    have hCzero : (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - (2 : F) • g)
        * (g.trace • (1 : Matrix (Fin 2) (Fin 2) F) - (2 : F) • g) = 0 := by
      rw [← hsub]
      exact sub_mul_self_eq_zero hAA hAB hBA hBB
    have h00 : g.trace ^ 2 - 4 * g.det = 0 := by
      have h := hC2
      rw [hCzero] at h
      exact eq_zero_of_smul_one_eq_zero _ h.symm
    exact hsep h00
  rcases key with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

end Work.L2F.Props.oddsub
