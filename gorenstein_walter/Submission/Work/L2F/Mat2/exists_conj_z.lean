import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Mat2.trace_mul_self
import Submission.Work.L2F.Mat2.trace_eq_zero_of_sq_eq_neg_one
import Submission.Work.L2F.Mat2.conj_z_of_entries

namespace Work.L2F.Mat2

/-- Every `x ∈ SL(2,F)` with `x² = -1` and `(2:F) ≠ 0` is conjugate over `GL(2,F)` to
`!![0,1;-1,0]`.  Proof: `x` is not a scalar matrix (`x = λ • 1` with `x² = -1` gives
`det x = λ² = -1 ≠ 1` since `2 ≠ 0`), so there is `v ≠ 0` with `x v ∉ F v`; in the basis
`(v, x v)` the matrix of `x` is `!![0,1;-1,0]`, and `P := (v | x v)` has `det ≠ 0` and satisfies
`P * x = !![0,1;-1,0] * P`.

Formalised entrywise: Cayley–Hamilton together with `det x = 1` and `x² = -1` gives
`tr x = 0` (`Work.L2F.Mat2.trace_eq_zero_of_sq_eq_neg_one`), so writing
`x = !![a,b;c,d]` we have `d = -a`, and the `(0,0)` entry of `x² = -1` is `a² + bc = -1`.
`Work.L2F.Mat2.conj_z_of_entries` then produces the conjugating matrix (the non-scalarity
argument of the informal proof, made explicit: a non-scalar matrix has a cyclic vector). -/
theorem exists_conj_z (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧
      P * (x : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] * P := by
  -- Fold the coercion into a local abbreviation `X`.
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  have hXX : X * X = -1 := hx
  have hdet : X.det = 1 := Matrix.SpecialLinearGroup.det_coe x
  -- Cayley–Hamilton plus `det X = 1` and `X * X = -1` force `tr X = 0`.
  have htrace : X.trace = 0 := trace_eq_zero_of_sq_eq_neg_one F X hdet hXX
  have htr : X 0 0 + X 1 1 = 0 := by
    rw [Matrix.trace_fin_two] at htrace
    exact htrace
  -- The `(0,0)` entry of `X * X = -1`.
  have h00 : X 0 0 * X 0 0 + X 0 1 * X 1 0 = -1 := by
    have h := congrFun (congrFun hXX 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  obtain ⟨P, hPdet, hP⟩ := conj_z_of_entries F h2 htr h00
  refine ⟨P, hPdet, ?_⟩
  rw [Matrix.eta_fin_two X]
  exact hP

end Work.L2F.Mat2
