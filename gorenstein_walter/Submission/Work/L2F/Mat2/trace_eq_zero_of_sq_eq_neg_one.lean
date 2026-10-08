import Mathlib
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

namespace Work.L2F.Mat2

/-- A `2 × 2` matrix `M` over a field with `det M = 1` and `M * M = -1` has trace `0`.
Proof: Cayley–Hamilton `M * M = tr M • M - det M • 1` (project lemma `sq_eq_trace_smul_sub_det`)
with `M * M = -1`, `det M = 1` gives `tr M • M = 0`; multiplying on the right by `M` gives
`tr M • (M * M) = 0`, i.e. `tr M • (-1) = 0`, and the `(0,0)` entry gives `-tr M = 0`. -/
lemma trace_eq_zero_of_sq_eq_neg_one (F : Type*) [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (h : M * M = -1) : M.trace = 0 := by
  -- Cayley–Hamilton together with `M * M = -1` and `det M = 1` gives `tr M • M = 0`.
  have h1 : M.trace • M = 0 := by
    have hCH := (sq_eq_trace_smul_sub_det F M).symm
    rw [h, hdet] at hCH
    simp only [one_smul] at hCH
    rw [sub_eq_iff_eq_add] at hCH
    simpa using hCH
  -- Multiply on the right by `M`: `tr M • (M * M) = 0`, i.e. `tr M • (-1) = 0`.
  have h2 : M.trace • (M * M) = 0 := by
    have := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N * M) h1
    simpa only [Matrix.smul_mul, Matrix.zero_mul] using this
  rw [h] at h2
  -- The `(0,0)` entry of `tr M • (-1) = 0` is `-tr M = 0`.
  have h3 := congrFun (congrFun h2 0) 0
  simpa using h3

end Work.L2F.Mat2
