/-
# TMC14Core: `blochDet`

`det (z - blochMat p q lam θ k) = trAq p q lam z θ - 2 cos (2 π k)`.

The proof passes to the general cyclic matrix `cycMat q d t` (diagonal `d`, twist `t`) and
the shooting matrix `smMat q d t` of `Submission/Work/TMC14Core/cycSetup.lean`:

  `det (smMat q d t) = det (cycMat q d t)`              (`Work.TMC14Core.smMat_det`)
  `det (smMat q d t) = tr (transProd d q) - (t + t⁻¹)`  (`Work.TMC14Core.smMat_trace`)

Specialising `d i = z - 2λ cos 2π(θ + i p/q)` and `t = e^{2πik}` identifies `cycMat` with
`z - blochMat` (`cycMat_bloch`) and `transProd` with `iterC` (`iterC_eq_transProd`).
-/
import Mathlib
import Submission.Work.TMC14Core.cycSetup
import Submission.Work.TMC14Core.smMat_det
import Submission.Work.TMC14Core.smMat_trace

open LeanEval.Analysis.TenMartini
noncomputable section

namespace Work.TMC14Core

/-- `trAq` is the trace of `iterC`. -/
theorem trAq_eq_trace (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) :
    trAq p q lam z θ = (iterC ((p : ℝ) / (q : ℝ)) lam z q θ).trace := by
  rw [trAq, Matrix.trace_fin_two]

/-- `dOf` written in the shape used by `iterC_eq_transProd`. -/
theorem dOf_eq (p : ℤ) (q : ℕ) (lam θ : ℝ) (z : ℂ) :
    dOf p q lam θ z
      = fun (i : ℕ) => z - (((2*lam*Real.cos (2*Real.pi*(θ + (i:ℝ)*((p:ℝ)/(q:ℝ))))) : ℝ) : ℂ) := by
  funext i
  simp only [dOf]
  congr 2
  ring_nf

theorem blochDet (p : ℤ) (q : ℕ) (lam θ k : ℝ) (z : ℂ) (hq : 0 < q) :
    (z • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMat p q lam θ k).det
      = trAq p q lam z θ - 2 * Real.cos (2 * Real.pi * k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hq)
  simp only [Nat.succ_eq_add_one]
  rw [cycMat_bloch p (m+1) lam θ k z]
  rw [← smMat_det m (dOf p (m+1) lam θ z) (wBeta k)]
  rw [smMat_trace m (dOf p (m+1) lam θ z) (wBeta k) (Complex.exp_ne_zero _)]
  rw [wBeta_add_inv k]
  have hal : (transProd (dOf p (m+1) lam θ z) (m+1)).trace
      = trAq p (m+1) lam z θ := by
    rw [dOf_eq p (m+1) lam θ z, trAq_eq_trace]
    rw [← iterC_eq_transProd ((p:ℝ)/(((m+1 : ℕ) : ℝ))) lam θ z (m+1)]
  rw [hal]
  push_cast
  ring

end Work.TMC14Core
