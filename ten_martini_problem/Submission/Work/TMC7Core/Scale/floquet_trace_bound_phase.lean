import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.FtbAux.floquet_core
import Submission.Work.TMC7Core.Solutions.block_transfer
import Submission.Work.TMC7Core.Solutions.iterC_mulVec_solution
import Submission.Work.TMC7Core.Scale.floquet_phase_aux
import Submission.Work.TMC7Core.Scale.floquet_of_genEigen_phase

/-!
# Floquet trace bound at rational frequency, arbitrary phase

For `α = p/q`, every energy `E` in the spectrum of the almost Mathieu operator at *phase* `θ`
satisfies `‖tr A_q(θ)‖ ≤ 2`, where `A_q(θ) = iterC α λ E q θ = S(θ+(q-1)α)⋯S(θ)` is the
transfer matrix over one period.

The Floquet-theory input is `Work.TMC7Core.Scale.floquet_of_genEigen_phase`, the phase-`θ`
version of `Work.TMC7Core.Solutions.floquet_of_genEigen`: a *generalized* eigenvalue `E'`
(a polynomially bounded nonzero formal solution) already forces `‖tr A_q(θ)‖ ≤ 2`.
Weak Schnol (`P_Schnol`) says generalized eigenvalues are dense in the spectrum, and the
Floquet trace is continuous in the energy, so the bound passes to the spectral point `E`.
(Compare `Work.TMC7Core.Solutions.floquet_trace_bound`, the phase-`0` case.)
-/

namespace Work.TMC7Core.Scale

open Work.TMC7Core

/-- The Floquet trace `E ↦ tr A_q(θ)` is continuous in the energy. -/
lemma continuous_trace_iterC_phase (α lam θ : ℝ) (q : ℕ) :
    Continuous (fun E : ℝ => (iterC α lam (E : ℂ) q θ).trace) :=
  ((continuous_iterC_energy α lam q θ).comp Complex.continuous_ofReal).matrix_trace

theorem floquet_trace_bound_phase (h1 : Work.TMC7Core.P_OpBasics) (h15 : Work.TMC7Core.P_Schnol)
    (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam θ E : ℝ)
    (H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)
    (hH : LeanEval.Analysis.TenMartini.IsAlmostMathieuOperator ((p : ℝ) / (q : ℝ)) lam θ H)
    (hE : (E : ℂ) ∈ spectrum ℂ H) :
    ‖(Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace‖ ≤ 2 := by
  have hcont : Continuous (fun E' : ℝ => ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E' : ℂ) q θ).trace‖) :=
    (continuous_trace_iterC_phase ((p : ℝ) / (q : ℝ)) lam θ q).norm
  have hclosed : IsClosed {E' : ℝ | ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E' : ℂ) q θ).trace‖ ≤ 2} :=
    isClosed_Iic.preimage hcont
  have hmem : E ∈ closure {E' : ℝ | ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E' : ℂ) q θ).trace‖ ≤ 2} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨E', hE', u, hu⟩ := h15 ((p : ℝ) / (q : ℝ)) lam θ H hH E hE ε hε
    exact ⟨E', floquet_of_genEigen_phase p q hq lam θ E' u hu,
      by rw [Real.dist_eq, abs_sub_comm]; exact hE'⟩
  rwa [hclosed.closure_eq] at hmem

end Work.TMC7Core.Scale
