import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.FtbAux.floquet_core

/-!
# Floquet trace bound at rational frequency

For `α = p/q`, every `E` in the spectrum `Σ_{λ,α}` of the almost Mathieu operator (phase `0`)
satisfies `‖tr A_q(0)‖ ≤ 2`, where `A_q(0) = iterC α λ E q 0` is the transfer matrix over one
period.

The input from Floquet theory is `Work.TMC7Core.FtbAux.floquet_of_genEigen`: the same bound
for a *generalized* eigenvalue `E'` (a polynomially bounded nonzero formal solution of the
eigenvalue equation).  Weak Schnol (`P_Schnol`) says that generalized eigenvalues are dense in
the spectrum, and the Floquet trace is continuous in the energy, so the bound passes to the
limit.  This is the rational-frequency half of the standard "spectrum = set of energies with
`‖tr A_q‖ ≤ 2`" correspondence; it isolates the role of `P_Schnol` in the C7 component.
-/

namespace Work.TMC7Core.Solutions

open Work.TMC7Core

/-- The Floquet trace `E ↦ tr A_q(E)` is continuous in the energy. -/
lemma continuous_trace_iterC (α lam : ℝ) (q : ℕ) :
    Continuous (fun E : ℝ => (iterC α lam (E : ℂ) q 0).trace) :=
  ((continuous_iterC_energy α lam q 0).comp Complex.continuous_ofReal).matrix_trace

/-- **Floquet trace bound at rational frequency.**
For `α = p/q` and `E` in the spectrum `Σ_{λ,α}` of the almost Mathieu operator
(phase `0`), the trace of the `q`-step transfer matrix `A_q(0)` has modulus `≤ 2`.

Indeed, `P_Schnol` produces generalized eigenvalues `E'` arbitrarily close to `E` (generalized
eigenvalues are dense in the spectrum), `floquet_of_genEigen` bounds the trace at each such
`E'`, and the trace depends continuously on the energy, so the set of energies satisfying the
bound is closed and contains `E`. -/
theorem floquet_trace_bound (h1 : P_OpBasics) (h15 : P_Schnol) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (E : ℝ)
    (hE : E ∈ amoSpec ((p : ℝ) / (q : ℝ)) lam) : ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace‖ ≤ 2 := by
  obtain ⟨H, hH, hspec⟩ := hE
  have hcont : Continuous (fun E' : ℝ => ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E' : ℂ) q 0).trace‖) :=
    (continuous_trace_iterC ((p : ℝ) / (q : ℝ)) lam q).norm
  have hclosed : IsClosed {E' : ℝ | ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E' : ℂ) q 0).trace‖ ≤ 2} :=
    isClosed_Iic.preimage hcont
  have hmem : E ∈ closure {E' : ℝ | ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E' : ℂ) q 0).trace‖ ≤ 2} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨E', hE', u, hu⟩ := h15 ((p : ℝ) / (q : ℝ)) lam 0 H hH E hspec ε hε
    exact ⟨E', Work.TMC7Core.FtbAux.floquet_of_genEigen p q hq lam E' u hu,
      by rw [Real.dist_eq, abs_sub_comm]; exact hE'⟩
  rwa [hclosed.closure_eq] at hmem

end Work.TMC7Core.Solutions
