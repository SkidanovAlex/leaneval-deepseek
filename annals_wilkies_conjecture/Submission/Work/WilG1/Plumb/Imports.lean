/-
  WilG1 — a helper module collecting the analysis imports needed by the plumbing lemmas
  (differentiability, `deriv`, iterated derivatives) so that delegated statements using them
  can list a workspace module in their `depends_on`.
-/
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Partial

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG1

/-- The fibre of `G` over the parameter `Fin.init z` is not differentiable at the last
coordinate of `z`. -/
def fibBadAt {p : ℕ} (G : (Fin (p + 1) → ℝ) → ℝ) (z : Fin (p + 1) → ℝ) : Prop :=
  ¬ DifferentiableAt ℝ (fun s : ℝ => G (Fin.snoc (Fin.init z) s)) (z (Fin.last p))

/-- The one-variable junk derivative of `f` in the `i`-th coordinate: `0` wherever the
one-dimensional derivative does not exist. -/
def junkPartial {n : ℕ} (i : Fin (n + 1)) (f : (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin (n + 1) → ℝ) : ℝ :=
  deriv (fun t : ℝ => f (Fin.insertNth i t (Fin.removeNth i z))) (z i)

/-- The one-variable junk derivative of `g : ℝ → ℝ`. -/
def junkDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := deriv g x

end Work.WilG1
