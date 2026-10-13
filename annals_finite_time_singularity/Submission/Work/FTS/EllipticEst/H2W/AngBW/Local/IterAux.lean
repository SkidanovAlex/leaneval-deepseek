/-
Temporary local support module (see `Local/slice5_vweight_le.lean`).

Two elementary calculus facts that the upstream module
`Submission/Work/FTS/EllipticEst/remov/slice5_vweight_le.lean` obtains from
`Submission.Work.FTS.EllipticEst.remov.DthIter_expansion`; that module's import closure is
currently broken by work in progress elsewhere in the workspace, so they are reproduced here
verbatim (same names) from `remov/DthIter_expansion.lean` lines 53--90.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- The derivative of a function that is `C^{n+1}` at a point is `C^n` at that point. -/
theorem contDiffAt_deriv_of_succ {g : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) g x) :
    ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (deriv g) x :=
  h.derivWithin (m := ((n : ℕ) : WithTop ℕ∞)) (by push_cast; simp)

/-- Iterated derivatives lower the order of differentiability. -/
theorem contDiffAt_iteratedDeriv_of_add {φ : ℝ → ℝ} {θ : ℝ} :
    ∀ (k M : ℕ), ContDiffAt ℝ (((M + k : ℕ)) : WithTop ℕ∞) φ θ →
      ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) (iteratedDeriv k φ) θ := by
  intro k
  induction k with
  | zero => intro M h; simpa using h
  | succ k ih =>
      intro M h
      rw [iteratedDeriv_succ]
      have hM : ContDiffAt ℝ (((M + 1 + k : ℕ)) : WithTop ℕ∞) φ θ := by
        rw [show M + 1 + k = M + (k + 1) by omega]
        exact h
      exact contDiffAt_deriv_of_succ (n := M) (ih (M + 1) hM)

/-- If `φ` is `C^N` at `θ` then its `k`-th iterated derivative is `C^{N-k}` at `θ`. -/
theorem contDiffAt_iteratedDeriv_of_le {φ : ℝ → ℝ} {θ : ℝ} {k N : ℕ} (hk : k ≤ N)
    (h : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) φ θ) :
    ContDiffAt ℝ (((N - k : ℕ)) : WithTop ℕ∞) (iteratedDeriv k φ) θ := by
  have h' : ContDiffAt ℝ ((((N - k) + k : ℕ)) : WithTop ℕ∞) φ θ := by
    rwa [Nat.sub_add_cancel hk]
  exact contDiffAt_iteratedDeriv_of_add k (N - k) h'

/-- If `φ` is `C^N` at `θ` with `k + 1 ≤ N`, its `k`-th iterated derivative is differentiable
at `θ`. -/
theorem differentiableAt_iteratedDeriv_of_le {φ : ℝ → ℝ} {θ : ℝ} {k N : ℕ}
    (h : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) φ θ) (hk : k + 1 ≤ N) :
    DifferentiableAt ℝ (iteratedDeriv k φ) θ := by
  have h1 := contDiffAt_iteratedDeriv_of_le (Nat.le_of_succ_le hk) h
  have hne : (((N - k : ℕ)) : WithTop ℕ∞) ≠ 0 := by
    intro hzero
    have : N - k = 0 := by exact_mod_cast hzero
    omega
  exact h1.differentiableAt hne

end Work.FTS.EllipticEst
