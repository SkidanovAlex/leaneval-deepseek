import Mathlib
import Submission.Work.Diff.MP.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

/-- Local existence for the autonomous ODE `α' = Q (α)` on the real normed space
`Submission.Diff.Alg.Curv4 n` (finite dimensional, hence complete), on an interval around `0`.
Intended proof: `unfold Submission.Diff.Alg.Q; fun_prop` proves
`ContDiff ℝ ⊤ (Q : Curv4 n → Curv4 n)`, hence `ContDiffAt ℝ 1 Q S`, and Mathlib's
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`
(`Mathlib.Analysis.ODE.ExistUnique`) with `f := Q`, `x₀ := S`, `t₀ := 0` produces `α` with
`α 0 = S` and `HasDerivAt α (Q (α t)) t` on `Ioo (-ε) ε`. -/
theorem exists_local_solution_Q (n : ℕ) (S : Submission.Diff.Alg.Curv4 n) :
    ∃ ε > 0, ∃ α : ℝ → Submission.Diff.Alg.Curv4 n, α 0 = S ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (Submission.Diff.Alg.Q (α t)) t := by
  -- Hamilton's reaction term is a quadratic polynomial in the components of `R`, hence `C¹`.
  have hQ : ContDiff ℝ 1
      (Submission.Diff.Alg.Q : Submission.Diff.Alg.Curv4 n → Submission.Diff.Alg.Curv4 n) := by
    unfold Submission.Diff.Alg.Q
    fun_prop
  -- Picard–Lindelöf at the point `S`, starting time `0`.
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (f := Submission.Diff.Alg.Q) (x₀ := S) hQ.contDiffAt 0
  exact ⟨ε, hε, α, hα0, fun t ht => hα t (by simpa using ht)⟩

end Work.Diff.MP
