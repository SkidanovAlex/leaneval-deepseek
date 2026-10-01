import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Submission.Commons.NumberTheory.DirichletCharacter.prefix_periodic

open scoped BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- A partial sum `∑_{n < M} χ(n)` depends on `M` only through `M % N`:
it equals the partial sum over the shorter range `0 ≤ n < M % N`. -/
private lemma partial_sum_mod {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (M : ℕ) :
    (∑ n ∈ Finset.range M, (χ (n : ZMod N) : ℂ)) =
      ∑ n ∈ Finset.range (M % N), (χ (n : ZMod N) : ℂ) := by
  classical
  have hM : M = (M / N) * N + M % N := by
    simpa [mul_comm] using (Nat.div_add_mod M N).symm
  have hind : ∀ q : ℕ,
      (∑ n ∈ Finset.range (q * N + M % N), (χ (n : ZMod N) : ℂ)) =
        ∑ n ∈ Finset.range (M % N), (χ (n : ZMod N) : ℂ) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have harg : (q + 1) * N + M % N = q * N + M % N + N := by ring
        rw [harg]
        rw [prefix_periodic χ hχ (q * N + M % N)]
        exact ih
  conv_lhs => rw [hM]
  exact hind (M / N)

/-- Partial sums of a nontrivial Dirichlet character over `0 ≤ n < M` are uniformly
bounded by the conductor: `‖∑_{n < M} χ(n)‖ ≤ N` for every `M`. -/
theorem partial_sum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (M : ℕ) : ‖∑ n ∈ Finset.range M, (χ (n : ZMod N) : ℂ)‖ ≤ (N : ℝ) := by
  rw [partial_sum_mod χ hχ M]
  have hr : M % N < N := Nat.mod_lt M (Nat.pos_of_ne_zero (NeZero.ne N))
  calc
    ‖∑ t ∈ Finset.range (M % N), (χ (t : ZMod N) : ℂ)‖ ≤
        ∑ t ∈ Finset.range (M % N), ‖(χ (t : ZMod N) : ℂ)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.range (M % N), (1 : ℝ) := by
      exact Finset.sum_le_sum (fun t _ => (DirichletCharacter.norm_le_one χ (t : ZMod N)))
    _ = (M % N : ℕ) := by simp
    _ ≤ (N : ℝ) := by exact_mod_cast (Nat.le_of_lt hr)

end Commons.NumberTheory.DirichletCharacter