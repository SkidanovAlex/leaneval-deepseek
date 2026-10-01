import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one

/-!
# The uniform bound `L(1, χ) ≪ log q` for non-principal characters

For every modulus `q ≥ 1` and every non-principal Dirichlet character `χ` mod `q` (primitive
or not) the value `L(1, χ)` is bounded by a constant times `log(2q + 2)`:

  `∃ C > 0, ∀ q (χ : DirichletCharacter ℂ q), χ ≠ 1 → ‖L(χ,1)‖ ≤ C · log(2q + 2)`.

This is the classical estimate `L(1,χ) ≪ log q` (Davenport, *Multiplicative Number Theory*,
Ch. 9; it is used throughout Heath-Brown's proof of Linnik's theorem to control the values of
`L`-functions at `s = 1`).

The analytic content is already in the shared library: the Commons module
`Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one` proves, for a
non-principal `χ` mod `N` and every `s` with `Re s ≥ 1`,

  `‖L(χ,s)‖ ≤ log N + log(2 + |Im s|) + 6`,

by combining the absolute convergence of the Dirichlet series on `Re s > 1` with partial
summation (the partial sums of a non-principal character are bounded by the modulus, because
they vanish over complete periods), and then letting `s → 1`.  Evaluating at `s = 1` and
absorbing the additive constants into a multiplicative `log(2q+2)` gives the statement below.
-/

namespace Work.LinnikAreas

/-- **Arithmetic bookkeeping.**  For `q ≥ 1` the additive logarithmic bound
`log q + log 2 + 6` is dominated by `20 · log(2q + 2)`. -/
private lemma log_q_add_log_two_add_six_le (q : ℕ) (hq : 1 ≤ q) :
    Real.log (q : ℝ) + Real.log 2 + 6 ≤ 20 * Real.log (2 * (q : ℝ) + 2) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : q ≠ 0))
  -- `log (2q) = log 2 + log q` and `log (2q) ≤ log (2q+2)`
  have hsplit : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hqpos)
  have hmono : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (q : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  -- `log(2q+2) ≥ log 4 = 2 log 2 > 1`
  have hlog4 : Real.log 4 ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_le_log (by norm_num)
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlog4' : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog2 : (1 : ℝ) < Real.log (2 * (q : ℝ) + 2) := by
    have := Real.log_two_gt_d9
    linarith
  linarith [hsplit, hmono, hlog4, hlog4', hlog2]

/-- **Uniform bound for `L(1,χ)`.**  There is an absolute constant `C > 0` with
`‖L(χ,1)‖ ≤ C · log(2q+2)` for every modulus `q ≥ 1` and every non-principal character
`χ` mod `q`. -/
theorem LFunctionOneBound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ‖DirichletCharacter.LFunction χ (1:ℂ)‖ ≤ C * Real.log (2 * (q:ℝ) + 2) := by
  refine ⟨20, by norm_num, ?_⟩
  intro q _ χ hχ
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  -- the shared-library bound at `s = 1`: `‖L(χ,1)‖ ≤ log q + log 2 + 6`
  have hlib :=
    Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ (1 : ℂ) le_rfl
  have hbound : ‖DirichletCharacter.LFunction χ (1:ℂ)‖ ≤ Real.log (q:ℝ) + Real.log 2 + 6 := by
    simpa using hlib
  exact hbound.trans (log_q_add_log_two_add_six_le q hq)

end Work.LinnikAreas
