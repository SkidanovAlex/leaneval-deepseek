import Mathlib
import Submission.Work.BMF.kdr_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the Heath–Brown Taylor/Abel reduction

Shared vocabulary for `Work.BMF.exp_sum_taylor_abel_bound_real`: the Taylor polynomial `tayP`
of `f` at the point `n` (in the variable `t`, i.e. `f(n+t)` is expanded) and the remainder
function `betaP t = f (n + t) - tayP t`, whose derivative is the `(k-1)`-st order Taylor
remainder of `f'` at `n`.
-/

namespace Work.BMF

open Finset

attribute [local instance] Classical.propDecidable

/-- The Taylor polynomial of `f` at `n` evaluated at `n + t`, i.e.
`Σ_{i=1}^{k-1} f^{(i)}(n) t^i / i! = Σ_{i ∈ range (k-1)} f^{(i+1)}(n) t^{i+1}/(i+1)!`. -/
noncomputable def tayP (k : ℕ) (f : ℝ → ℝ) (n : ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k - 1),
    iteratedDeriv (i + 1) f n * t ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)

/-- The difference between `f (n + t)` and its Taylor polynomial `tayP`:
`betaP k f n t = f (n + t) - tayP k f n t`. -/
noncomputable def betaP (k : ℕ) (f : ℝ → ℝ) (n : ℝ) : ℝ → ℝ :=
  fun t => f (n + t) - tayP k f n t

@[simp] lemma betaP_apply (k : ℕ) (f : ℝ → ℝ) (n t : ℝ) :
    betaP k f n t = f (n + t) - tayP k f n t := rfl

end Work.BMF
