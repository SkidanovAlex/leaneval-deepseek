import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower

/-!
# Vocabulary for the Rosser–Iwaniec `λ⁺` identity

`Gp A z D = Σ_{d ∣ P(z)} [rdPlus D d] μ(d) ν(d)` and `Gm A z E` the same with `rdMinus`:
the (weighted) Möbius sums over the upper/lower admissible divisors of `P(z)`.  They are the two
quantities that the Rosser–Iwaniec λ± sieve identities compute in terms of the layer sums `T_n`:

`Gp A z D = VfR A z + Σ_{n odd} T_n(D,z)`,
`Gm A z E = VfR A z - Σ_{n even, n ≥ 2} T_n(E,z)`.

The recursion peeling the largest prime `q < z` is
`Gp A z D = Gp A q D - ν(q) [q³ ≤ D] Gm A q (D/q)`,
`Gm A z E = Gm A q E - ν(q) Gp A q (E/q)`.

* `oddSum A D z M` / `evenSum A D z M` are the truncated sums `Σ_{n < M, n odd/even} T_n(D,z)`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

/-- The weighted Möbius sum over the **upper admissible** divisors of `P(z)`. -/
noncomputable def Gp (A : BoundingSieve) (z D : ℝ) : ℝ :=
  ∑ d ∈ (Pz A z).divisors,
    (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d

/-- The weighted Möbius sum over the **lower admissible** divisors of `P(z)`. -/
noncomputable def Gm (A : BoundingSieve) (z E : ℝ) : ℝ :=
  ∑ d ∈ (Pz A z).divisors,
    (if rdMinus E d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * A.nu d

/-- The truncated sum of the layer sums `T_n(D,z)` over **odd** `n < M`. -/
noncomputable def oddSum (A : BoundingSieve) (D z : ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n), T A n D z


/-- The truncated sum of the layer sums `T_n(D,z)` over the nonzero **even** `n < M`. -/
noncomputable def evenPosSum (A : BoundingSieve) (D z : ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0), T A n D z

/-- The truncated sum of the layer sums `T_n(D,z)` over **even** `n < M`. -/
noncomputable def evenSum (A : BoundingSieve) (D z : ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n), T A n D z

end

end Work.ChenPlan.LinearSieve.RI
