/-
# `Work.FIChain.Rossers` — the Rosser–Iwaniec `λ±` weights (local, Mathlib-only copy)

These are the definitions of `Submission.Work.ChenPlan.LinearSieve.RI.basic` (the Chen workspace's
Rosser–Iwaniec linear sieve, copied into this workspace by the project lead), transcribed here with
Mathlib-only imports so that they can be used WITHOUT the Chen closure (whose
`Submission.Chen.Interface` imports `ChallengeDeps`, a module that does not exist in this
workspace, so the whole `Submission.Work.ChenPlan.*` closure currently fails to build here).

* `rdPlus D d`: `d` is *upper-admissible* for level `D` when every divisor `e ∣ d` with `ω(e)` odd
  satisfies `e · (minFac e)² ≤ D` (i.e. `p₁⋯p_{l-1}p_l³ ≤ D` for odd `l`, divisor-wise);
* `rdMinus D d`: the lower-admissibility condition (every `e ≠ 1` with `ω(e)` even).
* `lamPlus P D d = μ(d)` on the upper-admissible divisors of `P`, `0` elsewhere;
  `lamMinus P D d = μ(d)` on the lower-admissible divisors of `P`.

The two facts the FI endgame needs about `lamPlus` — that it is an **upper Möbius function** on the
divisors of `P` (i.e. `ρ n = Σ_{d ∣ n} λ⁺(d) ≥ 0`, the conjunct the Selberg weight cannot supply)
and that its support is `< D` — are stated as the delegated lemmas
`Work.FIChain.lamPlus_upper_moebius` and `Work.FIChain.lamPlus_support_lt`.
-/
import Mathlib

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.FIChain

attribute [local instance] Classical.propDecidable

/-- **Rosser–Iwaniec upper support condition.**  Every divisor `e` of `d` with an odd number of
prime factors satisfies `e · (minFac e)^2 ≤ D`. -/
def rdPlus (D : ℝ) (d : ℕ) : Prop :=
  ∀ e ∈ d.divisors, Odd e.primeFactors.card → (e : ℝ) * (e.minFac : ℝ) ^ 2 ≤ D

/-- **Rosser–Iwaniec lower support condition.**  Every divisor `e ≠ 1` of `d` with an even number
of prime factors satisfies `e · (minFac e)^2 ≤ D`. -/
def rdMinus (D : ℝ) (d : ℕ) : Prop :=
  ∀ e ∈ d.divisors, Even e.primeFactors.card → e ≠ 1 → (e : ℝ) * (e.minFac : ℝ) ^ 2 ≤ D

/-- The Rosser–Iwaniec **upper-bound weight** `λ⁺(d) = μ(d)` if `d ∣ P` is upper-admissible,
`0` otherwise. -/
noncomputable def lamPlus (P : ℕ) (D : ℝ) (d : ℕ) : ℝ :=
  if d ∣ P ∧ rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

/-- The Rosser–Iwaniec **lower-bound weight** `λ⁻(d) = μ(d)` if `d ∣ P` is lower-admissible,
`0` otherwise. -/
noncomputable def lamMinus (P : ℕ) (D : ℝ) (d : ℕ) : ℝ :=
  if d ∣ P ∧ rdMinus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

end Work.FIChain
