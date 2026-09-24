import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.LinearSieve.FrameworkR

/-!
# The Rosser–Iwaniec λ± weights and the `T_n` sums

This file sets up the vocabulary for the **Rosser–Iwaniec** (`λ±`) form of the linear sieve,
following Nathanson, *Additive Number Theory: the classical bases*, Chapter 9 (Theorem 9.3,
Lemma 9.3, Lemma 9.8, Theorem 9.5) and its explicit versions (Bordignon–Johnston–Starichkova,
arXiv:2207.09452, §2.4; arXiv:2007.08774, §3).

The point of the `λ±` formulation is that it uses the sieve axiom **only at the top limit `z`**:
all products `V(p)/V(z)` are relative to `z`.  (The Jurkat–Richert "validity iteration" would
require the axiom at every sub-limit, which `IsLinear` — a single-limit axiom — does not give.)

* `rdPlus D d` / `rdMinus D d` : the Rosser–Iwaniec support conditions: `d` is *upper-admissible*
  when every divisor `e ∣ d` with `ω(e)` **odd** satisfies `e · (minFac e)² ≤ D`; *lower-admissible*
  when this holds for every `e ∣ d`, `e ≠ 1`, with `ω(e)` **even**.  (These are the standard
  "delay" conditions `p_1⋯p_{l−1}p_l³ ≤ D` for odd, resp. even, `l`, rewritten divisor-wise:
  for a divisor `e = p_1⋯p_l` the condition is `e·p_l² ≤ D` and `p_l = minFac e`.)
* `lamPlus P D d = μ(d)` on the upper-admissible divisors of `P`, `0` elsewhere;
  `lamMinus P D d = μ(d)` on the lower-admissible divisors of `P`.
* `IsLowerMoebius μ⁻` : `μ⁻ ∗ 1 ≤ ε` (the lower analogue of Mathlib's `IsUpperMoebius`).
* `T n D z = T_n(D,z)` : the Rosser–Iwaniec layer sums
  `T_n(D,z) = Σ_{y_n ≤ p_n < ⋯ < p_1 < z,  p_m < y_m (m<n, m≡n mod 2)} ν(p_1⋯p_n) V(p_n)`,
  defined here by the recursion that the proofs use,
  `T_0 = V(z)`, `T_{n+1}(D,z) = Σ_p ν(p) T_n(D/p, p)` with the outer condition.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

noncomputable section

open Classical

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

/-- A sequence of coefficients is **lower Moebius on the divisors of `P`** if `μ⁻ ∗ ζ ≤ ε` there:
the lower analogue of `BoundingSieve.IsUpperMoebius`, restricted to the divisors of `P`
(which is all the summation lemma needs, since it is applied to `gcd(n,P)`). -/
def IsLowerMoebiusOn (P : ℕ) (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∣ P → ∑ d ∈ n.divisors, muMinus d ≤ (if n = 1 then (1 : ℝ) else 0)

/-- `P(z) = ∏_{p ∣ P, p < z} p`: the product of the primes of the sieve problem below the limit
`z`.  When every prime of `P` is `< z` this is `P` itself. -/
noncomputable def Pz (A : BoundingSieve) (z : ℝ) : ℕ :=
  ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p

/-- The outer condition on the largest prime `p_1` in the layer `T_{n+1}`: for `n+1 = 1` the
"last index" condition `y_1 < p_1`; for odd `n+1 ≥ 3` the "first index" condition `y_1 > p_1`;
for even `n+1` no condition. -/
def Tcond (n : ℕ) (D : ℝ) (p : ℕ) : Prop :=
  (n = 1 → D < (p : ℝ) ^ 3) ∧ (2 ≤ n → Odd n → (p : ℝ) ^ 3 ≤ D)

/-- **The Rosser–Iwaniec layer sums** `T_n(D,z)`, defined by the recursion
`T_0 = V(z)`, `T_{n+1}(D,z) = Σ_{p ∣ P, p < z} [Tcond (n+1) D p] · ν(p) · T_n(D/p, p)`. -/
noncomputable def T (A : BoundingSieve) : ℕ → ℝ → ℝ → ℝ
  | 0, _, z => VfR A z
  | (n + 1), D, z =>
      ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z ∧ Tcond (n + 1) D p),
        A.nu p * T A n (D / (p : ℝ)) (p : ℝ)

end

end Work.ChenPlan.LinearSieve
