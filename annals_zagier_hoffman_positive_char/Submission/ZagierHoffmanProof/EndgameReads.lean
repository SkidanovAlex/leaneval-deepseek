import Submission.ZagierHoffmanProof.CoeffTwoTerms

/-!
# The level-`0` reads of the two-term endgame

The corrected identity of `Submission/PLAN.md` §«SESSION 354» §«continued 28» is

  `P · σ(δ₁) = P · W^w · δ₁ + W^w · (-A₂L^q + A₁P² + A₁(w-q)·P·L^q)`,   `W = X - C(θ^q)`,

with every object in `ambA F 0[X]`.  A "read" is its `θ`-coefficient at degree `j ∈ {0, q, 2q}`, taken
coefficientwise in `X`.

This file holds the reads, one at a time.  All the machinery is in place: `coeffNu_mul_two_terms`
(`CoeffTwoTerms.lean`) for `W^w` and `L^q`, `coeffNu_polyTwist_coeff` for `σ(δ₁)`,
`eq_three_terms_of_support` for `δ₁`, and `coeffNu_coeff_mul_of_ambF` for the `θ`-constant `P`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★ **THE FIRST READ** (§«continued 28»): the `θ^0`-coefficient of `P · σ(δ₁)`, coefficientwise in
`X`.  Since `P` is a `θ`-constant and `σ(δ₁) = polyTwist 1 δ₁`, this is the sum
`∑_{a+b=n} P_a · (θ^0-coefficient of δ₁ at X-degree b)` — i.e. the left side of the identity, ready to
be matched against `P·W^w·δ₁ + W^w·(-A₂L^q + A₁P² + A₁(w-q)·P·L^q)`'s `θ^0`-coefficient. -/
lemma coeffNu_zero_coeff_polyTwist_mul_ambF {P D : Polynomial (Ambient F)}
    (hP : ∀ n, P.coeff n ∈ ambF F) (hD : ∀ n, D.coeff n ∈ ambA F 0) (n : ℕ) :
    coeffNu F 0 0 ((P * polyTwist (q := Nat.card F) 1 D).coeff n)
      = ∑ b ∈ Finset.HasAntidiagonal.antidiagonal n,
          P.coeff b.1 * coeffNu F 0 0 (D.coeff b.2) := by
  have hσ : ∀ m, (polyTwist (q := Nat.card F) 1 D).coeff m ∈ ambA F 0 := by
    intro m
    rw [polyTwist_one_coeff]
    exact ambA_pow_card_mem F (hD m)
  rw [coeffNu_coeff_mul_of_ambF F hP hσ 0 n]
  exact Finset.sum_congr rfl fun b _ =>
    congrArg (fun z => P.coeff b.1 * z)
      (coeffNu_polyTwist_coeff F hD 0 b.2)

end ZagierHoffmanPositiveChar
