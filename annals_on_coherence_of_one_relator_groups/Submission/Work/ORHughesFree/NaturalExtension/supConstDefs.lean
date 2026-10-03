/-
# Definitions for the "duality" lemma `sup_const_mul_add_sup_const_ann`

For a skew Laurent polynomial ring `S = R[t^{±1};τ] = SkewL R` with `R` von Neumann regular,
a `τ`-compatible Sylvester rank function `rk` on `R`, and `p ∈ S` with non-negative
coefficients (i.e. `p ∈ R[t;τ]`), we consider

* `C0set p` : the set of constant terms of *polynomial* left multiples of `p`;
* `C1set p` : the set of constant terms of *polynomial* left annihilators of `p`.

The main statement is that there are `c₀ ∈ C0set p`, `c₁ ∈ C1set p` with
`rk c₀ + rk c₁ ≥ 1 - ε`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The set of constant terms of polynomial left multiples of `p = ∑ p_k t^k`. -/
def C0set (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R) : Set R :=
  {c : R | ∃ q q' : SkewL R, q = q' * p ∧ (∀ k : ℤ, k < 0 → coeffElt q k = 0) ∧ coeffElt q 0 = c}

/-- The set of constant terms of polynomial left annihilators of `p`. -/
def C1set (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (p : SkewL R) : Set R :=
  {c : R | ∃ q'' : SkewL R, q'' * p = 0 ∧ (∀ k : ℤ, k < 0 → coeffElt q'' k = 0) ∧
    coeffElt q'' 0 = c}

end Work.ORHughesFree.NaturalExtension
