import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.CDT.RatFuncDeriv

/-!
# Shared definitions for the `IND` (period-independence) development (area C17y)

This module fixes the vocabulary used by the `y1_periods_indep` development:

* `p1Q a b`, `p0Q a b` — the coefficients `P₁/P₂`, `P₀/P₂` of the order-two operator `M` as
  elements of `ℚ(X)`;
* `Dq` — the numerator `X⁶(X²−1)²` of the adjoint divisor bound;
* `rQ i` — the rational function `y^{i−4}·y'` (so that `Jᵢ' = rQ i · y1`);
* `Lst a b β` — the formal adjoint `(P₂β)'' − (P₁β)' + P₀β`;
* `LBE a b B` — the operator `B'' − p₁B' + (p₀ − p₁')B` of the equation (E);
* `rval f z` — the value at `z` of a rational function, via numerator/denominator.

The relation between the two operators is `LBE B = Lst (B/P₂)` (module `C17y.adjoint_equiv`).
-/

namespace Work.C17y

open Polynomial

noncomputable section

/-- `p₁ = P₁/P₂ ∈ ℚ(X)`. -/
def p1Q (a b : ℚ) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P1x a b)
    / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P2x a b)

/-- `p₀ = P₀/P₂ ∈ ℚ(X)`. -/
def p0Q (a b : ℚ) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P0x a b)
    / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P2x a b)

/-- `X⁶(X²−1)² `: the denominator appearing in the adjoint divisor bound. -/
def Dq : Polynomial ℚ := Polynomial.X ^ 6 * (Polynomial.X ^ 2 - 1) ^ 2

/-- `rᵢ = y^{i−4}·y' ∈ ℚ(X)`. -/
def rQ (i : Fin 6) : RatFunc ℚ :=
  Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ

/-- The formal adjoint of `M`: `L*(β) = (P₂β)'' − (P₁β)' + P₀β`. -/
def Lst (a b : ℚ) (β : RatFunc ℚ) : RatFunc ℚ :=
  Submission.CDT.dRat (Submission.CDT.dRat
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P2x a b) * β))
    - Submission.CDT.dRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P1x a b) * β)
    + algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.P0x a b) * β

/-- The operator of the equation (E): `B ↦ B'' − p₁B' + (p₀ − p₁')B`. -/
def LBE (a b : ℚ) (B : RatFunc ℚ) : RatFunc ℚ :=
  Submission.CDT.dRat (Submission.CDT.dRat B) - p1Q a b * Submission.CDT.dRat B
    + (p0Q a b - Submission.CDT.dRat (p1Q a b)) * B

/-- The value of a rational function at a complex point, read off from its
numerator/denominator representation. -/
def rval (f : RatFunc ℚ) (z : ℂ) : ℂ :=
  f.num.eval₂ (algebraMap ℚ ℂ) z / f.denom.eval₂ (algebraMap ℚ ℂ) z

end

end Work.C17y

namespace Work.C17y

open Polynomial

noncomputable section

/-- The recursion step of the differentiation bookkeeping: from the data `(A,B,C)` of one level it
produces the data of the next level, using the derivation `∂ : f ↦ f'` of `ℚ(X)`, the coefficients
`p₀ = P₀/P₂`, `p₁ = P₁/P₂` of the order-two operator `M`, and the six rational functions
`rQ i = y^{i−4}y'` together with the equation `y1'' = −p₁y1' − p₀y1`. -/
def dstep (a b : ℚ) (A B : RatFunc ℚ) (C : Fin 6 → Polynomial ℚ) :
    (RatFunc ℚ × RatFunc ℚ) × (Fin 6 → Polynomial ℚ) :=
  (⟨Submission.CDT.dRat A - B * p0Q a b
      + ∑ i, (algebraMap (Polynomial ℚ) (RatFunc ℚ) (C i)) * rQ i,
    A + Submission.CDT.dRat B - B * p1Q a b⟩,
   fun i => (C i).derivative)

/-- The `k`-th level data. -/
def lev (a b : ℚ) (A B : RatFunc ℚ) (C : Fin 6 → Polynomial ℚ) :
    ℕ → (RatFunc ℚ × RatFunc ℚ) × (Fin 6 → Polynomial ℚ)
  | 0 => (⟨A, B⟩, C)
  | (k + 1) => dstep a b (lev a b A B C k).1.1 (lev a b A B C k).1.2 (lev a b A B C k).2

@[simp] lemma lev_zero (a b : ℚ) (A B : RatFunc ℚ) (C : Fin 6 → Polynomial ℚ) :
    lev a b A B C 0 = (⟨A, B⟩, C) := rfl

@[simp] lemma lev_succ (a b : ℚ) (A B : RatFunc ℚ) (C : Fin 6 → Polynomial ℚ) (k : ℕ) :
    lev a b A B C (k + 1)
      = dstep a b (lev a b A B C k).1.1 (lev a b A B C k).1.2 (lev a b A B C k).2 := rfl

end

end Work.C17y
