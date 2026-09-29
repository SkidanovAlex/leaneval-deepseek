import Mathlib
import Submission.CDT.DerivOrderAt
import Submission.Commons.FieldTheory.Differential.exists_deriv_of_deriv_eq_of_isAlgebraic
import Submission.Commons.FieldTheory.Transcendental.linearIndependent_powers

/-!
# The function-field Lindemann–Weierstrass theorem (logarithmic case)

For a **nonconstant** rational function `f ∈ K(X)` (equivalently `dRat f ≠ 0`), `log f` is
transcendental over `K(X)`.  The algebraic content is a single "no simple pole" obstruction:

* the *logarithmic* derivative `(dRat f)/f` has a **simple** pole at every zero and every pole of
  `f` — `ordAt_dRat_div_self`, the order of vanishing of `(dRat f)/f` there is exactly `-1`;
* whereas `dRat g` **never** has a simple pole — `ordAt_dRat_ne_neg_one`, `ordAt α (dRat g) ≠ -1`
  for every `g` and every `α` (a pole of a derivative is always at least double).

Hence `(dRat f)/f` is not the derivative of any element of `K(X)`.  Combined with the "no new
integration" theorem
(`Commons.FieldTheory.Differential.exists_deriv_of_deriv_eq_of_isAlgebraic`: the derivative of an
algebraic element that lies in the base field is a derivative in the base field), this says that
any element `ℓ` of a differential field extension of `K(X)` with `ℓ' = (dRat f)/f` is
transcendental over `K(X)`, and consequently that the powers `1, ℓ, …, ℓ^{n-1}` are
`K(X)`-linearly independent (`linearIndependent_powers_of_deriv_eq_dRat_div`) — the form in which
the paper (CDT, Lemma `seven`) invokes the function-field Lindemann–Weierstrass theorem.

Over `K = ℂ` the special case `f = 1 - y` is the statement `log(1 - y) ∉ ℂ(y)` used in
`Submission.CDT.FuncFieldTranscendence`.
-/

noncomputable section

namespace Submission.CDT

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Function-field Lindemann–Weierstrass, first form.**  For a nonconstant rational function `f`
(`dRat f ≠ 0`), the logarithmic derivative `(dRat f) / f` is not a derivative in `K(X)`:
`dRat g ≠ (dRat f) / f` for every `g`. -/
theorem not_exists_dRat_eq_dRat_div (f : RatFunc K) (hf : dRat f ≠ 0) :
    ∀ g : RatFunc K, dRat g ≠ dRat f / f := by
  obtain ⟨α, hα⟩ := exists_ordAt_ne_zero_of_dRat_ne_zero f hf
  intro g hg
  have h1 : ordAt α (dRat g) = ordAt α (dRat f / f) := by rw [hg]
  rw [ordAt_dRat_div_self f α hα] at h1
  exact ordAt_dRat_ne_neg_one α g h1

/-- **Function-field Lindemann–Weierstrass, second form.**  In any differential field extension
`L` of `K(X)` whose derivation extends `dRat`, an element `ℓ` with `ℓ' = (dRat f)/f` for a
nonconstant `f` is transcendental over `K(X)`. -/
theorem transcendental_of_deriv_eq_dRat_div {L : Type*} [Field L] [Algebra (RatFunc K) L]
    [Differential (RatFunc K)] (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    [Differential L] [DifferentialAlgebra (RatFunc K) L] (f : RatFunc K) (hf : dRat f ≠ 0)
    (ℓ : L) (hℓ : Differential.deriv ℓ = algebraMap (RatFunc K) L (dRat f / f)) :
    ¬ IsAlgebraic (RatFunc K) ℓ := by
  intro halg
  obtain ⟨g, hg⟩ :=
    Commons.FieldTheory.Differential.exists_deriv_of_deriv_eq_of_isAlgebraic
      (K := RatFunc K) (L := L) hℓ halg
  refine not_exists_dRat_eq_dRat_div f hf g ?_
  rw [← hderiv g]
  exact hg

/-- **Function-field Lindemann–Weierstrass, third form (the shape used by the paper).**  If `ℓ' =
(dRat f)/f` for a nonconstant `f`, then `1, ℓ, ℓ², …, ℓ^{n-1}` are linearly independent over
`K(X)`. -/
theorem linearIndependent_powers_of_deriv_eq_dRat_div {L : Type*} [Field L]
    [Algebra (RatFunc K) L] [Differential (RatFunc K)]
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    [Differential L] [DifferentialAlgebra (RatFunc K) L] (f : RatFunc K) (hf : dRat f ≠ 0)
    (ℓ : L) (hℓ : Differential.deriv ℓ = algebraMap (RatFunc K) L (dRat f / f)) (n : ℕ) :
    LinearIndependent (RatFunc K) (fun i : Fin n => ℓ ^ (i : ℕ)) :=
  Commons.FieldTheory.Transcendental.linearIndependent_powers
    (transcendental_of_deriv_eq_dRat_div hderiv f hf ℓ hℓ) n

end Submission.CDT
