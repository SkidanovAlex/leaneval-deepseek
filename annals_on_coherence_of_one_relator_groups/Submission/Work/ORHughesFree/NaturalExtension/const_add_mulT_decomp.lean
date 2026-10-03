/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Splitting off the constant term: `q = [q]_0 + t·h`

In the skew Laurent polynomial ring `R[t^{±1};τ] = SkewMonoidAlgebra R (Multiplicative ℤ)`,
the variable `t = skewLaurentT = single (ofAdd 1) 1` is a unit: its inverse is
`single (ofAdd (-1)) 1`.  Consequently *every* element `q` of `R[t^{±1};τ]` can be written as
its constant term plus `t` times something:

  `q = [q]_0 + t · (t⁻¹ · (q - [q]_0))`,   where `[q]_0 = single 1 (coeffElt q 0)`.

In particular no hypothesis on the coefficients of `q` is needed for the algebraic identity; in
the application the hypothesis `∀ k < 0, coeffElt q k = 0` is what makes this the *finite*
decomposition of `q` into non-negative powers of `t` (i.e. it is what guarantees that the `h`
produced lies in `R[t;τ]`).

## Main results

* `skewLaurentT_mul_single_neg_one` : `t * t⁻¹ = 1`;
* `const_add_mulT_decomp` : `q = [q]_0 + t * h` for a suitable `h`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs

universe u

namespace Work.ORHughesFree.NaturalExtension

/-- The inverse of the variable `t` in the skew Laurent polynomial ring, written as a
`SkewMonoidAlgebra.single`: `t⁻¹ = single (ofAdd (-1)) 1`.  The relation `t * t⁻¹ = 1` is
`skewLaurentT_mul_single_neg_one`. -/
noncomputable def skewLaurentTinv {R : Type u} [Ring R] : SkewL R :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1

/-- The variable `t` of `R[t^{±1};τ]` is a unit, with inverse `single (ofAdd (-1)) 1`. -/
theorem skewLaurentT_mul_single_neg_one {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] :
    skewLaurentT * skewLaurentTinv (R := R) = 1 := by
  rw [skewLaurentTinv, skewLaurentT, SkewMonoidAlgebra.single_mul_single]
  simp

/-- Every element `q` of the skew Laurent polynomial ring `R[t^{±1};τ]` is the sum of its
constant term and a multiple of the variable `t`:  `q = [q]_0 + t * h`.

Explicitly one may take `h = t⁻¹ * (q - [q]_0)`, where `t⁻¹ = single (ofAdd (-1)) 1`.  The
hypothesis `hq` (the negative coefficients of `q` vanish) is not needed for this algebraic
decomposition; it is what makes `h` involve only non-negative powers of `t`, so that the
decomposition is the natural one along the degree filtration. -/
theorem const_add_mulT_decomp {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (q : SkewL R) (hq : ∀ k : ℤ, k < 0 → coeffElt q k = 0) : ∃ h : SkewL R, q = SkewMonoidAlgebra.single 1 (coeffElt q 0) + skewLaurentT * h := by
  refine ⟨skewLaurentTinv * (q - SkewMonoidAlgebra.single 1 (coeffElt q 0)), ?_⟩
  rw [← mul_assoc, skewLaurentT_mul_single_neg_one, one_mul]
  abel

end Work.ORHughesFree.NaturalExtension
