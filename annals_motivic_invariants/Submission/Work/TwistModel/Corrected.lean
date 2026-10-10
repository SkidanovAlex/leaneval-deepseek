/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TwistModel
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TwistModel.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The corrected rational-divisor predicate

`Work.Arithmetic.HasRatDivisorOfDegree` used the support condition `Order.coheight x = 0`, which on
a scheme selects the **generic points of the irreducible components** rather than the closed points
its docstring asks for; see `Work.TwistModel.Defect` for the analysis and the counterexample
`𝔸¹_𝕜` (`Work.TwistModel.not_hasRatDivisorOfDegree_one_affineLine`, now stated about the named
pre-fix predicate `Work.ArithFix.HasRatDivisorOfDegreeCoheight`).  The corrected predicate,
matching the docstring and Clark–Lacy's definition of the *index* of a curve, is
`HasRatDivisorOfDegreeClosed` below: the support consists of **closed** points
(`IsClosed ({x} : Set C)`, equivalently `Order.height x = 0`).

**The repair has been landed** (`Submission/Work/ArithFix`): the arithmetic predicate now satisfies
`Work.ArithFix.hasRatDivisorOfDegree_iff_height`, so `HasRatDivisorOfDegreeClosed` is not a
replacement for it but the same predicate in a different spelling
(`Work.ArithFix.predicateAgrees`), and the corrected theory below is the theory of the arithmetic
area's predicate.

With this predicate the theory is well behaved: a `𝕜`-rational point gives a `𝕜`-rational divisor of
degree `1` (`hasRatDivisorOfDegreeClosed_one_of_hasRatPoint`), degrees are additive
(`HasRatDivisorOfDegreeClosed.add`, `..._mul_five`), `ℙ¹_𝕜` carries rational divisors of every
degree, and every structure that carries the predicate becomes satisfiable — in particular the twist
models below are non-empty in the trivial-class case (`nonempty_twistCurveModelClosed_of_hasPoint`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The corrected `𝕜`-rational divisor of degree `n`**: a `ℤ`-linear combination of *closed*
points of `C` whose total residue degree is `n`.  This is the notion the docstring of
`Work.Arithmetic.HasRatDivisorOfDegree` describes (and Clark–Lacy's "degree of a `𝕜`-rational
zero-cycle"); the parent definition uses `Order.coheight x = 0`, which selects the generic points
of the components instead (`Work.TwistModel.Defect`). -/
def HasRatDivisorOfDegreeClosed (𝕜 : Type) [Field 𝕜] (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] (n : ℕ) : Prop :=
  ∃ D : C →₀ ℤ, (∀ x ∈ D.support, IsClosed ({x} : Set C)) ∧
    D.sum (fun x m => m * (Work.Arithmetic.resDeg 𝕜 x : ℤ)) = (n : ℤ)

/-- The same predicate with the support condition written as `Order.height x = 0`, the minimal
textual change to `Work.Arithmetic.HasRatDivisorOfDegree`.  On a scheme `Order.height x = 0` is
equivalent to `IsClosed {x}` (`AlgebraicGeometry.Scheme.height_of_isClosed` and the `T0` property of
schemes). -/
def HasRatDivisorOfDegreeHeight (𝕜 : Type) [Field 𝕜] (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] (n : ℕ) : Prop :=
  ∃ D : C →₀ ℤ, (∀ x ∈ D.support, Order.height x = 0) ∧
    D.sum (fun x m => m * (Work.Arithmetic.resDeg 𝕜 x : ℤ)) = (n : ℤ)

/-- The corrected predicate is not vacuous: the empty divisor has degree `0`. -/
theorem hasRatDivisorOfDegreeClosed_zero (𝕜 : Type) [Field 𝕜] (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : HasRatDivisorOfDegreeClosed 𝕜 C 0 := by
  refine ⟨0, ?_, ?_⟩
  · intro x hx
    simp at hx
  · simp

/-- The closed-point form implies the `Order.height = 0` form: a closed point has `Order.height 0`
(`AlgebraicGeometry.Scheme.height_of_isClosed`).  So the minimal textual fix `coheight` → `height` in
`Work.Arithmetic.HasRatDivisorOfDegree` gives a predicate implied by the closed-point one. -/
theorem HasRatDivisorOfDegreeClosed.toHeight {C : Scheme} [C.Over (Spec (CommRingCat.of 𝕜))]
    {n : ℕ} (h : HasRatDivisorOfDegreeClosed 𝕜 C n) : HasRatDivisorOfDegreeHeight 𝕜 C n := by
  obtain ⟨D, hsupp, hsum⟩ := h
  exact ⟨D, fun x hx => AlgebraicGeometry.Scheme.height_of_isClosed (hsupp x hx), hsum⟩

/-- **Degrees of corrected rational divisors are additive.**  (Same proof as
`Work.Arithmetic.HasRatDivisorOfDegree.add`: the support of a sum is contained in the union of the
supports.) -/
theorem HasRatDivisorOfDegreeClosed.add {C : Scheme} [C.Over (Spec (CommRingCat.of 𝕜))] {m n : ℕ}
    (h : HasRatDivisorOfDegreeClosed 𝕜 C m) (h' : HasRatDivisorOfDegreeClosed 𝕜 C n) :
    HasRatDivisorOfDegreeClosed 𝕜 C (m + n) := by
  obtain ⟨D, hD, hdeg⟩ := h
  obtain ⟨D', hD', hdeg'⟩ := h'
  refine ⟨D + D', ?_, ?_⟩
  · intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rcases eq_or_ne (D x) 0 with h0 | h0
    · rw [Finsupp.add_apply, h0, zero_add] at hx
      exact hD' x (Finsupp.mem_support_iff.mpr hx)
    · exact hD x (Finsupp.mem_support_iff.mpr h0)
  · rw [Finsupp.sum_add_index']
    · rw [hdeg, hdeg']
      push_cast
      first | refl_ring1 | ring
    · intro a
      simp
    · intro a b₁ b₂
      first | refl_ring1 | ring

/-- A corrected rational divisor of degree `5` gives corrected rational divisors of all degrees
divisible by `5`. -/
theorem hasRatDivisorOfDegreeClosed_mul_five {C : Scheme} [C.Over (Spec (CommRingCat.of 𝕜))]
    (h5 : HasRatDivisorOfDegreeClosed 𝕜 C 5) (m : ℕ) :
    HasRatDivisorOfDegreeClosed 𝕜 C (5 * m) := by
  induction m with
  | zero => simpa using hasRatDivisorOfDegreeClosed_zero 𝕜 C
  | succ k ih =>
    have h : 5 * (k + 1) = 5 * k + 5 := by ring
    rw [h]
    exact ih.add h5

end

end Work.TwistModel
