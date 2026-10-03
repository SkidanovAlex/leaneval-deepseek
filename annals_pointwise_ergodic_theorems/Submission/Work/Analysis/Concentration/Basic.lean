/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Fourier.ZMod
import Submission.Commons.MeasureTheory.Function.eLpNorm_count

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concentration estimates for polynomials modulo `q` (Krause–Mirek–Tao, Appendix C)

This file sets up the basic objects of the arithmetic ("concentration"/"level set") part of
B. Krause, M. Mirek and T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. **195** (2022), arXiv:2008.00857.

The paper's Appendix C studies the counting function
`h(y) = #{x ∈ ℤ/Qℤ : P(x) = y}` of a polynomial `P ∈ ℤ[X]` of degree `d ≥ 2` and its
consequences for the arithmetic averaging operator
`A f(y) = (1/Q) ∑_{x ∈ ℤ/Qℤ} f (y - P(x))`.

We work with `ZMod Q` throughout (`ℤ/Qℤ`), with the counting measure; `polyFiberCard P Q y`
is the paper's `h(y)`, `polyLevelSetCard P q N a` is the level set of `P` modulo `q` inside
`{0, …, N-1}`, and `polyShiftAverageZMod P Q f` is the averaging operator `A`.

The main *quantitative* inputs are collected here as predicates so that they can be stated
exactly and instantiated:

* `FiberMaxBound P Q M` — `h(y) ≤ M` for all `y` (the sharp case being `M ≍ Q^{1-1/d}`);
* `FiberLpBound P Q s C` — `∑_y h(y)^s ≤ C^s Q`, i.e. `‖h‖_{L^s} ≤ C Q^{1/s}`
  (Corollary `cor:1` of Appendix C, `‖h‖_{L^s} ≲_{s,P} 1` for `0 < s < d/(d-1)`);
* `FiberWeakType P Q d C` — `#{y : h(y) ≥ λ} ≤ C λ^{-d/(d-1)} Q`
  (Corollary `cor:1`, the weak-type form, Proposition `prop:zero`(iii));
* `PolyImprovingZMod P Q p p' C` — the `ℓ^p → ℓ^{p'}` improving estimate for `A`.

The elementary implications between these (and the elementary instances of the bounds) are
proved in the companion files `Fiber.lean`, `Young.lean`, `WeakType.lean`,
`PrimeUniform.lean`; the single-scale minor arc estimate `improv` of §5 and its reduction
to Peluse's inverse theorem live in `Improv.lean`.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## The reduction of a polynomial modulo `Q` and its fibres -/

/-- The image of `P : ℤ[X]` in `(ℤ/Qℤ)[X]`. -/
def polyMapZMod (P : ℤ[X]) (Q : ℕ) : (ZMod Q)[X] :=
  P.map (Int.castRingHom (ZMod Q))

/-- Evaluation of `P : ℤ[X]` at a point of `ℤ/Qℤ`. -/
def polyEvalZMod (P : ℤ[X]) (Q : ℕ) (x : ZMod Q) : ZMod Q :=
  (polyMapZMod P Q).eval x

@[simp] lemma polyEvalZMod_def (P : ℤ[X]) (Q : ℕ) (x : ZMod Q) :
    polyEvalZMod P Q x = (polyMapZMod P Q).eval x := rfl

/-- Evaluation of `P` at an integer, pushed to `ℤ/Qℤ`: the two agree.  This is the bridge
between the "interval" level sets and the "residue class" fibres. -/
lemma polyEvalZMod_natCast (P : ℤ[X]) (Q : ℕ) (n : ℕ) :
    polyEvalZMod P Q (n : ZMod Q) = ((P.eval (n : ℤ) : ℤ) : ZMod Q) := by
  have h : (n : ZMod Q) = (Int.castRingHom (ZMod Q)) (n : ℤ) := by
    simp [Int.castRingHom]
  rw [polyEvalZMod_def, polyMapZMod, h, Polynomial.eval_map,
    Polynomial.eval₂_at_apply]
  rfl

/-- The fibre counting function `h(y) = #{x ∈ ℤ/Qℤ : P(x) = y}` of Appendix C. -/
def polyFiberCard (P : ℤ[X]) (Q : ℕ) [NeZero Q] (y : ZMod Q) : ℕ :=
  (Finset.univ.filter (fun x : ZMod Q => polyEvalZMod P Q x = y)).card

/-- The level set of `P` modulo `q` inside the interval `{0, 1, …, N-1}`. -/
def polyLevelSetCard (P : ℤ[X]) (q N : ℕ) [NeZero q] (a : ZMod q) : ℕ :=
  ((Finset.range N).filter (fun n : ℕ => polyEvalZMod P q (n : ZMod q) = a)).card

/-- The **normalized** `L^p` "norm" on `ℤ/Qℤ`, with respect to the Haar probability measure
(normalized counting measure on `ℤ/Qℤ`):
`‖f‖_{L^p} = (Q⁻¹ ∑_x ‖f x‖^p)^{1/p}`.

This is the norm used in Section 10 of the paper (`L^p(ℤ/p^jℤ)`, `L^p(𝔾)` for the compact
rings `𝔾` of Example `avg-mult`).  The `L^∞` norm is the usual sup norm `‖f‖` of `ZMod Q → ℂ`. -/
def LpNormZMod (Q : ℕ) [NeZero Q] (p : ℝ) (f : ZMod Q → ℂ) : ℝ :=
  ((Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖f x‖ ^ p) ^ (1 / p)

/-- The polynomial averaging operator on `ℤ/Qℤ`:
`(A f)(y) = (1/Q) ∑_{x ∈ ℤ/Qℤ} f (y - P(x))`.

This is the arithmetic average `A_{ℤ/p^jℤ}^{P(n)}` of Section 10 of the paper (in the
"linear in the second variable" form; the bilinear operator of Section 10 is
`(f,g) ↦ A^{P(n)}(g) · f`). -/
def polyShiftAverageZMod (P : ℤ[X]) (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) : ZMod Q → ℂ :=
  fun y => (Q : ℂ)⁻¹ * ∑ x : ZMod Q, f (y - polyEvalZMod P Q x)

/-- Normalized convolution of two functions on `ℤ/Qℤ` (with respect to the Haar probability
measure): `(u ∗ v)(y) = Q⁻¹ ∑_z u z · v (y - z)`. -/
def convZMod (Q : ℕ) [NeZero Q] (u v : ZMod Q → ℂ) : ZMod Q → ℂ :=
  fun y => (Q : ℂ)⁻¹ * ∑ z : ZMod Q, u z * v (y - z)

/-- The **bilinear** polynomial averaging operator on `ℤ/Qℤ` of Example `avg-mult`:
`A(f,g)(x) = (1/Q) ∑_{y ∈ ℤ/Qℤ} f (x - P₁(y)) g (x - P₂(y))`.

The paper's arithmetic average is the case `P₁ = X`, `P₂ = P`. -/
def polyBilinearAverageZMod (P₁ P₂ : ℤ[X]) (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ) :
    ZMod Q → ℂ :=
  fun x => (Q : ℂ)⁻¹ * ∑ y : ZMod Q,
    f (x - polyEvalZMod P₁ Q y) * g (x - polyEvalZMod P₂ Q y)

/-! ## The concentration bounds -/

/-- **Maximal fibre bound.**  Every fibre of `P` modulo `Q` has at most `M` elements.
This is the `s → ∞` endpoint of the `L^s` bound of Appendix C, Corollary `cor:1`; for
`P` of degree `d` and `Q = p^j` one has the sharp value `M ≍_P Q^{1 - 1/d}`. -/
def FiberMaxBound (P : ℤ[X]) (Q : ℕ) [NeZero Q] (M : ℝ) : Prop :=
  ∀ y : ZMod Q, (polyFiberCard P Q y : ℝ) ≤ M

/-- **`L^s` concentration bound** (Appendix C, Corollary `cor:1`): `‖h‖_{L^s(ℤ/Qℤ)} ≤ C Q^{1/s}`,
i.e. `∑_y h(y)^s ≤ C^s Q`.  The paper proves this for `0 < s < d/(d-1)` with a constant
depending on `P` (and, in the prime-uniform form, uniformly in the prime power `Q`). -/
def FiberLpBound (P : ℤ[X]) (Q : ℕ) [NeZero Q] (s : ℝ) (C : ℝ) : Prop :=
  ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s ≤ C ^ s * Q

/-- **Weak-type concentration bound** (Appendix C, Proposition `prop:zero`(iii) and
Corollary `cor:1`): `#{y : h(y) ≥ λ} ≤ C λ^{-d/(d-1)} Q` for every `λ > 0`. -/
def FiberWeakType (P : ℤ[X]) (Q : ℕ) [NeZero Q] (d : ℝ) (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    ((Finset.univ.filter (fun y : ZMod Q => t ≤ (polyFiberCard P Q y : ℝ))).card : ℝ)
      ≤ C * t ^ (-(d / (d - 1))) * Q

/-- The explicit constant produced by the layer-cake argument converting the weak-type
concentration bound `FiberWeakType` into the `L^s` bound `FiberLpBound` (Appendix C,
Corollary `cor:1`): with `α = d/(d-1)` and `T = max 1 C^{1/α}`,
`C' = (s T^s + s C T^{s-α}/(α - s))^{1/s}`.

It depends only on `d`, `s` and the weak-type constant `C` (in particular not on `Q`). -/
noncomputable def fiberWeakTypeConstant (d s C : ℝ) : ℝ :=
  let α := d / (d - 1)
  let T := max 1 (C ^ (1 / α))
  (s * T ^ s + s * C * T ^ (s - α) / (α - s)) ^ (1 / s)

/-- **`ℓ^p → ℓ^{p'}` improving estimate** for the polynomial averaging operator
`polyShiftAverageZMod P Q`: `‖A f‖_{L^{p'}} ≤ C ‖f‖_{L^p}`, in the normalized norms
`LpNormZMod`.  This is the form in which Section 10 of the paper uses the concentration
estimates: equation (avg-4) is the case `p = 1`, `p' = s < d/(d-1)`, and (avg-2) is the
`p = p' = 2` case with `C ≤ 1`. -/
def PolyImprovingZMod (P : ℤ[X]) (Q : ℕ) [NeZero Q] (p p' : ℝ) (C : ℝ) : Prop :=
  ∀ f : ZMod Q → ℂ, LpNormZMod Q p' (polyShiftAverageZMod P Q f) ≤ C * LpNormZMod Q p f

/-- **Bilinear arithmetic averaging estimate** (the `r > 2` improvement of Section 10). -/
def BilinearAverageLq (P : ℤ[X]) (Q : ℕ) [NeZero Q] (q C : ℝ) : Prop :=
  ∀ f g : ZMod Q → ℂ,
    LpNormZMod Q q (polyBilinearAverageZMod X P Q f g) ≤ C * LpNormZMod Q 2 f * LpNormZMod Q 2 g

end

end Work.Analysis.Concentration
