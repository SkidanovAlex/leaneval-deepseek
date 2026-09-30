/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area GenusZero
-/
import Submission.Work.GenusZero.Basic
import Submission.Work.GenusZero.PointDiv
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GenusZero: Riemann–Roch at genus zero

On a curve of genus zero every divisor of degree zero is principal.  This is the whole
divisor-theoretic content of the genus-zero case of the Jacobian challenge, and it is what
replaces the Brill–Noether input used in genus `≥ 1`: there is no need to produce a rational
function with prescribed poles and zeros of large degree.

The proof is Riemann–Roch applied to `-D`: since `deg (-D) = 0` and `genus C = 0`, the equation

  `l (-D) - i (-D) = deg (-D) + 1 - genus C = 1`

together with `i (-D) ≥ 0` shows `l (-D) ≥ 1`, so `L (-D)` contains a nonzero function `h`.
By `mem_L_iff` the divisor `div h - D` is effective, and by `Order.deg_div` and `deg D = 0`
its degree is zero, so it vanishes (`Divisor.deg_eq_zero_iff`).

## Main results

* `Work.GenusZero.principal_of_deg_zero`
* `Work.GenusZero.linEquiv_of_deg_eq_zero`
-/

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.GenusZero

variable {k : Type u} [Field k]

/-- **Riemann–Roch at genus zero**: on a curve of genus `0`, every divisor of degree `0` is
the divisor of a nonzero rational function. -/
theorem principal_of_deg_zero (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (D : C.Div) (hD : C.deg D = 0) :
    ∃ h : C.functionField, h ≠ 0 ∧ C.div h = D := by
  have hrr := RiemannRoch.Curve.riemannRoch C (-D)
  have hdeg : C.deg (-D) = 0 := by rw [CurveBasics.Curve.deg_neg, hD, neg_zero]
  have h1 : (1 : ℤ) ≤ (CurveBasics.Curve.l C (-D) : ℤ) := by
    have h2 : (0 : ℤ) ≤ (RiemannRoch.Curve.i C (-D) : ℤ) := Int.natCast_nonneg _
    linarith
  have hne : CurveBasics.Curve.L C (-D) ≠ ⊥ := by
    intro hbot
    have h0 : CurveBasics.Curve.l C (-D) = 0 := by
      rw [CurveBasics.Curve.l, hbot]; simp
    omega
  obtain ⟨h, hh, hh0⟩ := Submodule.ne_bot_iff _ |>.mp hne
  refine ⟨h, hh0, sub_eq_zero.mp ?_⟩
  have heff : (C.div h - D).IsEffective := by
    rcases (CurveBasics.Curve.mem_L_iff C).mp hh with h0 | heff
    · exact absurd h0 hh0
    · simpa [sub_eq_add_neg] using heff
  have hdeg2 : C.deg (C.div h - D) = 0 := by
    rw [CurveBasics.Curve.deg_sub, Work.CurveBasics.Order.deg_div, hD, sub_zero]
  exact (Work.CurveBasics.Divisor.deg_eq_zero_iff heff).mp hdeg2

/-- **Riemann–Roch at genus zero, difference form**: two divisors of degree zero on a curve of
genus zero are linearly equivalent. -/
theorem linEquiv_of_deg_eq_zero (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) {D E : C.Div}
    (hD : C.deg D = 0) (hE : C.deg E = 0) :
    ∃ h : C.functionField, h ≠ 0 ∧ C.div h = D - E := by
  have : C.deg (D - E) = 0 := by rw [CurveBasics.Curve.deg_sub, hD, hE, sub_self]
  exact principal_of_deg_zero C hg (D - E) this

/-- **At genus zero, a divisor is principal exactly when its degree is zero.** -/
theorem deg_eq_zero_iff_principal (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (D : C.Div) :
    C.deg D = 0 ↔ ∃ h : C.functionField, h ≠ 0 ∧ C.div h = D :=
  ⟨principal_of_deg_zero C hg D, fun ⟨_, _, hdiv⟩ => hdiv ▸ Work.CurveBasics.Order.deg_div C _⟩

/-- **At genus zero, two divisors are linearly equivalent exactly when they have the same
degree.**  This is the divisor-theoretic form of "the Jacobian of a genus-zero curve is
trivial". -/
theorem linEquiv_iff_deg_eq (C : CurveBasics.Curve k)
    (hg : RiemannRoch.Curve.genus C = 0) (D E : C.Div) :
    KeyLemma.Curve.LinEquiv C D E ↔ C.deg D = C.deg E := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨f, _, hdiv⟩ := h
    have h0 : C.deg (D - E) = 0 := hdiv ▸ Work.CurveBasics.Order.deg_div C f
    rw [CurveBasics.Curve.deg_sub, sub_eq_zero] at h0
    exact h0
  · refine principal_of_deg_zero C hg (D - E) ?_
    rw [CurveBasics.Curve.deg_sub, h, sub_self]

end Work.GenusZero
