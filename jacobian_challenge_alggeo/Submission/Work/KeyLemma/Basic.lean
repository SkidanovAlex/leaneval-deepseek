/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL, layer 1: divisors, linear equivalence, and the pencil decomposition

This is the first layer of the "key lemma" `KL` of the Jacobian challenge (see
`Submission/Work/NOTES_LEAD_jacobian_blueprint.md`, §3, area KL):

> if `D`, `D'` are effective divisors of degree `n` on a curve `C_F` over a field `F`
> with `D - D' = div h`, then `Σ f(D) = Σ f(D')` in `A(F)`.

This file contains only the *divisor theory* of that statement, which needs nothing but
area `CB`:

* `Curve.posPart C h` and `Curve.negPart C h`: the divisor of zeros and the divisor of
  poles of a rational function `h`, i.e. the positive and the negative part of `div h`;
* `Curve.LinEquiv C D D'`: linear equivalence `∃ h ≠ 0, div h = D - D'`;
* `Curve.EffDiv C n`: effective divisors of degree `n`;
* the *pencil decomposition*
  `D = posPart C h + E`, `D' = negPart C h + E` with `E` effective, valid whenever
  `D` and `D'` are effective and `div h = D - D'`.

The last item is the technical heart of the reduction of `KL` to the pencil case: it says
that two linearly equivalent effective divisors are obtained from the divisors of zeros and
of poles of one rational function by adding the *same* effective divisor.

## Conventions

Everything here lives in the namespace `Work.KeyLemma.Curve`, with the curve an explicit
argument (`Work.KeyLemma.Curve.posPart C h`); `C.div`, `C.ordAt`, `C.Div`, `C.deg`,
`C.Place` are those of area `CB` (`Submission.Work.CurveBasics.*`).

## Main results

* `Work.KeyLemma.Curve.div_eq_posPart_sub_negPart`
* `Work.KeyLemma.Curve.sub_posPart_eq_sub_negPart`
* `Work.KeyLemma.Curve.pencil_decomposition`
* `Work.KeyLemma.Curve.linEquiv_refl`, `Work.KeyLemma.Curve.linEquiv_symm`,
  `Work.KeyLemma.Curve.linEquiv_trans`
-/
import Submission.Work.KeyLemma.CBImports

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-! ## Positive and negative parts of a principal divisor -/

/-- The order of vanishing of `h` at a place, as the value of the divisor `div h`
(area `CB` states this as `Curve.div_apply`; we record it here in the direction in which it
is used below). -/
theorem ordAt_eq_div (C : Curve k) (h : C.functionField) (Q : C.Place) :
    C.ordAt h Q = (C.div h) Q :=
  (Work.CurveBasics.Curve.div_apply C h Q).symm

/-- The divisor of zeros `div₀ h` of a rational function: the positive part of `div h`. -/
def posPart (C : Curve k) (h : C.functionField) : C.Div :=
  (C.div h).mapRange (fun n : ℤ => max n 0) (by simp)

/-- The divisor of poles `div_∞ h` of a rational function: the negative part of `div h`. -/
def negPart (C : Curve k) (h : C.functionField) : C.Div :=
  (C.div h).mapRange (fun n : ℤ => max (-n) 0) (by simp)

@[simp]
theorem posPart_apply (C : Curve k) (h : C.functionField) (Q : C.Place) :
    posPart C h Q = max (C.ordAt h Q) 0 := by
  rw [posPart, Finsupp.mapRange_apply, ← ordAt_eq_div]

@[simp]
theorem negPart_apply (C : Curve k) (h : C.functionField) (Q : C.Place) :
    negPart C h Q = max (-(C.ordAt h Q)) 0 := by
  rw [negPart, Finsupp.mapRange_apply, ← ordAt_eq_div]

/-- The divisor of a rational function is the difference of its divisor of zeros and its
divisor of poles. -/
theorem div_eq_posPart_sub_negPart (C : Curve k) (h : C.functionField) :
    C.div h = posPart C h - negPart C h := by
  ext Q
  rw [Finsupp.sub_apply, posPart_apply, negPart_apply, ← ordAt_eq_div]
  omega

theorem posPart_isEffective (C : Curve k) (h : C.functionField) :
    (posPart C h).IsEffective := fun Q => by
  rw [posPart_apply]; exact le_max_right _ _

theorem negPart_isEffective (C : Curve k) (h : C.functionField) :
    (negPart C h).IsEffective := fun Q => by
  rw [negPart_apply]; exact le_max_right _ _

theorem posPart_sub_negPart_apply (C : Curve k) (h : C.functionField) (Q : C.Place) :
    posPart C h Q - negPart C h Q = C.ordAt h Q := by
  rw [posPart_apply, negPart_apply]
  omega

/-- The pointwise version of the "pencil" identity: if `div h = D - D'` then
`D - div₀ h = D' - div_∞ h`, the common part being the pointwise minimum of `D` and `D'`. -/
theorem sub_posPart_eq_sub_negPart (C : Curve k) {D D' : C.Div} {h : C.functionField}
    (hh : C.div h = D - D') : D - posPart C h = D' - negPart C h := by
  ext Q
  have h1 : C.ordAt h Q = D Q - D' Q := by
    have h2 : (C.div h) Q = (D - D') Q := congrFun (congrArg DFunLike.coe hh) Q
    rw [Finsupp.sub_apply] at h2
    exact (ordAt_eq_div C h Q).trans h2
  rw [Finsupp.sub_apply, Finsupp.sub_apply, posPart_apply, negPart_apply, h1]
  omega

/-- The common part `D - div₀ h = D' - div_∞ h` is effective as soon as `D` and `D'` are
(the common part is the pointwise minimum of `D` and `D'`). -/
theorem isEffective_sub_posPart (C : Curve k) {D D' : C.Div} {h : C.functionField}
    (hD : D.IsEffective) (hD' : D'.IsEffective) (hh : C.div h = D - D') :
    (D - posPart C h).IsEffective := by
  intro Q
  have h1 : C.ordAt h Q = D Q - D' Q := by
    have h2 : (C.div h) Q = (D - D') Q := congrFun (congrArg DFunLike.coe hh) Q
    rw [Finsupp.sub_apply] at h2
    exact (ordAt_eq_div C h Q).trans h2
  rw [Finsupp.sub_apply, posPart_apply, h1]
  have := hD Q
  have := hD' Q
  omega

/-- **The pencil decomposition.** Two linearly equivalent effective divisors are obtained
from the divisor of zeros and the divisor of poles of a single rational function by adding
the same effective divisor. -/
theorem pencil_decomposition (C : Curve k) {D D' : C.Div} {h : C.functionField}
    (hD : D.IsEffective) (hD' : D'.IsEffective) (hh : C.div h = D - D') :
    D = posPart C h + (D - posPart C h) ∧
      D' = negPart C h + (D - posPart C h) ∧ (D - posPart C h).IsEffective := by
  refine ⟨?_, ?_, isEffective_sub_posPart C hD hD' hh⟩
  · rw [add_comm, sub_add_cancel]
  · rw [sub_posPart_eq_sub_negPart C hh, add_comm, sub_add_cancel]

/-- The pencil decomposition in the form in which it is used to reduce `KL` to the pencil
case: two linearly equivalent effective divisors are obtained from `div₀ h` and `div_∞ h`
for a single rational function `h` by adding the same effective divisor. -/
theorem exists_pencil_decomposition (C : Curve k) {D D' : C.Div} {h : C.functionField}
    (hD : D.IsEffective) (hD' : D'.IsEffective) (hh : C.div h = D - D') :
    ∃ E : C.Div, E.IsEffective ∧ D = posPart C h + E ∧ D' = negPart C h + E :=
  ⟨D - posPart C h, isEffective_sub_posPart C hD hD' hh,
    (pencil_decomposition C hD hD' hh).1, (pencil_decomposition C hD hD' hh).2.1⟩

/-! ## Linear equivalence -/

/-- Two divisors on a curve are *linearly equivalent* if their difference is the divisor of
a nonzero rational function. -/
def LinEquiv (C : Curve k) (D D' : C.Div) : Prop :=
  ∃ h : C.functionField, h ≠ 0 ∧ C.div h = D - D'

theorem div_one (C : Curve k) : C.div (1 : C.functionField) = 0 := by
  rw [← map_one (algebraMap k C.functionField)]
  exact Work.CurveBasics.Order.div_algebraMap_eq_zero C 1

theorem linEquiv_refl (C : Curve k) (D : C.Div) : LinEquiv C D D :=
  ⟨1, one_ne_zero, by rw [div_one]; simp⟩

theorem linEquiv_symm (C : Curve k) {D D' : C.Div} (h : LinEquiv C D D') :
    LinEquiv C D' D := by
  obtain ⟨f, hf, hfd⟩ := h
  exact ⟨f⁻¹, inv_ne_zero hf, by rw [Work.CurveBasics.Order.div_inv C hf, hfd]; abel⟩

theorem linEquiv_trans (C : Curve k) {D D' D'' : C.Div} (h : LinEquiv C D D')
    (h' : LinEquiv C D' D'') : LinEquiv C D D'' := by
  obtain ⟨f, hf, hfd⟩ := h
  obtain ⟨g, hg, hgd⟩ := h'
  exact ⟨f * g, mul_ne_zero hf hg, by rw [C.div_mul hf hg, hfd, hgd]; abel⟩

/-! ## Effective divisors of fixed degree -/

/-- The effective divisors of degree `n` on a curve.  This is the domain of the sum map
`Σ f` of the key lemma. -/
def EffDiv (C : Curve k) (n : ℕ) : Type u :=
  { D : C.Div // D.IsEffective ∧ C.deg D = n }

namespace EffDiv

variable {C : Curve k} {n : ℕ}

theorem isEffective (D : EffDiv C n) : D.1.IsEffective := D.2.1

theorem deg_eq (D : EffDiv C n) : C.deg D.1 = n := D.2.2

/-- Linear equivalence of effective divisors of degree `n`. -/
def LinEquiv (D D' : EffDiv C n) : Prop := Curve.LinEquiv C D.1 D'.1

theorem linEquiv_refl (D : EffDiv C n) : LinEquiv D D := Curve.linEquiv_refl C _

theorem linEquiv_symm {D D' : EffDiv C n} (h : LinEquiv D D') : LinEquiv D' D :=
  Curve.linEquiv_symm C h

theorem linEquiv_trans {D D' D'' : EffDiv C n} (h : LinEquiv D D') (h' : LinEquiv D' D'')
    : LinEquiv D D'' := Curve.linEquiv_trans C h h'

end EffDiv

end

end Curve

end Work.KeyLemma
