/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The divisor cut out by an ideal is multiplicative (area SY, `divOf`)

For a curve `C` over a field `F`, an affine open `W ⊆ C` with `Γ(C,W)` a Dedekind domain and
nonzero ideals `I, J ⊆ Γ(C,W)`, the divisor of the product is the sum of the divisors:

`divisorOfIdeal C W hW (I * J) = divisorOfIdeal C W hW I + divisorOfIdeal C W hW J`.

This is the additivity of `Σ_z v_z(J) [z]` in the ideal, which holds because the multiplicity
`v_z = Associate.count (m_z)` of a maximal ideal in the factorization of an ideal is additive
(`Associates.count_mul`, applied to the height-one prime `m_z`).

Used to make `divOfChart` behave like a divisor attached to an ideal, e.g. for
`Work.SymQuot.DivOf.divOfChart` and the compatibility of the divisor map with products of ideals
(`powMap`, `Sym`-actions).
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {F : Type u} [Field F]

/-- **The order of an ideal at a height-one prime is additive**: the exponent of a prime in the
factorization of `I * J` is the sum of its exponents in the factorizations of `I` and `J`. -/
theorem idealOrder_mul (C : Curve F) (V : C.left.Opens)
    [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V))]
    (v : IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V)))
    {I J : Ideal ↥(C.left.presheaf.obj (Opposite.op V))} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealOrder C V (I * J) v = idealOrder C V I v + idealOrder C V J v := by
  rw [idealOrder, idealOrder, idealOrder, ← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible

/-- **The order of vanishing of an ideal at a place is additive**: `placeOrder` is the
`Associates.count` of the maximal ideal `m_z`, which is additive in the ideal. -/
theorem placeOrder_mul (C : Curve F) (V : C.left.Opens) [Nonempty V]
    (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V))]
    {I J : Ideal ↥(C.left.presheaf.obj (Opposite.op V))} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (z : C.Place) (hz : z.point ∈ V) :
    placeOrder C V (I * J) z hz = placeOrder C V I z hz + placeOrder C V J z hz := by
  by_cases hp : placeIdeal C V z hz = ⊥
  · -- the maximal ideal is zero: every order vanishes
    have h0 : ∀ K : Ideal ↥(C.left.presheaf.obj (Opposite.op V)),
        placeOrder C V K z hz = 0 := by
      intro K
      rw [placeOrder, hp,
        show Associates.mk (⊥ : Ideal ↥(C.left.presheaf.obj (Opposite.op V))) = 0 from
          Associates.mk_eq_zero.mpr rfl]
      simp [Associates.count_reducible (not_irreducible_zero (M := Associates _))]
    rw [h0 (I * J), h0 I, h0 J, add_zero]
  · -- otherwise pass to the height-one prime given by `placeIdeal`
    let v : IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V)) :=
      { asIdeal := placeIdeal C V z hz
        isPrime := (placeIdeal_isMaximal hV z hz).isPrime
        ne_bot := hp }
    have h1 : placeOrder C V (I * J) z hz = idealOrder C V (I * J) v := rfl
    have h2 : placeOrder C V I z hz = idealOrder C V I v := rfl
    have h3 : placeOrder C V J z hz = idealOrder C V J v := rfl
    rw [h1, h2, h3]
    exact idealOrder_mul C V v hI hJ

theorem divisorOfIdeal_mul {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {W : C.left.Opens} [Nonempty W] (hW : AlgebraicGeometry.IsAffineOpen W)
    [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op W))]
    {I J : Ideal ↥(C.left.presheaf.obj (Opposite.op W))} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Work.SymQuot.DivOf.divisorOfIdeal C W hW (I * J) =
      Work.SymQuot.DivOf.divisorOfIdeal C W hW I +
        Work.SymQuot.DivOf.divisorOfIdeal C W hW J := by
  ext z
  rw [divisorOfIdeal_apply, Finsupp.add_apply, divisorOfIdeal_apply, divisorOfIdeal_apply]
  by_cases hz : z.point ∈ W
  · simp only [dif_pos hz]
    rw [placeOrder_mul C W hW hI hJ z hz]
    push_cast
    ring
  · simp only [dif_neg hz, add_zero]

end Work.SymQuot.DivOf
