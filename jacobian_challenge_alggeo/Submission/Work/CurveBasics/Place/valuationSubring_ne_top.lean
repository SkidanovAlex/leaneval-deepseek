/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The valuation ring of a curve at a place is a proper subring of the function field

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let `Q` be a
place of `C`, i.e. a closed point.  The valuation subring `𝒪_Q ⊆ K(C)` (the ring of functions
regular at `Q`) is a proper subring of the function field: the inverse of a uniformizer at `Q`
is not regular at `Q`, because a uniformizer has order of vanishing `1` at `Q`.

This is the (only) place where the nontriviality of the valuation at a place is used; it is the
input that turns the "the valuation ring at `Q` is the localisation of `k[h]^int` at
`k[h]^int ∩ 𝔪_Q`" statement into an unconditional one, with no hypothesis on the sign of
`ord_Q h`.
-/
import Mathlib
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.ord_uniformizer
import Submission.Work.CurveBasics.Order.ord_lem
import Submission.Work.CurveBasics.Order.div_inv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics.Place

open Work.CurveBasics

/-- **The valuation ring at a place is not the whole function field.** -/
theorem valuationSubring_ne_top {k : Type u} [Field k] {C : Curve k} (Q : C.Place) :
    Q.valuationSubring ≠ ⊤ := by
  intro htop
  have hmem : Q.uniformizer⁻¹ ∈ Q.valuationSubring := by rw [htop]; trivial
  rw [Place.mem_valuationSubring_iff] at hmem
  have hne : Q.uniformizer ≠ 0 := by
    intro h0
    have h1 : AlgebraicGeometry.Scheme.ord Q.uniformizer Q.point = 1 := Place.ord_uniformizer Q
    rw [h0, AlgebraicGeometry.Scheme.ord_zero] at h1
    exact one_ne_zero h1.symm
  have h2 : AlgebraicGeometry.Scheme.ord Q.uniformizer⁻¹ Q.point = -1 := by
    rw [Work.CurveBasics.Order.ordAt_inv C hne Q, Place.ord_uniformizer]
  rw [h2] at hmem
  linarith

end Work.CurveBasics.Place
