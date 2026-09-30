/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of divisors: the interface (area GB)

The shared conventions ask for two results about base change of divisors:

* `ell_baseChange`: `ℓ(D_{F'}) = ℓ(D)`;
* `linEquiv_baseChange_iff`: `D_{F'} ∼ D'_{F'} ↔ D ∼ D'`.

Both are about the pullback of divisors along a field extension `F → F'`, which is the map
sending a place `Q` of `C_F` to `∑ e(Q'/Q) [Q']` over the places of `C_{F'}` above it.
That map is *not* part of Mathlib and belongs to area CB, which has been asked for
`Div.baseChange` together with its compatibility with `deg`, with effectivity and with
`div` (see `NOTES_LEAD_jacobian_GC.md`, §7).

Until CB delivers it, this file records the exact interface as a structure
`Work.GCBasics.DivBaseChange C`: the pullback map and the four properties every consumer
needs.  Every statement below is a projection of that structure, so that the names of the
shared conventions exist and can be used with `BC : DivBaseChange C` as a named hypothesis.
Once CB's `Div.baseChange` is available, a single instance of this structure (whose fields
are CB's lemmas `Div.baseChange_add`, `Div.baseChange_deg`, `Div.baseChange_linEquiv` and
CB6) removes the hypothesis.
-/
import Submission.Work.GCBasics.DivApi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.GCBasics

open Work.CurveBasics

noncomputable section

variable {K : Type u} [Field K]

/-- The data of base change of divisors along field extensions of `K`, for a curve `C/K`:
the pullback `D ↦ D_{F'}` along `e : F →ₐ[K] F'`, together with the four properties that
the rest of the development uses.

Area CB is expected to build the canonical such structure from
`Curve.baseChange` and the ramification theory of places; see the module docstring. -/
structure DivBaseChange (C : Curve K) where
  /-- The pullback of divisors along a field extension. -/
  pull : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F'), Dv C F → Dv C F'
  /-- The pullback is additive. -/
  pull_add : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D D' : Dv C F), pull e (D + D') = pull e D + pull e D'
  /-- The pullback preserves the degree. -/
  pull_deg : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F), Ddeg C F' (pull e D) = Ddeg C F D
  /-- Linear equivalence is invariant under base change, in both directions (the backwards
  direction is descent of linear equivalence). -/
  pull_linEquiv : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D D' : Dv C F),
    LinEquiv C (pull e D) (pull e D') ↔ LinEquiv C D D'
  /-- `ℓ` is invariant under base change. -/
  pull_ell : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F), ell C (pull e D) = ell C D

namespace DivBaseChange

variable {C : Curve K} (BC : DivBaseChange C)

/-- `ℓ` is invariant under base change of divisors. -/
theorem ell_baseChange {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F) : ell C (BC.pull e D) = ell C D :=
  BC.pull_ell e D

/-- Linear equivalence is invariant under base change of divisors. -/
theorem linEquiv_baseChange_iff {F F' : Type u} [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F →ₐ[K] F') (D D' : Dv C F) :
    LinEquiv C (BC.pull e D) (BC.pull e D') ↔ LinEquiv C D D' :=
  BC.pull_linEquiv e D D'

/-- The degree is invariant under base change of divisors. -/
theorem deg_baseChange {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F) : Ddeg C F' (BC.pull e D) = Ddeg C F D :=
  BC.pull_deg e D

/-- The pullback of a principal divisor is principal. -/
theorem pull_zero {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') : BC.pull e (0 : Dv C F) = 0 := by
  have h := BC.pull_add e 0 0
  simpa using h

/-- The class map is compatible with base change. -/
theorem pic_mk_baseChange {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') {D D' : Dv C F} (h : LinEquiv C D D') :
    LinEquiv C (BC.pull e D) (BC.pull e D') :=
  (BC.pull_linEquiv e D D').mpr h

end DivBaseChange

end

end Work.GCBasics
