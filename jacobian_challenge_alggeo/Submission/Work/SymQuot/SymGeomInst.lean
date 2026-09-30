/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `SymGeom C n` instances (area SY)

`Work.SpecLin.SymGeom C n` is the interface through which areas `PR`, `CH` and `GC` consume the
symmetric powers.  This file inhabits it:

* `instSymGeomOfNeZero` — for `n ≥ 1`, from `symGeomOfComplete` and the completeness half of the
  point/divisor dictionary `DivOf.Complete.divOf_complete`;
* `Sym.symGeom_zero` (in `Sym/symGeom_zero.lean`) — for `n = 0`;
* `symGeomFamily C : ∀ n, SymGeom C n` — the two cases combined, for consumers such as
  `GroupChunk.Input.symGeom` that quantify over all `n`.

The `DivBase` argument of `SymGeom` resolves to `Work.SymQuot.instDivBase`, the concrete
ramification-weighted `bc` against which `divOf_map` is proved.
-/
import Submission.Work.SymQuot.SymGeomOfComplete
import Submission.Work.SymQuot.DivOf.Complete.divOf_complete
import Submission.Work.SymQuot.Sym.symGeom_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

/-- **The symmetric powers are a `SymGeom` datum**, for `n ≥ 1`. -/
noncomputable instance instSymGeomOfNeZero {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (n : ℕ) [NeZero n] [CurveAffineCover C] : Work.SpecLin.SymGeom C n :=
  symGeomOfComplete (fun {F} _ _ D hD hdeg =>
    Work.SymQuot.DivOf.Complete.divOf_complete (C := C) (n := n) D hD hdeg)

/-- **The symmetric powers are a `SymGeom` datum for `n = 0`**, with `S = Sym⁰ C` and the
constant divisor `0`.  Written out explicitly (rather than as `Classical.choice` of
`Sym.symGeom_zero`) so that `divOf` computes to `0`. -/
noncomputable def symGeomZero {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] : Work.SpecLin.SymGeom C 0 where
  S := Sym C 0
  isProper := Sym.isProper_sym C 0
  divOf := fun {F} _ _ _ => (0 : Work.SpecLin.Dv C F)
  divOf_injective := fun {F} _ _ p q _ => by
    haveI : Subsingleton (Work.SpecLin.FPt (Sym C 0) F) :=
      Sym.subsingleton_hom_sym_zero C (Work.SpecLin.specOf (K := K) F)
    exact Subsingleton.elim p q
  divOf_isEffective := fun {F} _ _ _ => Work.CurveBasics.Curve.Div.isEffective_zero
  divOf_deg := fun {F} _ _ _ => Work.CurveBasics.Curve.deg_zero (C.baseChange F)
  divOf_complete := fun {F} _ _ D hD hdeg => by
    have hD0 : D = 0 :=
      (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange F) hD).mp hdeg
    exact ⟨Sym.symZeroPt C (Work.SpecLin.specOf (K := K) F), by rw [hD0]⟩
  divOf_map := fun {F F'} _ _ _ _ _ _ => by rw [Work.SpecLin.DivBase.bc_zero]
  powMap := fun {T} _ => Sym.symZeroPt C T
  powMap_comp := fun {T T'} _ _ => by
    haveI : Subsingleton (T' ⟶ Sym C 0) := Sym.subsingleton_hom_sym_zero C T'
    exact Subsingleton.elim _ _
  divOf_powMap := fun {F} _ _ x => by simp
  split := fun {F F'} _ _ _ _ _ _ _ D hD hdeg => by
    have hD0 : D = 0 :=
      (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange F) hD).mp hdeg
    refine ⟨fun m : Fin 0 => Fin.elim0 m, ?_⟩
    rw [hD0, Work.SpecLin.DivBase.bc_zero]
    simp

/-- The divisor of a point of `Sym⁰ C` is `0`. -/
@[simp]
theorem symGeomZero_divOf {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (p : Work.SpecLin.FPt (Sym C 0) F) : (symGeomZero C).divOf p = 0 := rfl

/-- **The `n = 0` instance, registered for typeclass search.** -/
noncomputable instance instSymGeomZero {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] : Work.SpecLin.SymGeom C 0 :=
  symGeomZero C

/-- **The symmetric powers are a `SymGeom` datum for every `n`**, including `Sym⁰ C = Spec K`. -/
noncomputable def symGeomFamily {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [CurveAffineCover C] (n : ℕ) : Work.SpecLin.SymGeom C n :=
  match n with
  | 0 => symGeomZero C
  | k + 1 => instSymGeomOfNeZero C (k + 1)

end Work.SymQuot
