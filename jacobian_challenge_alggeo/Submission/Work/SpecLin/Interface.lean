/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The interfaces consumed by area SpecLin

Area `PR` (`Submission/Work/SpecLin`) proves the *specialisation of linear equivalence*
(`Work.SpecLin.specLin`).  Its statement is about the `n`-th symmetric power `Sym^n C` of a
curve, so it consumes

* `Work.SpecLin.DivBase C` — pullback of divisors along a field extension `F → F'`
  (`Div.baseChange` of area `CB`), together with its elementary properties;
* `Work.SpecLin.SymGeom C n` — the `n`-th symmetric power of `C` (area `SY`): the scheme
  `Sym^n C`, the *divisor of a point of `Sym^n`* `divOf`, and the `n`-fold addition map
  `powMap` (the quotient `C^n ⟶ Sym^n`).

The *point divisor* `ptDiv` is **not** an interface datum: it is defined concretely in
`Submission/Work/SpecLin/Points/Basic.lean` as the divisor of the closed point of `C_F`
attached to an `F`-point of `C` (`ptPlace`).  The link between area `SY`'s `divOf` and this
concrete `ptDiv` is the interface field `SymGeom.divOf_powMap`, which area `SY` discharges by
proving `divOf ∘ quot = Σ ptDiv`.

Both are *interfaces*: they collect, as data with axioms, exactly the facts that areas `CB`
and `SY` deliver.  Nothing here is an assumption specific to area `PR`; the only mathematical
input of area `PR` beyond these interfaces is `Work.SpecLin.linEquiv_of_sections`
(`Submission/Work/SpecLin/Core/linEquiv_of_sections.lean`).

The properties are recorded in the form in which they are used.  When `CB` and `SY` land,
`DivBase` and `SymGeom` are inhabited by their output; see `Submission/Work/SpecLin/NOTES.md`.
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- **Interface (area CB): base change of divisors along a field extension.**

`bc e D` is the pullback of the divisor `D` on `C_F` to `C_{F'}`, along `e : F →ₐ[K] F'`.
It is additive, preserves effectivity and degree, is functorial in `e`, commutes with
`LinEquiv` — the key point: two divisors over `F` are linearly equivalent if and only if their
pullbacks over `F'` are. -/
class DivBase (C : Work.CurveBasics.Curve K) where
  /-- Pullback of divisors along a field extension. -/
  bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F'],
    (F →ₐ[K] F') → Dv C F → Dv C F'
  /-- Pullback of `0`. -/
  bc_zero : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F'), bc e 0 = 0
  /-- Pullback is additive. -/
  bc_add : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D D' : Dv C F), bc e (D + D') = bc e D + bc e D'
  /-- Pullback commutes with negation. -/
  bc_neg : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F), bc e (-D) = -bc e D
  /-- Pullback preserves effectivity. -/
  isEffective_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') {D : Dv C F}, D.IsEffective → (bc e D).IsEffective
  /-- Pullback preserves the degree. -/
  deg_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F),
    (C.baseChange F').deg (bc e D) = (C.baseChange F).deg D
  /-- Pullback along the identity. -/
  bc_id : ∀ {F : Type u} [Field F] [Algebra K F] (D : Dv C F), bc (AlgHom.id K F) D = D
  /-- Functoriality of pullback. -/
  bc_comp : ∀ {F F' F'' : Type u} [Field F] [Field F'] [Field F''] [Algebra K F]
    [Algebra K F'] [Algebra K F''] (e : F →ₐ[K] F') (e' : F' →ₐ[K] F'') (D : Dv C F),
    bc (e'.comp e) D = bc e' (bc e D)
  /-- Linear equivalence is preserved by pullback. -/
  linEquiv_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') {D D' : Dv C F}, LinEquiv C D D' → LinEquiv C (bc e D) (bc e D')
  /-- Linear equivalence descends along a field extension. -/
  linEquiv_bc_iff : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D D' : Dv C F), LinEquiv C (bc e D) (bc e D') ↔ LinEquiv C D D'

/-- **Interface (area SY): the `n`-th symmetric power of a curve.**

This is the symmetric power `Sym^n C` together with its point-level description: field points of
`Sym^n C` correspond to effective divisors of degree `n` on `C_F` (`divOf`, injective with range
the effective divisors of degree `n`), `powMap` implements the addition of `n` points of `C`
(so that `divOf ∘ powMap` is the sum of the point divisors `Work.SpecLin.ptDiv`), all maps are
compatible with base change of the field, and an effective divisor of degree `n` splits into
points over any algebraically closed extension of the field. -/
class SymGeom (C : Work.CurveBasics.Curve K) (n : ℕ) [DivBase C] where
  /-- The scheme `Sym^n C`. -/
  S : Sch K
  /-- `Sym^n C` is proper over `K` (hence separated). -/
  isProper : IsProper S.hom
  /-- The divisor of a point of `Sym^n C`. -/
  divOf : ∀ {F : Type u} [Field F] [Algebra K F], FPt S F → Dv C F
  /-- A point of `Sym^n C` is determined by its divisor. -/
  divOf_injective : ∀ {F : Type u} [Field F] [Algebra K F] (p q : FPt S F),
    divOf p = divOf q → p = q
  /-- The divisor of a point of `Sym^n C` is effective. -/
  divOf_isEffective : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt S F),
    (divOf p).IsEffective
  /-- The divisor of a point of `Sym^n C` has degree `n`. -/
  divOf_deg : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt S F),
    (C.baseChange F).deg (divOf p) = n
  /-- Every effective divisor of degree `n` is the divisor of a point of `Sym^n C`. -/
  divOf_complete : ∀ {F : Type u} [Field F] [Algebra K F] (D : Dv C F), D.IsEffective →
    (C.baseChange F).deg D = n → ∃ p : FPt S F, divOf p = D
  /-- `divOf` is compatible with base change of the field. -/
  divOf_map : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (p : FPt S F), divOf (RPt.map e p) = DivBase.bc e (divOf p)
  /-- Addition of `n` points of `C`, as a morphism `C^n ⟶ Sym^n C` tested by an arbitrary
  `K`-scheme of parameters `T`. -/
  powMap : ∀ {T : Sch K}, (Fin n → (T ⟶ C.toOver)) → (T ⟶ S)
  /-- `powMap` is natural in the parameter scheme. -/
  powMap_comp : ∀ {T T' : Sch K} (g : T' ⟶ T) (x : Fin n → (T ⟶ C.toOver)),
    powMap (fun m => g ≫ x m) = g ≫ powMap x
  /-- The divisor of the sum of `n` points is the sum of their divisors. -/
  divOf_powMap : ∀ {F : Type u} [Field F] [Algebra K F] (x : Fin n → CurveFPt C F),
    divOf (powMap x) = ∑ m, ptDiv (x m)
  /-- Every effective divisor of degree `n` splits into `n` points over an algebraically closed
  extension of the field of definition. -/
  split : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [IsAlgClosed F'] (D : Dv C F), D.IsEffective →
    (C.baseChange F).deg D = n →
    ∃ x : Fin n → CurveFPt C F',
      DivBase.bc (IsScalarTower.toAlgHom K F F') D = ∑ m, ptDiv (x m)

end Work.SpecLin
