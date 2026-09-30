/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — density of separable points and the geometric inputs of COV

This file contains the *geometric* inputs of §3.5 of `NOTES_LEAD_jacobian_GC.md`, i.e. the
ingredients of `COV`/`COV′` that are not available in the library yet, recorded as named
inputs with the exact statements of the design:

* `SepClosedDense K` — density of `K`-points of a smooth geometrically irreducible scheme of
  finite type over a separably closed field `K`, and `dense_sepClosed_points`;
* `PointsDenseAfterBaseChange K` — the rational points of `X_K` are dense in `X_F`, and
  `dense_points_extension`;
* `GenericTranslate K` — GENERIC′: adding a degree-zero divisor to the generic `g`-tuple of
  `Sym^g` keeps `ℓ = 1` (the iteration of RR6, `i_add_generic`, `g` times), and
  `generic_translate`;
* `ChartBaseChange K` — the base change of the Brill–Noether chart along a field extension,
  and `V_base_change`.

**On the proof status.**  These four statements are *true* and are the content of steps 1–4 of
§3.5 of the lead's design; none of them is available in the library at the present pin
(they need, respectively, the theory of smooth morphisms over separably closed fields, the
Noetherian approximation of opens of `X_{k^s}`, RR6 over the function field, and the base
change of the symmetric power).  They are therefore recorded as classes, exactly as area `PR`
records the interfaces of areas CB and SY, so that every theorem of areas `GC`/`DS` that uses
them carries them as an explicit hypothesis, and so that the statements are pinned down for
the area that will prove them.
-/
import Submission.Work.Charts.Datum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-
**RETIRED as inputs of the COV path (lead design `Submission/Work/NOTES_LEAD_jacobian_charts3.md`
§0.1/§0.4).**  `PointsDenseAfterBaseChange` and `GenericTranslate` are no longer needed: route B
of that note proves COV′ directly over `k` without Noetherian approximation, without dominance of
the translations `T_c` and without GENERIC′.  They are kept as statements (they are true), but
nothing on the COV path should depend on them.  `SepClosedDense` (below) is *proved* and is still
used, by route B's SEP-PT step.
-/


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### The base change of a `K`-scheme along a field extension -/

/-- **The base change of a `K`-scheme along a field extension `K → F`**, as a scheme. -/
abbrev bcScheme (X : Sch K) (F : Type u) [Field F] [Algebra K F] : Scheme :=
  Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap K F)))

/-- **The base change of a `K`-point of `X`**: a `K`-point `p` of `X` yields an `F`-point of
the base change `X_F`, namely the `F`-point `p_F` of `X` together with the identity of
`Spec F`. -/
def bcSchemePt (X : Sch K) (F : Type u) [Field F] [Algebra K F] (p : FPt X K) :
    Spec (CommRingCat.of F) ⟶ bcScheme X F :=
  Limits.pullback.lift ((specOfMap (K := K) (IsScalarTower.toAlgHom K K F) ≫ p).left)
    (𝟙 _) (by
      rw [Category.id_comp, Over.comp_left, Category.assoc, Over.w p, specOf_hom,
        specOfMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
      apply CommRingCat.hom_ext
      ext x
      simp [Algebra.algebraMap_self])

/-- A `K`-point of `X` base changed to `F` lands in an open `U` of `X_F`. -/
def BCpt.LandsIn (X : Sch K) (F : Type u) [Field F] [Algebra K F] (p : FPt X K)
    (U : (bcScheme X F).Opens) : Prop :=
  (bcSchemePt X F p).base (IsLocalRing.closedPoint F) ∈ U

/-! ### Density of separable points -/

/-- **Area `CH`, named input (density of separable points).**  Every nonempty open subscheme of
a smooth, geometrically irreducible scheme of finite type over a separably closed field `K`
has a `K`-point.

The proof is *not* the naive "closed points of a smooth `K`-scheme are rational": that
statement is **false** in characteristic `p` — for `K = 𝔽_p(t)^{sep}` and `X = 𝔸¹_K`, the closed
point `x^p - t` of the smooth `K`-scheme `𝔸¹_K` has residue field `K(t^{1/p})`, purely
inseparable of degree `p`.  The correct argument uses the local structure of smooth morphisms:
`X → Spec K` is smooth and surjective, hence acquires a section after an étale base change
`S' → Spec K`; an étale cover of `Spec K` is a disjoint union of spectra of finite *separable*
extensions of `K`, which `IsSepClosed` collapses to `K` itself, so `X(K) ≠ ∅`.  Applying this
to the nonempty open subscheme `U` (again smooth, geometrically irreducible and of finite type)
gives the claim.  What is missing at the present pin is the étale-local structure theorem for
smooth morphisms (or, equivalently, Lang's theorem that separably closed fields are `C_1`). -/
class SepClosedDense (K : Type u) [Field K] [IsSepClosed K] : Prop where
  /-- density of `K`-points -/
  exists_fpt_of_opens : ∀ (X : Sch K) [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens), U ≠ ⊥ → ∃ p : FPt X K, p.LandsIn U

/-- **Density of `K`-points** of a nonempty open of a smooth geometrically irreducible scheme
of finite type over a separably closed field. -/
theorem dense_sepClosed_points [IsSepClosed K] [SepClosedDense K] (X : Sch K) [Smooth X.hom]
    [GeometricallyIrreducible X.hom] [LocallyOfFiniteType X.hom] (U : X.left.Opens)
    (hU : U ≠ ⊥) : ∃ p : FPt X K, p.LandsIn U :=
  SepClosedDense.exists_fpt_of_opens X U hU

/-- **Area `CH`, named input (density of `K`-points in the base change).**  The `K`-rational
points of `X` are dense in `X_F`: every nonempty open of `X_F` contains the base change of a
`K`-point of `X`.

This is step 3 of §3.5: it is applied to `X = Sym^g C` and `F ⊇ k^s` to produce the centre
`E_c` of a chart translate; the point is that the chart translate is an open of `Sym^g_{k^s}`
and the centres have to be *rational over a finite extension*, so one must find a point of
`Sym^g_k` (not merely of `Sym^g_{k^s}`) inside it.  Its proof needs the Noetherian approximation
of opens of `X_{k^s} = colim X_{k_1}` over the finite subextensions `k_1/k` of `k^s` — the step
flagged as a risk in §6 of the lead's design. -/
class PointsDenseAfterBaseChange (K : Type u) [Field K] [IsSepClosed K] : Prop where
  /-- density of the base change of `K`-points -/
  exists_fpt_landsIn : ∀ (F : Type u) [Field F] [Algebra K F] (X : Sch K) [Smooth X.hom]
    [GeometricallyIrreducible X.hom] [LocallyOfFiniteType X.hom]
    (U : (bcScheme X F).Opens), U ≠ ⊥ → ∃ p : FPt X K, BCpt.LandsIn X F p U

/-- **Density of `K`-points in the base change `X_F`.** -/
theorem dense_points_extension [IsSepClosed K] [PointsDenseAfterBaseChange K] (F : Type u)
    [Field F] [Algebra K F] (X : Sch K) [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [LocallyOfFiniteType X.hom] (U : (bcScheme X F).Opens) (hU : U ≠ ⊥) :
    ∃ p : FPt X K, BCpt.LandsIn X F p U :=
  PointsDenseAfterBaseChange.exists_fpt_landsIn F X U hU

/-! ### GENERIC′ -/

/-- **Area `CH`, named input (GENERIC′).**  Adding a degree-zero divisor `c` to the generic
`g`-tuple of `Sym^g C` gives a divisor of `ℓ = 1`: this is the statement that for the generic
point `ξ` of `Sym^g C` the class of `divOf ξ + c` is non-special.

Its proof is the iteration of RR6 (`i_add_generic`: adding the generic point of `C_F` to a
special divisor drops `i` by one, `g` times), together with `i (divOf ξ) = g` and the
Riemann–Roch equation: `i (divOf ξ + c) = 0` and `deg (divOf ξ + c) = g` force `ℓ = 1`. -/
class GenericTranslate (K : Type u) [Field K] : Prop where
  /-- GENERIC′ -/
  ell_generic_add : ∀ {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] [SymProps C R.g] (c : Dv C K), Ddeg C K c = 0 →
    ell C (divOf (genericFPt (Sym C R.g)) + pullK C c) = 1

/-- **`generic_translate`** (§3.5): the generic point of `Sym^g C` translated by a degree-zero
divisor has `ℓ = 1`.  (The translation is by the base change of `c` to the function field of
`Sym^g C`, which is where the generic point lives.) -/
theorem generic_translate [GenericTranslate K] {C : Curve K} [Work.SpecLin.DivBase C]
    (R : RochData C) [Work.SpecLin.SymGeom C R.g] [SymProps C R.g] (c : Dv C K)
    (hc : Ddeg C K c = 0) :
    ell C (divOf (genericFPt (Sym C R.g)) + pullK C c) = 1 :=
  GenericTranslate.ell_generic_add R c hc

/-! ### Base change of the Brill–Noether chart -/

/-- **The base-changed Brill–Noether chart.**  For a chart datum `d` over `K` and a field
extension `K → L`, the chart datum `d'` of the base-changed curve `C_L`, together with an
identification `e` of the points of `Sym^g C` over `L` with the points of `Sym^g(C_L)` (this
is the base change `Sym^g(C_L) ≅ (Sym^g C)_L` of area `SY`, on field points). -/
structure BCChart (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R) (L : Type u) [Field L] [Algebra K L] where
  [db : Work.SpecLin.DivBase (C.baseChange L)]
  /-- the Riemann–Roch data of the base-changed curve -/
  R' : RochData (C.baseChange L)
  [sym : Work.SpecLin.SymGeom (C.baseChange L) R'.g]
  /-- the chart datum of the base-changed curve -/
  d' : BNData (C.baseChange L) R'
  /-- the identification of the points of `Sym^g C` over `L` with those of `Sym^g(C_L)` -/
  e : Work.GCBasics.FPt (Sym C R.g) L ≃ Work.GCBasics.FPt (Sym (C.baseChange L) R'.g) L

/-- **Area `CH`, named input (`V_baseChange`).**  The Brill–Noether chart is stable under base
change of the field of definition: for a chart datum `d` over `K` there is a chart datum `d'`
of the base-changed curve `C_L` and an identification `e` of the points of `Sym^g C` over `L`
with those of `Sym^g(C_L)` such that a point `p` lies in `V d` exactly when `e p` lies in
`V d'`.

This is `V (d.baseChange L) = (Sym.baseChangeIso L) ⁻¹ᵁ (V d)` of §3.5, in the point-level form
used by area `DS`: the identification `e` is the base change of area `SY`, and the statement is
equivalent to the insensitivity of the Brill–Noether condition `i (divOf y) = 0` to the field
of definition, which is the content of the invariance of `ℓ` and linear equivalence under base
change (area `CB`). -/
class ChartBaseChange (K : Type u) [Field K] : Prop where
  /-- existence of the base-changed chart -/
  exists_bcChart : ∀ {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R) (L : Type u) [Field L] [Algebra K L],
    Nonempty (BCChart C R d L)
  /-- `V_baseChange` -/
  V_base_change : ∀ {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R) (L : Type u) [Field L] [Algebra K L]
    (D : BCChart C R d L), letI := D.db; letI := D.sym;
    ∀ p : Work.GCBasics.FPt (Sym C R.g) L, p.LandsIn d.V ↔ (D.e p).LandsIn D.d'.V

/-- **`V_baseChange`** (§3.5): the chart of the base-changed curve is the base change of the
chart. -/
theorem V_base_change [ChartBaseChange K] {C : Curve K} [Work.SpecLin.DivBase C]
    (R : RochData C) [Work.SpecLin.SymGeom C R.g] (d : BNData C R) (L : Type u) [Field L]
    [Algebra K L] (D : BCChart C R d L) : letI := D.db; letI := D.sym;
    ∀ p : FPt (Sym C R.g) L, p.LandsIn d.V ↔ (D.e p).LandsIn D.d'.V :=
  ChartBaseChange.V_base_change R d L D

end

end Work.Charts
