/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.LLink.Main
import Submission.Work.Arithmetic.LLink

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.Defs` — the Crauder–Katz geometric residual, decomposed

This area proves as much as can be proved, in Lean on top of the pinned Mathlib, of
Proposition `prop:elliptic` of Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, together with the function-field input of
Lemma `lemma:L-link` (2).  Its purpose is to *discharge* the single opaque residual
`Work.LLink.CrauderKatzExists 𝕜` of the sibling area `Submission/Work/LLink`, by

* isolating the paper's construction steps as named inputs, each stated in the vocabulary of
  the arithmetic area `Submission/Work/Arithmetic` (`Work.Arithmetic.GenOneCurve`,
  `Torsor.jacSq`, `IsIso`, `NotIsoJacSq`) and of Part A (`ResEquiv`, `ResAlgEquiv`, `exDiv`,
  `cInv`, `ResAlgEquiv`);
* proving every implication between them (`Submission/Work/CrauderKatz/Assembly.lean`), so that
  `Work.LLink.CrauderKatzExists 𝕜` follows from a *small* and *precisely stated* set of named
  inputs;
* proving the parts of the argument that are formalisable at all without projective geometry,
  blow-ups, cohomology of curves and Jacobian varieties (none of which are in Mathlib).

## The decomposition of `prop:elliptic` + `lemma:L-link`

The paper's proof of `prop:elliptic` produces, from a genus-one curve `C` with a divisor of
degree `5`, the smooth projective L-link

```
        T
      /   \
   Bl_C   Bl_{C'}
   /        \
  C ⊂ Q³ --ψ--> ℙ³ ⊃ C'
```

with `C' = Jac²C`, `Q³` a smooth quadric threefold, and `ψ` the Crauder–Katz quadro-cubic
transformation.  Lemma `lemma:L-link` (2) computes its invariant `c(ψ) ∈ ℤ[Bir/𝕜]` as
`[ℙ¹ × C] − [ℙ¹ × C']`, and `prop:cWF` (the weak-factorization formula) identifies the two
*exceptional divisors* of `ψ`: `Ex(ψ)` contains a divisor birational to `ℙ¹ × C'` (obtained from
the blow-up of ℙ³ along `C'`) and `Ex(ψ⁻¹)` contains one birational to `ℙ¹ × C` (from the
blow-up of `Q³` along `C`).  Their function fields are `κ(C')(t)` and `κ(C)(t)`; they are
distinct because `C ≇ Jac²C` (Shinder–Zhang, Lemma 2.7).

Formalised in the per-coefficient vocabulary of Part A (`Work.Motivic.cInv`), the input the
downstream argument needs is exactly:

* **(GEO)** a birational map `ψ : Q ⤏ P` of `𝕜`-varieties over `𝕜` with
  `exDiv ψ = {x}` and `exDiv ψ.symm = {y}` — one exceptional divisor in each direction, as
  `lemma:L-link` (L3) gives;
* **(F1)** `κ(y) ≅_𝕜 κ(C)(t)` and `κ(x) ≅_𝕜 κ(C')(t)` — the identifications of the two
  exceptional divisors with the `ℙ¹`-bundles over `C` and `Jac²C`;
* **(F2)** *one-variable function-field stability*: `κ(C)(t) ≅_𝕜 κ(C')(t)` forces
  `κ(C) ≅_𝕜 κ(C')`; for smooth projective curves the unique fibration of `C × ℙ¹` realises
  `κ(C)` as the (unique) function field of the base;
* **(F3)** *curve rigidity plus Shinder–Zhang*: a `𝕜`-isomorphism `κ(C) ≅ κ(C')` forces
  `C ≅ Jac²C`, i.e. `X.IsIso X.torsor.jacSq.cls` — a statement purely in the arithmetic area's
  vocabulary (`Torsor.IsIso`, `jacSq`);
* **(TRA)** the transports `ε : 𝔸³ ⤏ Q`, `δ : P ⤏ 𝔸³` over `𝕜` with vanishing invariant
  (`Q³` and `ℙ³` are strongly rational: `lem:GP-strongly-rational` and the fact that `[Q³] =
  [ℙ³]` since `Q³` contains a line).

**(GEO)**, **(F1)** and **(TRA)** are the fields of the structure `CrauderKatzLink` below;
**(F2)** and **(F3)** are the named `Prop`s `CylinderDetectsCurve` and
`CurveFieldIsoForcesJacSq`.  `Assembly.lean` proves

```
CrauderKatzLink + (F2) + (F3) + X.NotIsoJacSq  ⟹  ¬ ResEquiv 𝕜 y x  ⟹  QuadroCubicLink 𝕜 X,
```

hence `Work.LLink.CrauderKatzExists 𝕜`; the *field-theoretic* content of `Work.LLink`'s
`not_resEquiv_yx` field is thereby reduced to (F2) and (F3), and the *base point* `z₀`
(and the model `Z` of `C × ℙ¹` used by `QuadroCubicLink`) is eliminated: the base point can be
taken to be the exceptional divisor `y` itself, with `resEquiv_y` reflexive
(`Work.LLink.QuadroCubicLink.invAtY` computes the same value `1`).

## What is *not* formalised here, and why

None of `ℙ⁴`, a net of quadrics as a linear system, a smooth quadric threefold `Q³` as a
scheme, the blow-up of a scheme along a smooth curve, the resolution of a rational map, the
secant surface `Sym²(C)`, `Jac²C` as a scheme, or genus/Riemann–Roch is available in the
pinned Mathlib, so the *construction* of `ψ`, of its two exceptional divisors and of the
identifications (F1) is not formalisable; it is recorded as the fields of `CrauderKatzLink`
rather than silently assumed.  See `Submission/Work/CrauderKatz/NOTES.md` for the mapping
between the paper's numbered statements and these fields, and for exactly which Mathlib
ingredients a future formalisation would have to build first.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order
open Work.Arithmetic (GenOneCurve)

namespace Work.CrauderKatz

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## The function fields `κ(C)` and `κ(C)(t)` -/

/-- The function field `κ(C)` of the curve `X.C` (an integral scheme, by `Variety`): Mathlib's
`Scheme.functionField`, i.e. the stalk of the structure sheaf at the generic point. -/
noncomputable abbrev curveField (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) : Type :=
  (X.C.functionField : Type)

/-- The structure map `𝕜 → κ(D)` of an integral scheme `D` over `Spec 𝕜`: the composite of the
`𝕜`-algebra structure of the ring of global sections with the canonical map to the function field
(the stalk at the generic point).  For `D = X.C` this is `curveResMap`. -/
noncomputable def functionFieldResMap (𝕜 : Type) [Field 𝕜] (D : Scheme.{0})
    [IrreducibleSpace D] [D.Over (Spec (.of 𝕜))] : 𝕜 →+* (D.functionField : Type) :=
  letI : Nonempty (⊤ : D.Opens) := ⟨⟨genericPoint D, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
    (D ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ D.germToFunctionField ⊤).hom

/-- The structure map `𝕜 → κ(C)` of the curve. -/
noncomputable def curveResMap (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) :
    𝕜 →+* curveField 𝕜 X :=
  letI : Nonempty (⊤ : X.C.Opens) := ⟨⟨genericPoint X.C, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
    (X.C ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ X.C.germToFunctionField ⊤).hom

/-- **The cylinder field `κ(C)(t)`**: the function field of `ℙ¹ × C`, equivalently of
`𝔸¹ × C`, modelled as the fraction field `RatFunc κ(C)` of the one-variable polynomial ring
over the function field of `C`.  `𝔸¹` and `ℙ¹` are birational, so this is the function field of
the `ℙ¹`-bundles that occur as the exceptional divisors of the Crauder–Katz link. -/
noncomputable abbrev cylinderField (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) : Type :=
  RatFunc (curveField 𝕜 X)

/-- The structure map `𝕜 → κ(C)(t)` (constants). -/
noncomputable def cylResMap (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) :
    𝕜 →+* cylinderField 𝕜 X :=
  (algebraMap (curveField 𝕜 X) (cylinderField 𝕜 X)).comp (curveResMap 𝕜 X)

/-! ## A scheme model of the dual elliptic quintic `Jac²C` -/

/-- **A scheme model of `Jac²C`** (Shinder–Zhang, *L-equivalence for degree five elliptic
curves*, §2): a genus-one curve over `𝕜`, realised as a scheme, whose class in the
Weil–Châtelet group `H¹(𝕜, Jac⁰C)` of the Jacobian of `C = X.C` is `cls²`; equivalently whose
`Torsor` data is `X.torsor.jacSq`.

This is the object the paper denotes `C'`.  Mathlib has no Jacobian variety, so the *scheme* is
an input (the arithmetic area `Submission/Work/Arithmetic` carries only the class `cls²` and the
isomorphism relation `Torsor.IsIso`); this structure is what makes the paper's statement
`C' = Jac²C` precise at the level of schemes. -/
structure JacSqModel (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) where
  /-- The curve `C' = Jac²C`. -/
  C' : GenOneCurve 𝕜
  /-- `C' = Jac²C`: same Jacobian, class `cls²`. -/
  torsor_eq : C'.torsor = X.torsor.jacSq

namespace JacSqModel

variable {X : GenOneCurve 𝕜} (M : JacSqModel 𝕜 X)

/-- `C' = Jac²C` has the same Jacobian as `C`. -/
theorem E_eq : M.C'.torsor.E = X.torsor.E := by rw [M.torsor_eq]; rfl

/-- The class of `C' = Jac²C` is the class `cls²` of `X.torsor.jacSq` (heterogeneous equality:
the two classes live in the `W` of the same torsor, identified by `torsor_eq`). -/
theorem cls_heq : HEq M.C'.torsor.cls (X.torsor.jacSq.cls) := by
  rw [M.torsor_eq]

end JacSqModel

/-! ## The two function-field inputs (F2) and (F3) -/

/-- **(F2) One-variable function-field stability**, in the form in which the paper uses it:

> if `κ(ℙ¹ × C) ≅_𝕜 κ(ℙ¹ × C')` then `κ(C) ≅_𝕜 κ(C')`.

For smooth projective curves `C` this holds because `C × ℙ¹` has a unique structure of a
`ℙ¹`-fibration (for `C` non-rational it is the minimal ruled surface; for `C ≅ ℙ¹` both sides
are rational), so the base curve is recovered from the function field of the surface.  It is the
first half of the paper's input "`C` and `C'` are not stably birational"; Mathlib has no
minimal models and no theory of fibrations of surfaces, so it is recorded as a named input.

Note that this is *not* implied by `X.NotIsoJacSq` and is not assumed anywhere silently: it is a
hypothesis of `Work.CrauderKatz.noCylinderIso_of_F2_F3` and of the assembly theorems of
`Assembly.lean`. -/
def CylinderDetectsCurve (𝕜 : Type) [Field 𝕜] : Prop :=
  ∀ (X Y : GenOneCurve 𝕜),
    (∃ e : cylinderField 𝕜 X ≃+* cylinderField 𝕜 Y,
        e.toRingHom.comp (cylResMap 𝕜 X) = cylResMap 𝕜 Y) →
      ∃ e : curveField 𝕜 X ≃+* curveField 𝕜 Y,
        e.toRingHom.comp (curveResMap 𝕜 X) = curveResMap 𝕜 Y

/-- **(F3) Curve rigidity + Shinder–Zhang**, in the arithmetic area's own vocabulary:

> if `κ(C) ≅_𝕜 κ(Jac²C)` then `C ≅ Jac²C`, i.e. `X.IsIso X.torsor.jacSq.cls`.

The first half is the classical statement that birational smooth projective curves are
isomorphic; the second is that, for two genus-one curves with the same Jacobian, isomorphism is
the same as lying in the same `Aut(E)`-orbit on `H¹(𝕜,E)` (`Torsor.IsIso`, Silverman *AEC*
Exercise 10.4).  Together they make `X.NotIsoJacSq`, i.e. Shinder–Zhang Lemma 2.7, contradict
any isomorphism of the curve function fields — this is the *only* place where the arithmetic
input of `Submission/Work/Arithmetic` is consumed by the geometry. -/
def CurveFieldIsoForcesJacSq (𝕜 : Type) [Field 𝕜] {X : GenOneCurve 𝕜}
    (M : JacSqModel 𝕜 X) : Prop :=
  (∃ e : curveField 𝕜 X ≃+* curveField 𝕜 M.C',
      e.toRingHom.comp (curveResMap 𝕜 X) = curveResMap 𝕜 M.C') →
    X.torsor.IsIso X.torsor.jacSq.cls

/-- **The function-field input** of the Crauder–Katz link, bundling (F2) and (F3). -/
abbrev FunctionFieldInput (𝕜 : Type) [Field 𝕜] : Prop :=
  CylinderDetectsCurve 𝕜 ∧
    ∀ (X : GenOneCurve 𝕜) (M : JacSqModel 𝕜 X), CurveFieldIsoForcesJacSq 𝕜 M

/-- **(F2) + (F3) applied to the two residue-field presentations.**  If the residue fields of two
points `y`, `x` of `𝕜`-schemes are presented as the cylinder fields `κ(C)(t)` and `κ(C')(t)`
(`ResAlgEquiv`, the paper's (F1)), then the function-field input (F2)+(F3) together with
`X.NotIsoJacSq` (Shinder–Zhang Lemma 2.7) forces `κ(y) ≇_𝕜 κ(x)`.

This is the *only* place where the field theory enters the Crauder–Katz argument, and every
hypothesis is explicit. -/
theorem not_resEquiv_of_presentations {X : GenOneCurve 𝕜} (M : JacSqModel 𝕜 X)
    {Q P : Scheme.{0}} [IrreducibleSpace Q] [IrreducibleSpace P]
    [Q.Over (Spec (.of 𝕜))] [P.Over (Spec (.of 𝕜))] {x : Q} {y : P}
    (resY : Work.LLink.ResAlgEquiv 𝕜 y (cylinderField 𝕜 X) (cylResMap 𝕜 X))
    (resX : Work.LLink.ResAlgEquiv 𝕜 x (cylinderField 𝕜 M.C') (cylResMap 𝕜 M.C'))
    (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) : ¬ ResEquiv 𝕜 y x :=
  Work.LLink.not_resEquiv_of_ringEquiv (A := cylinderField 𝕜 X)
    (B := cylinderField 𝕜 M.C') (cylResMap 𝕜 X) (cylResMap 𝕜 M.C') resX resY
    (fun h => hni (hF.2 X M (hF.1 X M.C' h)))

/-! ## The geometric residual -/

/-- **The Crauder–Katz link, decomposed.**

Every field is a separately attackable statement, and every one of them is a paper statement:

* `C'`, `torsor_eq` — `C' = Jac²C` (Shinder–Zhang §2; Lemma 2.7);
* `Q`, `P`, `ψ` — the quadro-cubic transformation `ψ : Q³ ⤏ ℙ³` of `prop:elliptic`, together
  with the smooth quadric `Q³ ⊃ C` and the residual curve `C' ⊂ ℙ³` (the latter two are
  subsumed in `P`/`ψ`: nothing downstream of `ψ` mentions them — see `NOTES.md` §3);
* `x`, `y` with `exDiv ψ = {x}` and `exDiv ψ.symm = {y}` — `lemma:L-link` (L3) plus the
  weak-factorization formula `prop:cWF`: `ψ` has exactly one exceptional divisor in each
  direction, `x` (birational to `ℙ¹ × C'`) and `y` (birational to `ℙ¹ × C`);
* `resY`, `resX` — **(F1)**: the residue fields of the two exceptional divisors, presented as the
  cylinder fields `κ(C)(t)` and `κ(C')(t)` (`ResAlgEquiv`);
* `ε`, `δ`, `cInv_ε`, `cInv_δ` — **(TRA)**: the transports to affine space over `𝕜`, with
  vanishing invariant (`Q³` and `ℙ³` strongly rational, `lem:GP-strongly-rational`).

The *field-theoretic* input `¬ ResEquiv 𝕜 y x` is **not** a field of this structure: it is
*derived* in `Assembly.lean` from `resX`, `resY`, `(F2)` and `(F3)` together with the caller's
`X.NotIsoJacSq` (see `not_resEquiv_yx`).  Likewise no model `Z` of `C × ℙ¹` and no base point
`z₀` are needed: the base point is the exceptional divisor `y` itself. -/
structure CrauderKatzLink (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) where
  /-- A scheme model of `C' = Jac²C`. -/
  M : JacSqModel 𝕜 X
  /-- The source threefold `Q³` of the link. -/
  Q : Scheme.{0}
  [varietyQ : Variety 𝕜 Q]
  /-- The target threefold `ℙ³` of the link. -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- The Crauder–Katz quadro-cubic transformation. -/
  ψ : Q.BirationalMap P
  [isOverψ : ψ.IsOver (Spec (.of 𝕜))]
  /-- The exceptional divisor of `ψ` on the source, birational to `ℙ¹ × C'`. -/
  x : Q
  /-- The exceptional divisor of `ψ⁻¹` on the target, birational to `ℙ¹ × C`. -/
  y : P
  /-- `x` is the only exceptional divisor of `ψ` (one in each direction: `L3` + `prop:cWF`). -/
  exDiv_ψ : exDiv ψ = {x}
  /-- `y` is the only exceptional divisor of `ψ⁻¹`. -/
  exDiv_ψ_symm : exDiv ψ.symm = {y}
  /-- **(F1)** the function field of the `ℙ¹ × C`-divisor is `κ(C)(t)`. -/
  resY : Work.LLink.ResAlgEquiv 𝕜 y (cylinderField 𝕜 X) (cylResMap 𝕜 X)
  /-- **(F1)** the function field of the `ℙ¹ × C'`-divisor is `κ(C')(t)`. -/
  resX : Work.LLink.ResAlgEquiv 𝕜 x (cylinderField 𝕜 M.C') (cylResMap 𝕜 M.C')
  /-- **(TRA)** the birational identification `𝔸³ ⤏ Q³`. -/
  ε : (Work.LLink.Affine3 𝕜).BirationalMap Q
  [isOverε : ε.IsOver (Spec (.of 𝕜))]
  /-- **(TRA)** the birational identification `ℙ³ ⤏ 𝔸³`. -/
  δ : P.BirationalMap (Work.LLink.Affine3 𝕜)
  [isOverδ : δ.IsOver (Spec (.of 𝕜))]
  /-- The transport `ε` contributes nothing (`Q³` is strongly rational). -/
  cInv_ε : cInv 𝕜 y ε = 0
  /-- The transport `δ` contributes nothing. -/
  cInv_δ : cInv 𝕜 y δ = 0

namespace CrauderKatzLink

variable {X : GenOneCurve 𝕜} (L : CrauderKatzLink 𝕜 X)

local instance instVarietyQ : Variety 𝕜 L.Q := L.varietyQ
local instance instVarietyP : Variety 𝕜 L.P := L.varietyP
local instance instIsOverψ : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
local instance instIsOverε : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
local instance instIsOverδ : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ

/-- **The two function-field inputs (F2) and (F3) imply the non-isomorphism of the two
exceptional divisors' function fields**, hence `¬ ResEquiv 𝕜 y x`: if the two residue fields were
`𝕜`-isomorphic, (F2) would produce an isomorphism `κ(C) ≅ κ(C')` of curve function fields, (F3)
would then give `C ≅ Jac²C`, contradicting the caller's `X.NotIsoJacSq` (Shinder–Zhang
Lemma 2.7).  This is the *exact* field-isomorphism input, recorded as an explicit hypothesis and
never assumed silently. -/
theorem noCylinderIso (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    ¬ ∃ e : cylinderField 𝕜 X ≃+* cylinderField 𝕜 L.M.C',
        e.toRingHom.comp (cylResMap 𝕜 X) = cylResMap 𝕜 L.M.C' :=
  fun h => hni (hF.2 X L.M (hF.1 X L.M.C' h))

/-- **The non-isomorphism of the two exceptional divisors** (the paper's `κ(C)(t) ≇ κ(C')(t)`,
i.e. `C` and `C'` are not stably birational), derived from (F2), (F3) and `X.NotIsoJacSq`
through the residue-field presentations (F1) of the link.  Every hypothesis is named; nothing is
assumed silently. -/
theorem not_resEquiv_yx (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    ¬ ResEquiv 𝕜 L.y L.x :=
  not_resEquiv_of_presentations L.M L.resY L.resX hF hni

/-- The flipped form of `not_resEquiv_yx`: `κ(x) ≇ κ(y)`, with the arguments in the order in
which the L-link counting lemmas consume them. -/
theorem not_resEquiv_xy (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    ¬ ResEquiv 𝕜 L.x L.y := fun h =>
  L.not_resEquiv_yx hF hni (Work.Motivic.ResEquiv.symm h)

/-- The `[κ(ℙ¹ × C)]`-coefficient of the Crauder–Katz link itself is `1` (the paper's
`lemma:L-link` item 2, in Part A's vocabulary): `y` matches the base point `y`, `x` does not. -/
theorem cInv_ψ (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) : cInv 𝕜 L.y L.ψ = 1 :=
  Work.LLink.cInv_eq_one_of_exDiv_eq_singletons L.y L.ψ L.exDiv_ψ L.exDiv_ψ_symm
    (L.not_resEquiv_xy hF hni) (Work.Motivic.ResEquiv.refl 𝕜 L.y)

/-- The link is motivically non-trivial at the exceptional divisor `y`. -/
theorem cInv_ψ_ne_zero (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    cInv 𝕜 L.y L.ψ ≠ 0 := by
  rw [L.cInv_ψ hF hni]; norm_num

/-- The transported Cremona map of the link, written in the affine coordinates of `Cr 𝕜 3`:
`φ = ε ∘ ψ ∘ δ`, an explicit element of `Work.LLink.Affine3 𝕜 ⤏ Work.LLink.Affine3 𝕜`. -/
noncomputable def toCremona : (Work.LLink.Affine3 𝕜).BirationalMap (Work.LLink.Affine3 𝕜) :=
  Work.LLink.transport L.ε L.ψ L.δ

/-- The transported map is defined over `𝕜`, hence lies in the Cremona group `Cr 𝕜 3`
(`MotivicInvariants.Cr`). -/
noncomputable def toCr : Cr 𝕜 3 :=
  Work.LLink.transportCr L.ε L.ψ L.δ

/-- **The invariant of the transported Crauder–Katz map is `1`** — the paper's
`c(φ) = c(ψ) = [ℙ¹ × C] − [ℙ¹ × C'] ≠ 0` in the per-coefficient vocabulary of Part A. -/
theorem cInv_toCremona (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) (z : L.P) :
    cInv 𝕜 z L.toCremona = cInv 𝕜 z L.ε + cInv 𝕜 z L.ψ + cInv 𝕜 z L.δ :=
  Work.LLink.cInv_transport_eq L.ε L.ψ L.δ z

/-- **The main computation of this area**: the transported Crauder–Katz map has `[κ(ℙ¹×C)]`-
coefficient exactly `1`, where the base point is the exceptional divisor `y` itself. -/
theorem cInv_toCremona_at_y (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    cInv 𝕜 L.y L.toCremona = 1 := by
  change cInv 𝕜 L.y (Work.LLink.transport L.ε L.ψ L.δ) = 1
  rw [Work.LLink.cInv_transport_eq_of_eq_zero L.ε L.ψ L.δ L.y L.cInv_ε L.cInv_δ,
    L.cInv_ψ hF hni]

/-- The same, in non-vanishing form, in the exact shape consumed by
`Work.Motivic.not_gen_of_cInv_ne_zero`. -/
theorem cInv_toCr_ne_zero (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) :
    cInv 𝕜 L.y ((L.toCr : Cr 𝕜 3) : (Work.LLink.Affine3 𝕜).BirationalMap
      (Work.LLink.Affine3 𝕜)) ≠ 0 := by
  have h : ((L.toCr : Cr 𝕜 3) : (Work.LLink.Affine3 𝕜).BirationalMap
      (Work.LLink.Affine3 𝕜)) = L.toCremona := by
    simp [CrauderKatzLink.toCr, CrauderKatzLink.toCremona]
  rw [h, L.cInv_toCremona_at_y hF hni]
  norm_num

end CrauderKatzLink

end

end Work.CrauderKatz
