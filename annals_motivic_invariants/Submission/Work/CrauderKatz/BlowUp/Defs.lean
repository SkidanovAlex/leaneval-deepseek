/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.Reduced
import Submission.Work.LLink.cInv_eq_neg_symm
import Submission.Work.CrauderKatz.cInv_eq_one_of_oneSidedLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.Defs` — blow-up machinery, piece 1: the blow-up of the plane

The Crauder–Katz link of `prop:elliptic` of Lin–Shinder is built out of *blow-ups*: the link
`ψ : Q³ ⤏ ℙ³` is the common resolution

```
        T
      /   \
   Bl_C   Bl_{C'}
   /        \
  C ⊂ Q³ --ψ--> ℙ³ ⊃ C'
```

of two blow-ups, one along the elliptic quintic `C ⊂ Q³` and one along `C' = Jac²C ⊂ ℙ³`.  The
input the counting argument consumes — and nothing else — is the *exceptional divisor* structure of
such a blow-up: a birational map with exactly one exceptional divisor on one side and none on the
other, together with the function field of that divisor.

Mathlib has no blow-up of a scheme along a closed subscheme.  This file starts the missing chapter
at its lowest non-trivial rung, the one that already exhibits every phenomenon the L-link needs:

* `PlaneBlowUp 𝕜` — the blow-up `σ : Bl₀ 𝔸² ⤏ 𝔸²` of the affine plane at the origin, recorded
  exactly in the `exDiv` vocabulary of Part A: a scheme `B` over `𝕜`, the birational map `σ`, and
  the *exceptional divisor* `E` (the generic point of the exceptional curve `ℙ¹`), with
  `exDiv σ = {E}` (the blow-up contracts `E` to the origin, so it is not a local isomorphism
  there, and is a local isomorphism everywhere else) and `exDiv σ.symm = ∅` (the inverse map is
  undefined only at the origin, which has codimension two).

The point of recording it in this shape is that it is *precisely* the one-sided configuration
underlying the L-link: `PlaneBlowUp` is the smallest instance of "a birational map with one
exceptional divisor in one direction and none in the other", which is what both blow-ups of
`prop:elliptic` provide (with `ℙ¹` replaced by `ℙ¹ × C` and `ℙ¹ × C'`).

The counting is immediate and is proved below (`cInv_eq_neg_one`, `cInv_ne_zero`): with the base
point taken to be `E` itself,

`cInv 𝕜 E σ = excCount(σ⁻¹) − excCount(σ) = 0 − 1 = −1`,

with no field-theoretic input at all — the mirror image of
`Work.LLink.cInv_eq_one_of_oneSidedLink`.  Note that this *cannot* be turned into a witness for
Theorem 1.2 (1) by itself: the map must be a *self-map* of `𝔸³`, and for a self-map the two
one-sided pictures cancel (`Work.CrauderKatz.cInv_conj_eq`, NOTES §6.3(a)); this is exactly why
`prop:elliptic` needs two blow-ups along two *different* curves.

## Status

`PlaneBlowUp 𝕜` is *not* yet constructed: the construction of `Bl₀𝔸²` (gluing the two charts
`Spec 𝕜[x, t]`, `Spec 𝕜[s, y]`, or the closed subscheme `{y S = x T} ⊂ ℙ¹ × 𝔸²`) together with
the two `exDiv` computations is delegated and carried as `Nonempty (PlaneBlowUp 𝕜)`.  Everything
*above* the construction — the counting, the non-vanishing, and the interface to `cInv` — is proved
here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

namespace Work.CrauderKatz

noncomputable section

/-- The affine plane `𝔸²` over `𝕜`. -/
abbrev Affine2 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := 𝔸(Fin 2; Spec (CommRingCat.of 𝕜))

/-- The affine three-space `𝔸³` over `𝕜`. -/
abbrev Affine3 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := 𝔸(Fin 3; Spec (CommRingCat.of 𝕜))

/-- **The blow-up of the affine plane at the origin**, recorded in the vocabulary of `exDiv`.

`B` is `Bl₀ 𝔸²`, `σ : B ⤏ 𝔸²` is the blow-up, and `E` is the generic point of the exceptional
curve `ℙ¹` (a point of `B` of codimension one).  The two fields say that the blow-up is a *local
isomorphism exactly away from the exceptional curve*:
`exDiv σ = {E}` (the centre has codimension two, so the forward direction sees the exceptional
curve and nothing else) and `exDiv σ.symm = ∅` (the inverse map is undefined only at the origin,
a point of codimension two).

A witness is the classical blow-up: glue the two affine charts `Spec 𝕜[x, t]` (where the point is
`(x, x t)`) and `Spec 𝕜[s, y]` (where the point is `(s y, y)`) along their common open subscheme
`Spec 𝕜[t^{±1}, x] ≅ Spec 𝕜[s^{±1}, y]`, or, equivalently, realise it as the closed subscheme
`{y S = x T}` of `ℙ¹ × 𝔸²`; the map to `𝔸²` is `(x, t) ↦ (x, x t)`, resp. `(s, y) ↦ (s y, y)`.
The exceptional curve is `{x = 0}`, resp. `{y = 0}`; the blow-up agrees with its inverse over
`𝔸² \ {0}`, so both `exDiv` computations reduce to the fact that the blow-up contracts `ℙ¹` to the
origin and is invertible everywhere else.

The two `exDiv` fields are exactly the content the counting layer consumes: one exceptional divisor
in the forward direction, none in the inverse direction.  They say nothing about `ℙ¹`, about the
origin, or about the equation of the blow-up; a caller who needs those (for instance in order to
compute the function field `κ(E)`) must add them.  They are, however, *not* automatic: the
elementary transformation `(x,y) ↦ (x, y/x)` of the affine plane is birational with inverse
`(x,z) ↦ (x, x·z)`, and that inverse is not injective, so it is not a local isomorphism at the
generic point of the line `x = 0`; consequently the elementary transformation has one exceptional
divisor in *both* directions and does not satisfy the fields below. -/
structure PlaneBlowUp (𝕜 : Type) [Field 𝕜] where
  /-- The blow-up `Bl₀ 𝔸²` of the affine plane at the origin. -/
  B : Scheme.{0}
  [irrB : IrreducibleSpace B]
  [overB : B.Over (Spec (CommRingCat.of 𝕜))]
  /-- The blow-up map. -/
  σ : B.BirationalMap (Affine2 𝕜)
  [isOverσ : σ.IsOver (Spec (CommRingCat.of 𝕜))]
  /-- The generic point of the exceptional curve (a point of `B` of codimension one, as
  `coheight_E` below shows). -/
  E : B
  /-- The forward map is a local isomorphism away from the exceptional curve. -/
  exDiv_σ : exDiv σ = {E}
  /-- The inverse map is a local isomorphism everywhere: the centre is of codimension two. -/
  exDiv_σ_symm : exDiv σ.symm = ∅

/-- **The one-sided modification of any variety along a codimension-two centre.**  If a birational
map `σ : B ⤏ X` has exactly one exceptional divisor, `E`, on the source side and none on the target
side — the `exDiv` shape of a blow-up of `X` along a centre of codimension at least two, and of each
half of the Crauder–Katz link — then the coefficient of its invariant at `E` is `-1`.

The target `X` is an arbitrary scheme over `𝕜` (in the application `X = Q³`), so this is the
counting layer a producer of the residual can use directly, `PlaneBlowUp` being the case
`X = 𝔸²`. -/
theorem cInv_eq_neg_one_of_exDiv_singletons (𝕜 : Type) [Field 𝕜]
    {X B : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace B]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [B.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (σ : B.BirationalMap X) (E : B) (hE : exDiv σ = {E}) (hE' : exDiv σ.symm = ∅) :
    cInv 𝕜 E σ = -1 := by
  have h0 : cInv 𝕜 E σ = -cInv 𝕜 E σ.symm := by
    have h := Work.LLink.cInv_eq_neg_symm 𝕜 E (σ.symm)
    rwa [Work.LLink.birationalMap_symm_symm σ] at h
  have h1 : cInv 𝕜 E σ.symm = 1 :=
    cInv_eq_one_of_oneSidedLink 𝕜 σ.symm E hE'
      (by rw [Work.LLink.birationalMap_symm_symm]; exact hE)
  rw [h0, h1]

/-- **The classical blow-up of the affine plane at the origin.**  This is `PlaneBlowUp` together with
the two pieces of geometry that distinguish the honest blow-up from the cheaper one-sided
modifications:

* `f : B ⟶ 𝔸²`, a *morphism* inducing the forward map (`hom_eq`): the blow-up map is a morphism,
  whereas a rational map whose source is a proper open subscheme of `B` (for instance an affine
  chart of `𝔸¹ × ℙ¹`) is not;
* `reduced : IsReduced B`: the blow-up of the plane is smooth at the exceptional curve, whereas the
  square-zero thickening along the exceptional curve constructed in
  `Submission/Work/CrauderKatz/BlowUp/ThickDefs.lean` is not.

Both remaining `exDiv` fields are inherited from the counting shape: `exDiv σ = {E}` (the blow-up is
a local isomorphism exactly away from the exceptional curve) and `exDiv σ.symm = ∅` (its inverse is
undefined only at the origin, of codimension two).  So a witness of `PlaneBlowUpClassical 𝕜` is
(up to the usual `exDiv`-level equivalence) the blow-up of the plane at the origin; see NOTES §10. -/
structure PlaneBlowUpClassical (𝕜 : Type) [Field 𝕜] where
  /-- The blow-up `Bl₀ 𝔸²`. -/
  B : Scheme.{0}
  [irrB : IrreducibleSpace B]
  [overB : B.Over (Spec (CommRingCat.of 𝕜))]
  /-- The birational self-modification of the plane given by the blow-up. -/
  σ : B.BirationalMap (Affine2 𝕜)
  [isOverσ : σ.IsOver (Spec (CommRingCat.of 𝕜))]
  /-- The blow-up morphism. -/
  f : B ⟶ Affine2 𝕜
  /-- The forward map of `σ` is the rational map of the morphism `f`. -/
  hom_eq : σ.hom = f.toRationalMap
  /-- The generic point of the exceptional curve. -/
  E : B
  /-- The forward map is a local isomorphism away from the exceptional curve. -/
  exDiv_σ : exDiv σ = {E}
  /-- The inverse map is a local isomorphism everywhere. -/
  exDiv_σ_symm : exDiv σ.symm = ∅
  /-- The blow-up of the plane is reduced (it is even smooth). -/
  reduced : IsReduced B

namespace PlaneBlowUpClassical

variable {𝕜 : Type} [Field 𝕜] (W : PlaneBlowUpClassical 𝕜)

local instance instIrr : IrreducibleSpace W.B := W.irrB
local instance instOver : W.B.Over (Spec (CommRingCat.of 𝕜)) := W.overB

include W in
/-- The exceptional point is a divisor. -/
theorem coheight_E : Order.coheight W.E = 1 := by
  have h : W.E ∈ exDiv W.σ := by rw [W.exDiv_σ]; exact Set.mem_singleton W.E
  have h' : Order.coheight W.E = 1 ∧ ¬ IsIsoAt W.σ W.E := h
  exact h'.1

include W in
/-- The counting for the classical blow-up: `cInv 𝕜 E σ = -1`. -/
theorem cInv_eq_neg_one : cInv 𝕜 W.E W.σ = -1 :=
  cInv_eq_neg_one_of_exDiv_singletons 𝕜 W.σ W.E W.exDiv_σ W.exDiv_σ_symm

include W in
/-- The classical blow-up of the plane is motivically non-trivial at its exceptional divisor. -/
theorem cInv_ne_zero : cInv 𝕜 W.E W.σ ≠ 0 := by
  rw [W.cInv_eq_neg_one]
  norm_num

/-- Every classical blow-up of the plane is in particular a `PlaneBlowUp`. -/
def toPlaneBlowUp (W : PlaneBlowUpClassical 𝕜) : PlaneBlowUp 𝕜 :=
  { B := W.B
    irrB := W.irrB
    overB := W.overB
    σ := W.σ
    isOverσ := W.isOverσ
    E := W.E
    exDiv_σ := W.exDiv_σ
    exDiv_σ_symm := W.exDiv_σ_symm }

end PlaneBlowUpClassical

/-- **The blow-up of the affine three-space along a coordinate line**, recorded in the `exDiv`
vocabulary and with the function field of its exceptional divisor identified.

The blow-up `σ : Bl_L 𝔸³ ⤏ 𝔸³` of `𝔸³` along a line `L` is the one rung above `PlaneBlowUp`: the
exceptional divisor is a *surface*, `ℙ¹ × 𝔸¹` (rather than a curve), and its generic point `E` has
function field `κ(ℙ¹ × 𝔸¹) = 𝕜(t)(z) = RatFunc (RatFunc 𝕜)` — which is exactly the shape of the
cylinder `cylinderField 𝕜 X = RatFunc (curveField 𝕜 X)` that the Crauder–Katz link assigns to its
exceptional divisors, here for the rational curve `𝔸¹`.  The field `resE` records that
identification; it is the first genuine 3-dimensional instance of the (F1)-input of the residual.

Glue the two charts `Spec 𝕜[x,t,z]` (with `(x,t,z) ↦ (x, x·t, z)`) and `Spec 𝕜[s,y,z]` (with
`(s,y,z) ↦ (s·y, y, z)`) along `Spec 𝕜[t^{±1},z] ≅ Spec 𝕜[s^{±1},z]`; the exceptional divisor is
`{x = 0}`, whose generic point has residue field `Frac 𝕜[t,z] = RatFunc (RatFunc 𝕜)`. -/
structure LineBlowUp (𝕜 : Type) [Field 𝕜] where
  /-- The blow-up of `𝔸³` along a coordinate line. -/
  B : Scheme.{0}
  [irrB : IrreducibleSpace B]
  [overB : B.Over (Spec (CommRingCat.of 𝕜))]
  /-- The blow-up map. -/
  σ : B.BirationalMap (Affine3 𝕜)
  [isOverσ : σ.IsOver (Spec (CommRingCat.of 𝕜))]
  /-- The generic point of the exceptional surface `ℙ¹ × 𝔸¹`. -/
  E : B
  /-- The forward map is a local isomorphism away from the exceptional surface. -/
  exDiv_σ : exDiv σ = {E}
  /-- The inverse map is a local isomorphism everywhere (the centre has codimension two). -/
  exDiv_σ_symm : exDiv σ.symm = ∅
  /-- The exceptional divisor is a cylinder: `κ(E) = 𝕜(t)(z)`. -/
  resE : Work.LLink.ResAlgEquiv 𝕜 E (RatFunc (RatFunc 𝕜)) (algebraMap 𝕜 (RatFunc (RatFunc 𝕜)))

/-- **The one-sided half of the Crauder–Katz link: the blow-up of a threefold along a curve of
genus one, with the *cylinder* function field `RatFunc κ(X.C)` on its exceptional divisor.**

This is the piece of `prop:elliptic` that the (F1) input of `CrauderKatzLink` consumes, stated in
the arithmetic area's vocabulary: `X : GenOneCurve 𝕜` is the elliptic curve `C` of the residual,
`σ : B ⤏ P` is the blow-up of a threefold `P` along (a chart of) `C`, `E` is the generic point of
its exceptional divisor — a `ℙ¹`-bundle over `C` — and `resE` records that the residue field at `E`
is the cylinder `RatFunc κ(C)` over `C`, i.e. exactly `Work.CrauderKatz.cylinderField 𝕜 X`.

A witness is completely affine (no products of schemes are needed): take an affine chart
`Spec R ⊆ X.C` (so that `Frac R ≅ κ(X.C)`), let `P := Spec (R[u,v])` — a threefold over `𝕜`, since
`R` has transcendence degree one over `𝕜` — and let `B` be the blow-up of `P` at the ideal
`(u,v)`, glued from the two charts `Spec (R[u,t])` (where `(u,t) ↦ (u, u·t)`) and `Spec (R[s,v])`
(where `(s,v) ↦ (s·v, v)`) along `Spec (R[t^{±1},u])`; the exceptional divisor is `{u = 0}`, whose
generic point has residue field `Frac (R[t]) ≅ RatFunc (Frac R) ≅ RatFunc κ(X.C)`.  This is the
genus-one case of `LineBlowUp` (where the curve is a line and the cylinder is
`RatFunc (RatFunc 𝕜) = RatFunc κ(𝔸¹)`). -/
structure CylinderBlowUp (𝕜 : Type) [Field 𝕜] (X : Work.Arithmetic.GenOneCurve 𝕜) where
  /-- The blow-up of the threefold `P` along the curve. -/
  B : Scheme.{0}
  [varietyB : MotivicInvariants.Variety 𝕜 B]
  /-- The threefold containing the curve (in the intended witness an affine chart of `X.C` times
  the affine plane). -/
  P : Scheme.{0}
  [varietyP : MotivicInvariants.Variety 𝕜 P]
  /-- The blow-up map. -/
  σ : B.BirationalMap P
  [isOverσ : σ.IsOver (Spec (CommRingCat.of 𝕜))]
  /-- The generic point of the exceptional divisor. -/
  E : B
  /-- The forward map is a local isomorphism away from the exceptional divisor. -/
  exDiv_σ : exDiv σ = {E}
  /-- The inverse map is a local isomorphism everywhere (the curve has codimension two). -/
  exDiv_σ_symm : exDiv σ.symm = ∅
  /-- The exceptional divisor is the cylinder over `X.C`: `κ(E) ≅_𝕜 RatFunc κ(X.C)`. -/
  resE : Work.LLink.ResAlgEquiv 𝕜 E (Work.CrauderKatz.cylinderField 𝕜 X)
    (Work.CrauderKatz.cylResMap 𝕜 X)

namespace CylinderBlowUp

variable {𝕜 : Type} [Field 𝕜] {X : Work.Arithmetic.GenOneCurve 𝕜}

variable (W : CylinderBlowUp 𝕜 X)

local instance instVarietyB : MotivicInvariants.Variety 𝕜 W.B := W.varietyB
local instance instVarietyP : MotivicInvariants.Variety 𝕜 W.P := W.varietyP

include W in
/-- The exceptional point is a divisor. -/
theorem coheight_E : Order.coheight W.E = 1 := by
  have h : W.E ∈ exDiv W.σ := by rw [W.exDiv_σ]; exact Set.mem_singleton W.E
  have h' : Order.coheight W.E = 1 ∧ ¬ IsIsoAt W.σ W.E := h
  exact h'.1

include W in
/-- **The counting for the curve-centre blow-up**: the coefficient of the invariant at the cylinder
`κ(C)(t)` is `-1`. -/
theorem cInv_eq_neg_one : cInv 𝕜 W.E W.σ = -1 :=
  cInv_eq_neg_one_of_exDiv_singletons 𝕜 W.σ W.E W.exDiv_σ W.exDiv_σ_symm

include W in
/-- The genus-one cylinder link is motivically non-trivial at its exceptional divisor. -/
theorem cInv_ne_zero : cInv 𝕜 W.E W.σ ≠ 0 := by
  rw [W.cInv_eq_neg_one]
  norm_num

end CylinderBlowUp

namespace LineBlowUp

variable {𝕜 : Type} [Field 𝕜] (W : LineBlowUp 𝕜)

local instance instIrr : IrreducibleSpace W.B := W.irrB
local instance instOver : W.B.Over (Spec (CommRingCat.of 𝕜)) := W.overB

include W in
/-- The exceptional point is a divisor. -/
theorem coheight_E : Order.coheight W.E = 1 := by
  have h : W.E ∈ exDiv W.σ := by rw [W.exDiv_σ]; exact Set.mem_singleton W.E
  have h' : Order.coheight W.E = 1 ∧ ¬ IsIsoAt W.σ W.E := h
  exact h'.1

include W in
/-- The counting for the 3-fold blow-up: `cInv 𝕜 E σ = -1`. -/
theorem cInv_eq_neg_one : cInv 𝕜 W.E W.σ = -1 :=
  cInv_eq_neg_one_of_exDiv_singletons 𝕜 W.σ W.E W.exDiv_σ W.exDiv_σ_symm

include W in
/-- The blow-up of `𝔸³` along a line is motivically non-trivial at its exceptional divisor. -/
theorem cInv_ne_zero : cInv 𝕜 W.E W.σ ≠ 0 := by
  rw [W.cInv_eq_neg_one]
  norm_num

end LineBlowUp

namespace PlaneBlowUp

variable {𝕜 : Type} [Field 𝕜] (W : PlaneBlowUp 𝕜)

local instance instIrr : IrreducibleSpace W.B := W.irrB
local instance instOver : W.B.Over (Spec (CommRingCat.of 𝕜)) := W.overB

include W in
/-- The exceptional point is a divisor: it has codimension one.  This is *derived* from the
`exDiv` field, not assumed separately. -/
theorem coheight_E : coheight W.E = 1 := by
  have h : W.E ∈ exDiv W.σ := by rw [W.exDiv_σ]; exact Set.mem_singleton W.E
  have h' : coheight W.E = 1 ∧ ¬ IsIsoAt W.σ W.E := h
  exact h'.1

include W in
/-- **The count.**  The blow-up has exactly one exceptional divisor, `E`, and its inverse none, so
the `[κ(E)]`-coefficient of its invariant is `0 − 1 = −1`. -/
theorem cInv_eq_neg_one : cInv 𝕜 W.E W.σ = -1 := by
  have h0 : cInv 𝕜 W.E W.σ = -cInv 𝕜 W.E W.σ.symm := by
    have h := Work.LLink.cInv_eq_neg_symm 𝕜 W.E (W.σ.symm)
    rwa [Work.LLink.birationalMap_symm_symm W.σ] at h
  have h1 : cInv 𝕜 W.E W.σ.symm = 1 :=
    cInv_eq_one_of_oneSidedLink 𝕜 W.σ.symm W.E W.exDiv_σ_symm
      (by rw [Work.LLink.birationalMap_symm_symm]; exact W.exDiv_σ)
  rw [h0, h1]

include W in
/-- The one-sided blow-up of the plane is motivically non-trivial at its exceptional divisor. -/
theorem cInv_ne_zero : cInv 𝕜 W.E W.σ ≠ 0 := by
  rw [W.cInv_eq_neg_one]
  norm_num

end PlaneBlowUp

end

end Work.CrauderKatz
