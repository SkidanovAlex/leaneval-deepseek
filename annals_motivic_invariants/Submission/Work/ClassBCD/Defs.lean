/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.ClassBCD
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessTwist.All
import Submission.Work.SilvermanReduction.All
import Submission.Work.TorsorExistence.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.ClassBCD` — the function-field classes (b), (c), (d) of the motivic chain

This area closes the **function-field classes** of Lin–Shinder, *Motivic invariants of birational
maps*, Annals of Math. **199** (1), 2024, Theorem 1.2 (1) (b)–(d), at the level at which the
delivered `Work.Twist` / `Work.PointlessTwist` chain consumes them: the **arithmetic half**
`Work.PointlessTwist.HasPointlessTwist 𝕜` for `𝕜 = X.functionField` (a positive-dimensional
`𝔽`-variety `X`).

The concrete data is the one the paper's proof uses:

* the **constant** elliptic curve `E(c) : y² + (1-c)xy - cy = x³ - cx²` (Mathlib's Tate normal
  form `Work.TorsorExistence.Tate.tateCurve c`, `c ∈ 𝔽` a good parameter) base changed to `𝕜`,
  with the marked point `(0,0)` of exact order `5` — this is `Work.PointlessTwist.ConstantTateData`;
* a **cyclic quintic extension** `L/𝕜` — for the Kummer cases `L.L = 𝕜(s)` with `s ^ 5 = t`
  (`Work.TorsorExistence.existsCyclicExtension_of_zeta5`, `ζ₅ ∈ 𝔽`, `t ∉ 𝕜 ^ 5`), for the
  characteristic-`5` cases the Artin–Schreier extension `s ^ 5 - s = t`
  (`existsCyclicExtension_of_charP_five`);
* the **place obstruction**: an additive, `σ`-invariant map out of `E(L)` which does not kill the
  marked point (`Work.PointlessTwist.HasReductionPlace`, produced by a place of `L.L` through the
  Silverman reduction map, `Work.SilvermanReduction.hasReductionPlace_of_localModelData`).

The **residual** of each class is `FunctionFieldResidual 𝔽 𝕜`: the existence of this concrete data
together with the place obstruction.  Two forms of the obstruction are provided, and the relation
between them is proved:

* `ConstantTwistData.HasConstantsOnly` — the *trivial Galois action* form
  `E(𝔽(s)) = E(𝔽)`, i.e. every `L.L`-point of the constant curve is constant
  (`Work.PointlessTwist.ConstantsOnly`, the classical shape of the residual);
* `ConstantTwistData.HasPlaceObstruction` — the *place* form
  `Work.PointlessTwist.HasReductionPlace`, which is the form the chain consumes.

`HasConstantsOnly ⟹ HasPlaceObstruction` is proved here
(`ConstantTwistData.hasPlaceObstruction_of_constantsOnly`), and it is this implication which closes
the classes completely at `𝕜 = 𝔽(t)` (`Work.ClassBCD.RatFunc`), where the classical
`E(𝔽(t)) = E(𝔽)` is available from `Work.Genus`.

## Main results

* `Work.ClassBCD.ConstantTwistData` — the concrete data over `𝔽 → 𝕜` with a chosen parameter `c`.
* `Work.ClassBCD.FunctionFieldResidual 𝔽 𝕜` — the residual (a `Type`, hence a structure: it
  carries the `DecidableEq 𝕜` needed by Mathlib's group law).
* `Work.ClassBCD.FunctionFieldResidual.hasPointlessTwist` — **the residual gives the arithmetic
  half**: `Work.PointlessTwist.HasPointlessTwist 𝕜`.
* `Work.ClassBCD.ConstantTwistData.pointlessOf_of_constantsOnly`,
  `...hasPlaceObstruction_of_constantsOnly` — the two forms of the obstruction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.ClassBCD

noncomputable section

/-! ## 1. The concrete data -/

/-- **The concrete data of the function-field classes (b), (c), (d).**

Over a field `𝕜` with a chosen structure map `𝔽 → 𝕜` (the `Algebra 𝔽 𝕜` instance):

* `c : 𝔽` — a parameter with a nonsingular Tate normal form and `j ≠ 1728`
  (`hΔ`, `hj`, in the characteristic-free form `c₄³ ≠ 1728·Δ`);
* `d : ConstantTateData 𝔽 𝕜 c` — the **constant** Tate model base changed to `𝕜`, marked by the
  base change of `(0,0)` (`Work.PointlessTwist.Constants.nonempty_constantTateData` produces it);
* `L : CyclicExtension 𝕜 5` — the cyclic quintic extension of the twist.

The instances `DecidableEq L.L`, `Algebra 𝔽 L.L`, `IsScalarTower 𝔽 𝕜 L.L` are recorded as fields so
that the chain `ConstantsOnly → PointlessOf` (`Work.PointlessTwist.bridge`) applies verbatim. -/
structure ConstantTwistData (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (𝕜 : Type) [Field 𝕜]
    [DecidableEq 𝕜] [Algebra 𝔽 𝕜] (c : 𝔽) where
  /-- The Tate parameter is good: the Tate normal form is nonsingular. -/
  hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0
  /-- `j ≠ 1728`, in the characteristic-free form `c₄ ^ 3 ≠ 1728 * Δ`. -/
  hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ
  /-- The constant Tate model over `𝕜`. -/
  d : Work.PointlessTwist.ConstantTateData 𝔽 𝕜 c
  /-- The cyclic quintic extension of `𝕜`. -/
  L : Work.PointlessTwist.CyclicExtension 𝕜 5
  /-- Mathlib's group law on affine points needs a `DecidableEq` instance. -/
  [decEqL : DecidableEq L.L]
  /-- The top field of the extension is an `𝔽`-algebra. -/
  [algebraL : Algebra 𝔽 L.L]
  /-- The tower `𝔽 → 𝕜 → L.L`. -/
  [towerL : IsScalarTower 𝔽 𝕜 L.L]

attribute [instance] ConstantTwistData.decEqL ConstantTwistData.algebraL ConstantTwistData.towerL

namespace ConstantTwistData

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
  [Algebra 𝔽 𝕜] {c : 𝔽} (t : ConstantTwistData 𝔽 𝕜 c)

/-- The quintic twist of the concrete data, whose class in `H¹(ℤ/5, E(L))` is decided by the
place obstruction. -/
abbrev twist : Work.PointlessTwist.QuinticTwist 𝕜 := Work.PointlessTwist.twistOf t.d.C₅ t.L

/-- The curve of the twist is the constant Tate model over `𝕜`: recorded for rewriting. -/
theorem curve_eq : t.twist.E = (Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜 := t.d.E_eq

/-! ## 2. The two forms of the obstruction -/

/-- **The `ConstantsOnly` form of the obstruction.**  Every `L.L`-point of the constant curve
`Tate.tateCurve c` is the base change of an `𝔽`-point — the classical `E(𝔽(s)) = E(𝔽)` of the
function-field classes, i.e. the statement that there is no non-constant morphism `ℙ¹ → E`
(an elliptic curve is not unirational).  In this form the Galois generator acts trivially on
`E(L)` and the twist is pointless. -/
def HasConstantsOnly : Prop :=
  Work.PointlessTwist.ConstantsOnly 𝔽 (Work.TorsorExistence.Tate.tateCurve c) t.L.L

/-- **The place form of the obstruction.**  An additive, `σ`-invariant map out of `E(L)` which does
not kill the marked point (`Work.PointlessTwist.HasReductionPlace`): this is what a place of `L.L`
with residue field fixed pointwise by `σ` produces (the reduction map on points, Silverman *AEC*
VII.2.1–2.2).  It is the form the chain `Work.PointlessTwist` consumes. -/
def HasPlaceObstruction : Prop := Work.PointlessTwist.HasReductionPlace t.twist

/-- **The `ConstantsOnly` form gives the residual**: the Galois generator acts trivially on `E(L)`,
so `P ≠ 0` is not a coboundary. -/
theorem pointlessOf_of_constantsOnly (h : t.HasConstantsOnly) :
    Work.PointlessTwist.PointlessOf t.d.C₅ t.L :=
  Work.PointlessTwist.pointlessOf_of_trivialGaloisAction t.d.C₅ t.L
    (Work.PointlessTwist.bridge.trivialGaloisAction_of_constantsOnly c t.d t.L h)

/-- **The `ConstantsOnly` form gives the place form.** -/
theorem hasPlaceObstruction_of_constantsOnly (h : t.HasConstantsOnly) : t.HasPlaceObstruction :=
  (Work.PointlessTwist.hasReductionPlace_iff_hasInvariantObstruction t.twist).mpr
    (Work.PointlessTwist.hasInvariantObstruction_of_pointless t.d.C₅ t.L
      (t.pointlessOf_of_constantsOnly h))

/-- **A place of `L.L` gives the obstruction**: the local-model data of the Silverman reduction
chapter (a discrete valuation ring inside `L.L` at which the curve has good reduction, preserved by
`σ`, with `σ` acting trivially on the residue field, and with the marked point reducing
non-trivially) produces `HasPlaceObstruction` through the reduction map on points. -/
theorem hasPlaceObstruction_of_localModelData
    (h : Work.SilvermanReduction.LocalModelData t.twist) : t.HasPlaceObstruction :=
  Work.SilvermanReduction.hasReductionPlace_of_localModelData t.twist h

/-- **The place form gives `PointlessOf` at the concrete data.** -/
theorem pointlessOf_of_hasPlaceObstruction (h : t.HasPlaceObstruction) :
    Work.PointlessTwist.PointlessOf t.d.C₅ t.L :=
  Work.PointlessTwist.pointlessOf_of_hasReductionPlace t.d.C₅ t.L h

/-- **The place form gives the arithmetic half of the chain**, i.e. the pointlessness of a quintic
twist over `𝕜`. -/
theorem hasPointlessTwist_of_hasPlaceObstruction (h : t.HasPlaceObstruction) :
    Work.PointlessTwist.HasPointlessTwist 𝕜 :=
  ⟨t.twist, Work.PointlessTwist.pointless_of_hasReductionPlace t.twist h⟩

end ConstantTwistData

/-! ## 3. The residual of the function-field classes -/

/-- **The residual of the function-field classes (b), (c), (d).**  The concrete data
(`c : 𝔽`, the constant Tate model over `𝕜`, a cyclic quintic extension `L/𝕜`, the `𝔽`-algebra
structure on `L.L`) together with the **place obstruction** which decides the class of the twist.

The `DecidableEq 𝕜` instance is a field of the structure (it is a Mathlib artefact of the group law
on affine points), so that statements about `X.functionField` do not have to carry it.

The residual is *not* an extra hypothesis on the mathematics of the chain: it is the concrete data
together with the local obstruction at a place of `L.L`, i.e. exactly the input of the paper's
route (ii)/(iii) for these classes.  It is shown to be *provable* at `𝕜 = 𝔽(t)`
(`Work.ClassBCD.RatFunc`), where the classical `E(𝔽(t)) = E(𝔽)` supplies
`HasConstantsOnly`. -/
structure FunctionFieldResidual (𝔽 : Type) [Field 𝔽] (𝕜 : Type) [Field 𝕜]
    [Algebra 𝔽 𝕜] where
  /-- Mathlib's group law needs a `DecidableEq` on the field of constants. -/
  [decF : DecidableEq 𝔽]
  /-- Mathlib's group law needs a `DecidableEq` on the function field. -/
  [decK : DecidableEq 𝕜]
  /-- The Tate parameter. -/
  c : 𝔽
  /-- The concrete data. -/
  data : ConstantTwistData 𝔽 𝕜 c
  /-- The place obstruction at the concrete data. -/
  place : data.HasPlaceObstruction

namespace FunctionFieldResidual

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- **The residual gives the arithmetic half** of the chain in the `DecidableEq`-free form
(the residual carries its own `DecidableEq 𝕜`, so that statements about `X.functionField` do not
have to mention it). -/
theorem exists_hasPointlessTwist (h : FunctionFieldResidual 𝔽 𝕜) :
    ∃ dec : DecidableEq 𝕜, @Work.PointlessTwist.HasPointlessTwist 𝕜 _ dec := by
  letI := h.decF
  letI := h.decK
  exact ⟨h.decK, h.data.hasPointlessTwist_of_hasPlaceObstruction h.place⟩

end FunctionFieldResidual

/-! ## 4. The two provable forms of the residual

The residual `FunctionFieldResidual` asks for the place obstruction directly.  It is fed by either of
the two forms in which the obstruction is *proved* in practice:

* `FunctionFieldConstantsOnlyDatum` — the classical `E(𝔽(s)) = E(𝔽)` at the top field of the
  extension (the constant-curve/trivial-action route, the paper's route (iii)); this is the form
  which is available at `𝕜 = 𝔽(t)`, where `L.L` is again a rational function field;
* `FunctionFieldPlaceDatum` — a **place** of `L.L` (a discrete valuation ring inside `L.L` with
  `IsFractionRing R L.L`), at which the curve has good reduction, which `σ` preserves and on whose
  residue field `σ` acts trivially, and at which the marked point reduces non-trivially
  (`Work.SilvermanReduction.LocalModelData`); this is the honest "reduce modulo a place" input of
  the paper's proof, and it is *strictly stronger* than the residual.
-/

/-- **The `ConstantsOnly` form of the residual.**  The concrete data together with the classical
statement `E(𝔽(s)) = E(𝔽)` for the constant Tate normal form at the top field of the extension. -/
structure FunctionFieldConstantsOnlyDatum (𝔽 : Type) [Field 𝔽] (𝕜 : Type) [Field 𝕜]
    [Algebra 𝔽 𝕜] where
  /-- Mathlib's group law needs a `DecidableEq` on the field of constants. -/
  [decF : DecidableEq 𝔽]
  /-- Mathlib's group law needs a `DecidableEq` on the function field. -/
  [decK : DecidableEq 𝕜]
  /-- The Tate parameter. -/
  c : 𝔽
  /-- The concrete data. -/
  data : ConstantTwistData 𝔽 𝕜 c
  /-- The classical input `E(𝔽(s)) = E(𝔽)`. -/
  constantsOnly : data.HasConstantsOnly

namespace FunctionFieldConstantsOnlyDatum

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- **The `ConstantsOnly` form gives the residual.** -/
def toResidual (h : FunctionFieldConstantsOnlyDatum 𝔽 𝕜) : FunctionFieldResidual 𝔽 𝕜 := by
  letI := h.decF
  letI := h.decK
  exact FunctionFieldResidual.mk h.c h.data
    (h.data.hasPlaceObstruction_of_constantsOnly h.constantsOnly)

end FunctionFieldConstantsOnlyDatum

/-- **The place form of the residual.**  The concrete data together with a discrete valuation ring
inside `L.L` at which the reduction map of Silverman *AEC* VII.2.1–2.2 decides the class of the
twist. -/
structure FunctionFieldPlaceDatum (𝔽 : Type) [Field 𝔽] (𝕜 : Type) [Field 𝕜]
    [Algebra 𝔽 𝕜] where
  /-- Mathlib's group law needs a `DecidableEq` on the field of constants. -/
  [decF : DecidableEq 𝔽]
  /-- Mathlib's group law needs a `DecidableEq` on the function field. -/
  [decK : DecidableEq 𝕜]
  /-- The Tate parameter. -/
  c : 𝔽
  /-- The concrete data. -/
  data : ConstantTwistData 𝔽 𝕜 c
  /-- The place of `L.L`, at which the reduction decides the class. -/
  localModel : Work.SilvermanReduction.LocalModelData data.twist

namespace FunctionFieldPlaceDatum

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- **The place form gives the residual** (by the reduction map on the points of the curve). -/
def toResidual (h : FunctionFieldPlaceDatum 𝔽 𝕜) : FunctionFieldResidual 𝔽 𝕜 := by
  letI := h.decF
  letI := h.decK
  exact FunctionFieldResidual.mk h.c h.data
    (h.data.hasPlaceObstruction_of_localModelData h.localModel)

end FunctionFieldPlaceDatum


end

end Work.ClassBCD
