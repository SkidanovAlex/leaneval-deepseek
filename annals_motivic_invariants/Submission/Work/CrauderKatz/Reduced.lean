/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.Reduced` — the minimal interface to the Crauder–Katz residual

`Work.CrauderKatz.Defs` splits the residual `Work.LLink.CrauderKatzExists 𝕜` into

* `CrauderKatzLink 𝕜 X` — the geometric data: the link `ψ : Q ⤏ P` with its two exceptional
  divisors, the two residue-field presentations (F1), and the transports (TRA);
* `FunctionFieldInput 𝕜` — the field theory: (F2) one-variable function-field stability and
  (F3) curve rigidity + Shinder–Zhang.

This file records the *coarser* but smaller interface `ReducedLink 𝕜 X`, in which the whole field
theory is compressed into the single implication

> `ResEquiv 𝕜 y x → X.torsor.IsIso X.torsor.jacSq.cls`

(`κ(C)(t) ≅ κ(C')(t)` forces `C ≅ Jac²C`), expressed entirely in the arithmetic area's vocabulary
`Torsor.IsIso`/`Torsor.jacSq` — no scheme model of `Jac²C`, no `RatFunc`-presentations of the two
residue fields, and no model `Z` of `C × ℙ¹` are needed.  `ReducedLink` is therefore the shortest
statement of the residual that still implies `Work.LLink.CrauderKatzExists 𝕜`, and a caller who is
willing to take the paper's non-birationality input as a single hypothesis can use it directly;
`CrauderKatzLink.toReducedLink` shows that the finer decomposition of `Defs.lean` implies it, i.e.
the two interfaces are compatible.
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

/-- **The reduced residual.**  A `𝕜`-variety `Q` and a `𝕜`-variety `P` (in the application: `Q³`
and `ℙ³`), a birational map `ψ : Q ⤏ P` over `𝕜` with exactly one exceptional divisor `x` on the
source and exactly one `y` on the target, two transports `ε`, `δ` to affine space with vanishing
invariant, and finally the *single* field-theoretic input

> an isomorphism of the two exceptional divisors' function fields forces `C ≅ Jac²C`.

The base point of the invariant is `y` itself, so no separate base scheme is needed. -/
structure ReducedLink (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) where
  /-- The source threefold of the link (`Q³` in the application). -/
  Q : Scheme.{0}
  [varietyQ : Variety 𝕜 Q]
  /-- The target threefold of the link (`ℙ³` in the application). -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- The Crauder–Katz transformation. -/
  ψ : Q.BirationalMap P
  [isOverψ : ψ.IsOver (Spec (.of 𝕜))]
  /-- The exceptional divisor of `ψ` on the source. -/
  x : Q
  /-- The exceptional divisor of `ψ⁻¹` on the target. -/
  y : P
  exDiv_ψ : exDiv ψ = {x}
  exDiv_ψ_symm : exDiv ψ.symm = {y}
  /-- **The field-theoretic input**: `κ(y) ≅_𝕜 κ(x)` would force `C ≅ Jac²C`.  This is the
  contrapositive form of (F1)+(F2)+(F3) of `Defs.lean`, in the arithmetic area's vocabulary
  (`Torsor.IsIso`, `Torsor.jacSq`). -/
  cylinderStability : ResEquiv 𝕜 y x → X.torsor.IsIso X.torsor.jacSq.cls
  /-- The birational identification `𝔸³ ⤏ Q`. -/
  ε : (Work.LLink.Affine3 𝕜).BirationalMap Q
  [isOverε : ε.IsOver (Spec (.of 𝕜))]
  /-- The birational identification `P ⤏ 𝔸³`. -/
  δ : P.BirationalMap (Work.LLink.Affine3 𝕜)
  [isOverδ : δ.IsOver (Spec (.of 𝕜))]
  cInv_ε : cInv 𝕜 y ε = 0
  cInv_δ : cInv 𝕜 y δ = 0

namespace ReducedLink

variable {X : GenOneCurve 𝕜} (R : ReducedLink 𝕜 X)

local instance instVarietyQ : Variety 𝕜 R.Q := R.varietyQ
local instance instVarietyP : Variety 𝕜 R.P := R.varietyP
local instance instIsOverψ : (R.ψ).IsOver (Spec (.of 𝕜)) := R.isOverψ
local instance instIsOverε : (R.ε).IsOver (Spec (.of 𝕜)) := R.isOverε
local instance instIsOverδ : (R.δ).IsOver (Spec (.of 𝕜)) := R.isOverδ

/-- The two exceptional divisors of a reduced link have non-isomorphic function fields, by the
field-theoretic input and Shinder–Zhang's `C ≇ Jac²C` (`X.NotIsoJacSq`). -/
theorem not_resEquiv_yx (hni : X.NotIsoJacSq) : ¬ ResEquiv 𝕜 R.y R.x :=
  fun h => hni (R.cylinderStability h)

/-- The `[κ(ℙ¹ × C)]`-coefficient of the reduced link is `1`. -/
theorem cInv_eq_one (hni : X.NotIsoJacSq) : cInv 𝕜 R.y R.ψ = 1 :=
  Work.LLink.cInv_eq_one_of_exDiv_eq_singletons R.y R.ψ R.exDiv_ψ R.exDiv_ψ_symm
    (fun h => R.not_resEquiv_yx hni (Work.Motivic.ResEquiv.symm h))
    (Work.Motivic.ResEquiv.refl 𝕜 R.y)

/-- The reduced link is motivically non-trivial. -/
theorem cInv_ne_zero (hni : X.NotIsoJacSq) : cInv 𝕜 R.y R.ψ ≠ 0 := by
  rw [R.cInv_eq_one hni]
  norm_num

/-- The transported Crauder–Katz transformation of the reduced link. -/
noncomputable def toCremona : (Work.LLink.Affine3 𝕜).BirationalMap (Work.LLink.Affine3 𝕜) :=
  Work.LLink.transport R.ε R.ψ R.δ

/-- Its invariant is `1` as well. -/
theorem cInv_toCremona (hni : X.NotIsoJacSq) : cInv 𝕜 R.y R.toCremona = 1 := by
  change cInv 𝕜 R.y (Work.LLink.transport R.ε R.ψ R.δ) = 1
  rw [Work.LLink.cInv_transport_eq_of_eq_zero R.ε R.ψ R.δ R.y R.cInv_ε R.cInv_δ,
    R.cInv_eq_one hni]

end ReducedLink

variable {X : GenOneCurve 𝕜}

/-- **The reduced residual gives `Work.LLink.QuadroCubicLink`.** -/
noncomputable def ReducedLink.toQuadroCubicLink (R : ReducedLink 𝕜 X) (hni : X.NotIsoJacSq) :
    Work.LLink.QuadroCubicLink 𝕜 X :=
  letI : Variety 𝕜 R.Q := R.varietyQ
  letI : Variety 𝕜 R.P := R.varietyP
  letI : (R.ψ).IsOver (Spec (.of 𝕜)) := R.isOverψ
  letI : (R.ε).IsOver (Spec (.of 𝕜)) := R.isOverε
  letI : (R.δ).IsOver (Spec (.of 𝕜)) := R.isOverδ
  { notIsoJacSq := hni
    Z := R.P
    z₀ := R.y
    Q := R.Q
    P := R.P
    ψ := R.ψ
    x := R.x
    y := R.y
    exDiv_ψ := R.exDiv_ψ
    exDiv_ψ_symm := R.exDiv_ψ_symm
    ε := R.ε
    δ := R.δ
    resEquiv_y := Work.Motivic.ResEquiv.refl 𝕜 R.y
    not_resEquiv_yx := R.not_resEquiv_yx hni
    cInv_ε := R.cInv_ε
    cInv_δ := R.cInv_δ }

/-- **The reduced residual, in existence form.** -/
def ReducedLinkExists (𝕜 : Type) [Field 𝕜] : Prop :=
  ∀ X : GenOneCurve 𝕜, X.index = 5 → X.NotIsoJacSq → Nonempty (ReducedLink 𝕜 X)

/-- **`Work.LLink.CrauderKatzExists` from the reduced residual.** -/
theorem crauderKatzExists_of_reducedLinkExists (h : ReducedLinkExists 𝕜) :
    Work.LLink.CrauderKatzExists 𝕜 :=
  fun X hindex hni => (h X hindex hni).map (ReducedLink.toQuadroCubicLink · hni)

/-- The finer decomposition of `Defs.lean` (link data + (F1) + (TRA) together with (F2)+(F3))
implies the reduced interface: from a `CrauderKatzLink` and the function-field input one builds a
`ReducedLink` whose stability input is the contrapositive of the derived
`CrauderKatzLink.not_resEquiv_yx`.  So the reduced interface is not *stronger* than the paper's
decomposition — it is the same residual, stated with fewer moving parts. -/
noncomputable def CrauderKatzLink.toReducedLink (L : CrauderKatzLink 𝕜 X)
    (hF : FunctionFieldInput 𝕜) (hni : X.NotIsoJacSq) : ReducedLink 𝕜 X :=
  letI : Variety 𝕜 L.Q := L.varietyQ
  letI : Variety 𝕜 L.P := L.varietyP
  letI : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
  letI : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
  letI : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ
  { Q := L.Q
    P := L.P
    ψ := L.ψ
    x := L.x
    y := L.y
    exDiv_ψ := L.exDiv_ψ
    exDiv_ψ_symm := L.exDiv_ψ_symm
    cylinderStability := fun h => absurd h (L.not_resEquiv_yx hF hni)
    ε := L.ε
    δ := L.δ
    cInv_ε := L.cInv_ε
    cInv_δ := L.cInv_δ }

end

end Work.CrauderKatz
