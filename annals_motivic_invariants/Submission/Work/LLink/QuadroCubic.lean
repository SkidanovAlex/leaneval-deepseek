import Mathlib
import Submission.Work.Arithmetic.LLink
import Submission.Work.LLink.Count
import Submission.Work.LLink.Transport
import Submission.Work.LLink.not_resEquiv_of_ringEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.LLink.QuadroCubic` — the Crauder–Katz quadro-cubic L-link

This file records the geometric input of §'Elliptic curves' of Lin–Shinder,
`Motivic invariants of birational maps` (Annals 199 (1), 2024), in the shape in which the
theorem-level argument consumes it, and derives from it the exact value of the coefficient
`cInv` of Part A.

## The geometric input

Proposition `prop:elliptic` of the paper produces, from a genus-one curve `C` with a divisor of
degree five, the smooth projective L-link

```
        T
      /   \
   Bl_C   Bl_{C'}
   /        \
  C ⊂ Q³ --ψ--> ℙ³ ⊃ C'
```

with `C' = Jac²(C)`, `Q³` a smooth quadric threefold, `ψ` the Crauder–Katz quadro-cubic
transformation.  Its two exceptional divisors are birational to
`ℙ¹ × C'` (on the `Q³`-side) and `ℙ¹ × C` (on the `ℙ³`-side).  By Lemma `lemma:L-link` (2),
taking `z₀` to be the generic point of `C × ℙ¹` (so `κ(z₀) = κ(C)(t)`),

`c(ψ) = [ℙ¹ × C] − [ℙ¹ × C']`,

whose `[κ(C)(t)]`-coefficient is `1 − 0 = 1` — nonzero because `κ(C)(t) ≇ κ(C')(t)`.

## The arithmetic input comes from `Work.Arithmetic`

The curve `C` is *not* invented here: it is a parameter `X : Work.Arithmetic.GenOneCurve 𝕜`,
i.e. a genus-one curve over `𝕜` realised as a scheme, with its class in the Weil–Châtelet group
and the bridges `cls = 1 ↔ C(𝕜) ≠ ∅`, `cls ^ n = 1 ↔ ∃ D, deg D = n`.  The four field-class
theorems of `Submission/Work/LLink/Classes.lean` consume the named arithmetic input
`Work.Arithmetic.HasLLinkCurve 𝕜` (the paper's `lem:torsors`) through that area's
`Work.Arithmetic.llink_tors_*`, and all that is left over is the single geometric residual
`Work.LLink.CrauderKatzExists 𝕜` defined below.

## What is an *input* and what is *proved*

Nothing about cubic threefolds, blow-ups, Jacobians or projective space is available in Mathlib,
so the *existence* of the above configuration is a hypothesis, recorded as the structure
`QuadroCubicLink 𝕜 X`.  Each of its fields is a separately named residual:

* `notIsoJacSq : X.NotIsoJacSq` — the arithmetic input `C ≇ Jac²C` (Shinder–Zhang Lemma 2.7);
* `exDiv_ψ : exDiv ψ = {x}`, `exDiv_ψ_symm : exDiv ψ.symm = {y}` — the residual map `ψ` has
  exactly the two exceptional divisors of the link, `x` (birational to `ℙ¹ × C'`) and `y`
  (birational to `ℙ¹ × C`);
* `resEquiv_y : ResEquiv 𝕜 y z₀` — `κ(y) ≅_𝕜 κ(z₀)`, i.e. both are the function field `κ(C)(t)`
  of `ℙ¹ × C`;
* `not_resEquiv_yx : ¬ ResEquiv 𝕜 y x` — `κ(C)(t) ≇_𝕜 κ(C')(t)`;
* `cInv_ε : cInv 𝕜 z₀ ε = 0`, `cInv_δ : cInv 𝕜 z₀ δ = 0` — the transports to affine space are
  strongly birational.

Everything *on top* of those inputs — the transport, its membership in `Cr 𝕜 3`, additivity, and
the exact count `1 − 0` — is proved, sorry-free, in `Count.lean` and `Transport.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order
open Work.Arithmetic (GenOneCurve)

namespace Work.LLink

/-- **The Crauder–Katz quadro-cubic L-link, transported to affine space.**

The parameter `X : GenOneCurve 𝕜` is the arithmetic input (a genus-one curve over `𝕜` realised
as a scheme); `X.NotIsoJacSq` is the paper's `C ≇ Jac²C`.  Everything else is the geometric and
transport data described in the module docstring. -/
structure QuadroCubicLink (𝕜 : Type) [Field 𝕜] (X : GenOneCurve 𝕜) where
  /-- The arithmetic input `C ≇ Jac²C` (Shinder–Zhang Lemma 2.7, guarded by `j ≠ 1728`). -/
  notIsoJacSq : X.NotIsoJacSq
  /-- The `𝕜`-variety `Z` modelling `C × ℙ¹`. -/
  Z : Scheme.{0}
  [overZ : Z.Over (Spec (.of 𝕜))]
  /-- The base point `z₀` of the invariant: the generic point of `C × ℙ¹`. -/
  z₀ : Z
  /-- The source threefold `Q³` of the link (a smooth quadric threefold). -/
  Q : Scheme.{0}
  [varietyQ : Variety 𝕜 Q]
  /-- The target threefold `ℙ³` of the link. -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- The Crauder–Katz birational map `ψ : Q³ ⤏ ℙ³`. -/
  ψ : Q.BirationalMap P
  [isOverψ : ψ.IsOver (Spec (.of 𝕜))]
  /-- The exceptional divisor of `ψ` on the source (birational to `ℙ¹ × C'`). -/
  x : Q
  /-- The exceptional divisor of `ψ⁻¹` on the target (birational to `ℙ¹ × C`). -/
  y : P
  /-- `x` is the only exceptional divisor of `ψ`. -/
  exDiv_ψ : exDiv ψ = {x}
  /-- `y` is the only exceptional divisor of `ψ⁻¹`. -/
  exDiv_ψ_symm : exDiv ψ.symm = {y}
  /-- The birational identification `𝔸³ ⤏ Q³`. -/
  ε : (Affine3 𝕜).BirationalMap Q
  [isOverε : ε.IsOver (Spec (.of 𝕜))]
  /-- The birational identification `ℙ³ ⤏ 𝔸³`. -/
  δ : P.BirationalMap (Affine3 𝕜)
  [isOverδ : δ.IsOver (Spec (.of 𝕜))]
  /-- `κ(y) ≅ κ(z₀)`: both are the function field `κ(C)(t)`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- `κ(y) ≇ κ(x)`: the function fields `κ(C)(t)` and `κ(C')(t)` of the two exceptional
  divisors are not `𝕜`-isomorphic.  This is the *only* field-theoretic input; combined with
  `resEquiv_y` it gives `κ(x) ≇ κ(z₀)`, see `not_resEquiv_x`. -/
  not_resEquiv_yx : ¬ ResEquiv 𝕜 y x
  /-- The transport `ε : 𝔸³ ⤏ Q³` contributes nothing (`Q³` is strongly rational). -/
  cInv_ε : cInv 𝕜 z₀ ε = 0
  /-- The transport `δ : ℙ³ ⤏ 𝔸³` contributes nothing. -/
  cInv_δ : cInv 𝕜 z₀ δ = 0

/-- **(GEO) — the single geometric residual.**

`CrauderKatzExists 𝕜` is the residual content of Proposition `prop:elliptic` *after* the
arithmetic input has been supplied: for every genus-one curve `X` over `𝕜` of index `5` (the
output of the paper's Lemma `lem:torsors`, produced in `Work.Arithmetic` by Clark–Lacy /
Lang–Tate) which is not isomorphic to `Jac²X`, the Crauder–Katz quadro-cubic construction
produces the L-link `QuadroCubicLink 𝕜 X`, transported to affine space.

Mathlib has no projective space, no blow-ups, no genus and no Jacobians, so this residual is not
formalised; everything downstream of it is.  It is stated uniformly over `𝕜` because the
construction is field-independent; the four field classes differ only in which fields it is
applied to (`𝕜`, or `X.functionField`). -/
def CrauderKatzExists (𝕜 : Type) [Field 𝕜] : Prop :=
  ∀ X : GenOneCurve 𝕜, X.index = 5 → X.NotIsoJacSq → Nonempty (QuadroCubicLink 𝕜 X)

namespace QuadroCubicLink

variable {𝕜 : Type} [Field 𝕜] {X : GenOneCurve 𝕜}

/-- The transported Cremona map of an L-link: an explicit element of `Cr 𝕜 3`. -/
noncomputable def transportCr (L : QuadroCubicLink 𝕜 X) : Cr 𝕜 3 :=
  letI : Variety 𝕜 L.Q := L.varietyQ
  letI : Variety 𝕜 L.P := L.varietyP
  letI : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
  letI : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
  letI : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ
  Work.LLink.transportCr L.ε L.ψ L.δ

/-- The underlying birational self-map of `𝔸³`. -/
noncomputable def toBirationalMap (L : QuadroCubicLink 𝕜 X) :
    (Affine3 𝕜).BirationalMap (Affine3 𝕜) :=
  ((L.transportCr : Cr 𝕜 3) : (Affine3 𝕜).BirationalMap (Affine3 𝕜))

/-- **The invariant coefficient of the transported L-link.**  This is the number whose
non-vanishing Theorem 1.2 (1) needs, and it is `1`.

Technically, the definition binds the base-scheme structure `L.Z.Over (Spec 𝕜)` by `letI` so that
the whole development of the link can be phrased about the *bundled* data `L` without the caller
having to re-supply the instances of the individual fields. -/
noncomputable def inv (L : QuadroCubicLink 𝕜 X) : ℤ :=
  letI : L.Z.Over (Spec (.of 𝕜)) := L.overZ
  cInv 𝕜 L.z₀ L.toBirationalMap

/-- The same invariant coefficient, but with the base point taken to be the exceptional divisor
`y` of `ψ⁻¹` (a point of `ℙ³`) instead of a point of a model of `C × ℙ¹`.  By
`cInv_congr_of_resEquiv` the two agree whenever the base points have isomorphic residue fields. -/
noncomputable def invAtY (L : QuadroCubicLink 𝕜 X) : ℤ :=
  letI : Variety 𝕜 L.Q := L.varietyQ
  letI : Variety 𝕜 L.P := L.varietyP
  cInv 𝕜 L.y L.ψ

section Aux

variable (L : QuadroCubicLink 𝕜 X)

local instance instVarietyQ : Variety 𝕜 L.Q := L.varietyQ
local instance instVarietyP : Variety 𝕜 L.P := L.varietyP
local instance instOverZ : L.Z.Over (Spec (.of 𝕜)) := L.overZ
local instance instIsOverε : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
local instance instIsOverψ : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
local instance instIsOverδ : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ

/-- **How to produce the field-theoretic input.**  To discharge `not_resEquiv_yx` it suffices to
exhibit two `𝕜`-fields `A`, `B` — intended to be the function fields `κ(ℙ¹ × C)` and
`κ(ℙ¹ × C')` — together with `κ(y) ≅ A`, `κ(x) ≅ B` and the failure of `A ≅ B` as `𝕜`-algebras.
The remaining work is then exactly the one-variable function-field step
`κ(C)(t) ≅ κ(C')(t) ⟹ C` birational to `C'`, which combined with `X.NotIsoJacSq` gives `h`. -/
theorem not_resEquiv_yx_of_functionFields {A B : Type} [Field A] [Field B]
    (φ : 𝕜 →+* A) (ψ : 𝕜 →+* B) (hy : ResAlgEquiv 𝕜 L.y A φ) (hx : ResAlgEquiv 𝕜 L.x B ψ)
    (h : ¬ ∃ e : A ≃+* B, e.toRingHom.comp φ = ψ) : ¬ ResEquiv 𝕜 L.y L.x :=
  not_resEquiv_of_ringEquiv φ ψ hx hy h

/-- The second exceptional divisor, as a point of the target, carries the function field
`κ(C)(t)`; consequently it is *not* in the class of the first one. -/
theorem not_resEquiv_xy : ¬ ResEquiv 𝕜 L.x L.y := fun h =>
  L.not_resEquiv_yx (Work.Motivic.ResEquiv.symm h)

/-- `κ(x) ≇ κ(z₀)`: the `ℙ¹ × C'`-divisor does not match the base point.  This is exactly the
input that makes the second `excCount` vanish, and it is *derived* here from the two fields
`not_resEquiv_yx` (the arithmetic input `κ(C')(t) ≇ κ(C)(t)`) and `resEquiv_y` (the identification
of the `ℙ¹ × C`-divisor with the base point). -/
theorem not_resEquiv_x : ¬ ResEquiv 𝕜 L.x L.z₀ := fun h =>
  L.not_resEquiv_yx
    (Work.Motivic.ResEquiv.symm
      (Work.Motivic.ResEquiv.trans h (Work.Motivic.ResEquiv.symm L.resEquiv_y)))

/-- The two exceptional divisors of the link contribute `1` and `0` to the coefficient at `z₀`:
`excCount 𝕜 z₀ ψ⁻¹ = 1` (the `ℙ¹ × C` divisor matches the function field `κ(C)(t)`) and
`excCount 𝕜 z₀ ψ = 0` (the `ℙ¹ × C'` divisor does not). -/
theorem excCount_pair : excCount 𝕜 L.z₀ L.ψ.symm = 1 ∧ excCount 𝕜 L.z₀ L.ψ = 0 :=
  excCount_pair_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.Q) (Y := L.P) L.z₀ L.ψ
    L.exDiv_ψ L.exDiv_ψ_symm L.not_resEquiv_x L.resEquiv_y

/-- The `[κ(z₀)]`-coefficient of the Crauder–Katz link itself is `1`. -/
theorem cInv_ψ : cInv 𝕜 L.z₀ L.ψ = 1 :=
  cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.Q) (Y := L.P) L.z₀ L.ψ
    L.exDiv_ψ L.exDiv_ψ_symm L.not_resEquiv_x L.resEquiv_y

/-- The transport does not change the coefficient (`c(φ) = c(ψ)` of the paper, which holds because
`ε` and `δ` are strongly birational identifications, i.e. have vanishing invariant). -/
theorem cInv_toBirationalMap_eq : cInv 𝕜 L.z₀ L.toBirationalMap = cInv 𝕜 L.z₀ L.ψ := by
  have h : L.toBirationalMap = Work.LLink.transport L.ε L.ψ L.δ := rfl
  rw [h]
  exact cInv_transport_eq_of_eq_zero L.ε L.ψ L.δ L.z₀ L.cInv_ε L.cInv_δ

/-- The coefficient of the transported map is exactly `1`. -/
theorem inv_eq_one : L.inv = 1 := by
  have h : L.inv = cInv 𝕜 L.z₀ L.toBirationalMap := rfl
  rw [h, cInv_toBirationalMap_eq, cInv_ψ]

/-- **Main theorem of this file.**  The transported Crauder–Katz map is a Cremona transformation
of `𝔸³` over `𝕜` whose `[κ(C)(t)]`-coefficient is exactly `1`; in particular the L-link is
motivically non-trivial. -/
theorem inv_ne_zero : L.inv ≠ 0 := by
  rw [L.inv_eq_one]
  norm_num

/-- **The arithmetic input is exactly what makes the link non-trivial.**  If the two exceptional
divisors of the Crauder–Katz link had the same function field — i.e. if `C` and `Jac²C` were
stably birational — the coefficient of the transported map would vanish.  So `not_resEquiv_yx`
(hence the paper's `C ≇ Jac²C`) is the precise content consumed by Theorem 1.2 (1) (a). -/
theorem inv_eq_zero_of_resEquiv_yx (h : ResEquiv 𝕜 L.y L.x) : L.inv = 0 := by
  have hyz : ResEquiv 𝕜 L.y L.z₀ := L.resEquiv_y
  have hxz : ResEquiv 𝕜 L.x L.z₀ :=
    Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm h) L.resEquiv_y
  have hψ : cInv 𝕜 L.z₀ L.ψ = 0 :=
    cInv_eq_zero_of_exDiv_eq_singletons_of_resEquiv (𝕜 := 𝕜) (X := L.Q) (Y := L.P) L.z₀ L.ψ
      L.exDiv_ψ L.exDiv_ψ_symm hxz hyz
  have hinv : L.inv = cInv 𝕜 L.z₀ L.toBirationalMap := rfl
  rw [hinv, cInv_toBirationalMap_eq, hψ]

/-- The same coefficient computed at the exceptional divisor `y` itself as base point.  This is
the base-point-free form of the computation: with `Z := ℙ³` and `z₀ := y` the hypothesis
`resEquiv_y` is `rfl`, and the only input is `not_resEquiv_yx`. -/
theorem invAtY_eq_one : L.invAtY = 1 := by
  have h : L.invAtY = cInv 𝕜 L.y L.ψ := rfl
  rw [h]
  exact cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.Q) (Y := L.P) L.y L.ψ
    L.exDiv_ψ L.exDiv_ψ_symm L.not_resEquiv_xy (Work.Motivic.ResEquiv.refl 𝕜 L.y)

/-- The `[κ(ℙ¹ × C)]`-coefficient of the link is nonzero, base point `y`. -/
theorem invAtY_ne_zero : L.invAtY ≠ 0 := by
  rw [L.invAtY_eq_one]
  norm_num

end Aux

/-- Existence form, ready to be fed to `Work.Motivic.not_gen_of_cInv_ne_zero`: the transported
Crauder–Katz transformation is a Cremona map with non-vanishing `[κ(C)(t)]`-coefficient. -/
theorem exists_cInv_ne_zero (h : Nonempty (QuadroCubicLink 𝕜 X)) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
      cInv 𝕜 z₀ (φ : (Affine3 𝕜).BirationalMap (Affine3 𝕜)) ≠ 0 := by
  obtain ⟨L⟩ := h
  exact ⟨L.Z, L.overZ, L.z₀, L.transportCr, L.inv_ne_zero⟩

end QuadroCubicLink

end Work.LLink
