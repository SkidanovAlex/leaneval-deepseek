import Submission.Work.K3.Defs
import Submission.Work.LLink.Count
import Submission.Work.LLink.not_resEquiv_of_ringEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.K3Link` — the K3 L-link over a field and its invariant coefficient

This file records the geometric data of Theorem `thm:K3` of Lin–Shinder
(*Motivic invariants of birational maps*, Annals **199** (1), 2024) in the shape in which the
theorem-level argument consumes it, and computes the resulting invariant coefficient.

## The link

Over a field `𝕜`, the theorem produces a motivically non-trivial L-link

```
        T
      /   \
 Bl_{S_0}  Bl_{S'_0}
   /          \
 S_0 ⊂ ℙ⁴ --ψ--> ℙ⁴ ⊃ S'_0
```

where `S`, `S'` are non-isomorphic K3 surfaces of degree `12` and geometric Picard rank one
(`S'` the unique Fourier–Mukai partner of `S`), and

`c(ψ_𝕜) = [S_𝕜 × ℙ¹] − [S'_𝕜 × ℙ¹] ≠ 0`  (Lemma `lemma:L-link` (2) with `m = m' = 2`),

because `S_𝕜` and `S'_𝕜` are not stably birational (Totaro, `cor-CYnSB`).  The two exceptional
divisors of `ψ` are birational to `S'_0 × ℙ¹` and `S_0 × ℙ¹` respectively, which are birational
to `S' × ℙ¹` and `S × ℙ¹` (`thm-HL` (1)).

## What is an input and what is proved

* **Inputs** (fields of the structure `K3Link`): the two K3 surfaces `S`, `S'` with their named
  geometric predicates; the ambient fourfold `P` (a model of `ℙ⁴`) with the birational self-map
  `ψ` and its **two exceptional divisors** `x` (birational to `S' × ℙ¹`, on the source side) and
  `y` (birational to `S × ℙ¹`, on the target side); the base point `z₀`, a point of `P` with
  `κ(z₀) = κ(S)(t) = κ(y)` (in the descent it is the exceptional divisor `y` itself); the fact that
  `κ(y) ≇ κ(x)`
  (`not_resEquiv_yx`, which is Totaro's Corollary `cor-CYnSB` combined with the ℙ¹-bundle
  description of the two exceptional divisors — see `Work.K3.HL`); and the two birational
  identifications `ε : 𝔸⁴ ⤏ P`, `δ : P ⤏ 𝔸⁴` with vanishing coefficient (strong rationality of
  `ℙ⁴`).
* **Proved here**: everything on top of the inputs — the counting (`excCount` of the two
  exceptional divisors is `1` and `0`), the value of the coefficient `cInv 𝕜 z₀ ψ = 1`, the
  invariance of the coefficient under the affine transport, and the conclusion
  `inv = 1 ≠ 0`, together with the sharpness converse
  (`inv_eq_zero_of_resEquiv_yx`).

## Relation to `Work.LLink`

The counting layer is that of `Work.LLink.Count`, which is stated for an arbitrary birational map
`φ : X ⤏ Y` with a single exceptional divisor in each direction; the dimension of the link plays
no role in the count.  What is `n = 4`-specific here is the affine transport
`Work.K3.transportCr` (to `Cr 𝕜 4`) and the geometric identification of the two centres.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

/-- **The geometric data of the K3 L-link** (`thm:K3` without the non-triviality statement).

The named geometric predicates (`isK3`, `picardOne`, …) stand for properties of smooth projective
K3 surfaces that Mathlib cannot express; the remaining fields are the geometric data of the link:
the two centres `S`, `S'`, the ambient model `P` of `ℙ⁴`, the Cremona transformation `ψ` with its
**two exceptional divisors** `x` (birational to `S' × ℙ¹`) and `y` (birational to `S × ℙ¹`), the
base point `z₀` (a point of `P` with `κ(z₀) = κ(S)(t) = κ(y)`), the ℙ¹-bundle bridge
`bridge` (an isomorphism of the function fields of the two exceptional divisors forces `S`, `S'`
to be stably birational), and the two birational identifications with `𝔸⁴` with vanishing
coefficient (strong rationality of the two sides of the link).

This is the datum which the descent step (`Submission/Work/K3/Descent.lean`) produces over `𝕜`
from the `ℚ`-model of the Hassett–Lai construction. -/
structure K3Data (𝕜 : Type) [Field 𝕜] where
  /-- The first K3 surface `S` (the centre `S_0 ⊂ ℙ⁴`, minimal model `S`). -/
  S : Scheme.{0}
  [varietyS : Variety 𝕜 S]
  /-- `S` is a K3 surface of degree `12` (named predicate). -/
  isK3 : IsK3Degree12 𝕜 S
  /-- `S` is `K`-trivial (named predicate). -/
  kTrivial : IsKTrivial 𝕜 S
  /-- `S` has geometric Picard rank one (named predicate). -/
  picardOne : PicardRankOneGeom 𝕜 S
  /-- The Fourier–Mukai partner `S'` (the minimal model of the other centre `S'_0`). -/
  S' : Scheme.{0}
  [varietyS' : Variety 𝕜 S']
  /-- `S'` is a K3 surface of degree `12` (named predicate). -/
  isK3' : IsK3Degree12 𝕜 S'
  /-- `S'` is `K`-trivial (named predicate). -/
  kTrivial' : IsKTrivial 𝕜 S'
  /-- `S'` has geometric Picard rank one (named predicate). -/
  picardOne' : PicardRankOneGeom 𝕜 S'
  /-- The fourfold carrying the link (a model of `ℙ⁴`). -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- The Cremona transformation `ψ : ℙ⁴ ⤏ ℙ⁴` of the link. -/
  ψ : P.BirationalMap P
  [isOverψ : ψ.IsOver (Spec (.of 𝕜))]
  /-- The exceptional divisor of `ψ` on the source (birational to `S' × ℙ¹`). -/
  x : P
  /-- The exceptional divisor of `ψ⁻¹` on the target (birational to `S × ℙ¹`). -/
  y : P
  /-- `x` is the only exceptional divisor of `ψ`. -/
  exDiv_ψ : exDiv ψ = {x}
  /-- `y` is the only exceptional divisor of `ψ⁻¹`. -/
  exDiv_ψ_symm : exDiv ψ.symm = {y}
  /-- The base point `z₀` of the invariant: a point of `P` whose residue field is the function
  field `κ(S)(t)` of `S × ℙ¹` (in the descent it is the exceptional divisor `y` itself). -/
  z₀ : P
  /-- `κ(y) ≅ κ(z₀)`: both are the function field `κ(S)(t)` of `S × ℙ¹`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- The birational identification `𝔸⁴ ⤏ P` (strong rationality of `ℙ⁴`). -/
  ε : (Affine4 𝕜).BirationalMap P
  [isOverε : ε.IsOver (Spec (.of 𝕜))]
  /-- The birational identification `P ⤏ 𝔸⁴`. -/
  δ : P.BirationalMap (Affine4 𝕜)
  [isOverδ : δ.IsOver (Spec (.of 𝕜))]
  /-- The transport `ε` contributes nothing to the coefficient. -/
  cInv_ε : cInv 𝕜 z₀ ε = 0
  /-- The transport `δ` contributes nothing to the coefficient. -/
  cInv_δ : cInv 𝕜 z₀ δ = 0
  /-- **The `ℙ¹`-bundle bridge.**  The exceptional divisor `y` is birational to `S × ℙ¹` and `x`
  to `S' × ℙ¹` (Lemma `lemma:L-link` (2)); hence a `𝕜`-isomorphism of their function fields — the
  function fields of the two `ℙ¹`-bundles — forces `S` and `S'` to be stably birational.  This is
  the (F1)–(F3) residual of the L-link analysis (`Submission/Work/LLink/NOTES.md` §6): it
  transfers the conclusion of Totaro's `cor-CYnSB` from the centres to the link. -/
  bridge : ResEquiv 𝕜 y x → StablyBirational 𝕜 S S'

/-- **The K3 L-link**: the geometric data together with the non-triviality input
`κ(y) ≇ κ(x)`, i.e. `κ(S)(t) ≇ κ(S')(t)`, which is where Totaro's Corollary `cor-CYnSB`
(non-isomorphic `K`-trivial varieties of Picard number one are not stably birational) enters;
see `Work.K3.K3Data.not_resEquiv_yx_of_totaro` in `Submission/Work/K3/HL.lean`. -/
structure K3Link (𝕜 : Type) [Field 𝕜] extends K3Data 𝕜 where
  /-- `κ(y) ≇ κ(x)`: the function fields `κ(S)(t)` and `κ(S')(t)` of the two exceptional
  divisors are not `𝕜`-isomorphic. -/
  not_resEquiv_yx : ¬ ResEquiv 𝕜 y x

/- The structure fields as instances (the constituents of the link are `𝕜`-schemes). We test
that instance search can use them for a *variable* `D : K3Data 𝕜`. -/
attribute [instance] K3Data.varietyS K3Data.varietyS' K3Data.varietyP
  K3Data.isOverψ K3Data.isOverε K3Data.isOverδ

example {𝕜 : Type} [Field 𝕜] (D : K3Data 𝕜) : Variety 𝕜 D.S := inferInstance
example {𝕜 : Type} [Field 𝕜] (D : K3Data 𝕜) : (ResEquiv 𝕜 D.y D.x → ResEquiv 𝕜 D.y D.x) := id

namespace K3Link

variable {𝕜 : Type} [Field 𝕜] {L : K3Link 𝕜}

/-- The transported Cremona map of the K3 link: an explicit element of `Cr 𝕜 4`. -/
noncomputable def transportCr (L : K3Link 𝕜) : Cr 𝕜 4 :=
  letI : Variety 𝕜 L.P := L.varietyP
  letI : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
  letI : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
  letI : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ
  Work.K3.transportCr L.ε L.ψ L.δ

/-- The underlying birational self-map of `𝔸⁴`. -/
noncomputable def toBirationalMap (L : K3Link 𝕜) :
    (Affine4 𝕜).BirationalMap (Affine4 𝕜) :=
  ((L.transportCr : Cr 𝕜 4) : (Affine4 𝕜).BirationalMap (Affine4 𝕜))

/-- **The invariant coefficient of the K3 link**, i.e. the `[κ(S)(t)]`-coefficient of `c(ψ_𝕜)`,
computed at the base point `z₀`.  This is the number whose non-vanishing Theorem 1.2 (2) needs. -/
noncomputable def inv (L : K3Link 𝕜) : ℤ :=
  letI : L.P.Over (Spec (.of 𝕜)) := L.varietyP.over
  cInv 𝕜 L.z₀ L.toBirationalMap

/-- The same coefficient, computed with base point the exceptional divisor `y` itself (which has
the same function field `κ(S)(t)` as `z₀`, so the two agree by
`Work.LLink.cInv_congr_of_resEquiv`). -/
noncomputable def invAtY (L : K3Link 𝕜) : ℤ :=
  letI : Variety 𝕜 L.P := L.varietyP
  cInv 𝕜 L.y L.ψ

section Aux

variable (L : K3Link 𝕜)

local instance instVarietyS : Variety 𝕜 L.S := L.varietyS
local instance instVarietyS' : Variety 𝕜 L.S' := L.varietyS'
local instance instVarietyP : Variety 𝕜 L.P := L.varietyP
local instance instOverPt : L.P.Over (Spec (.of 𝕜)) := L.varietyP.over
local instance instIsOverε : (L.ε).IsOver (Spec (.of 𝕜)) := L.isOverε
local instance instIsOverψ : (L.ψ).IsOver (Spec (.of 𝕜)) := L.isOverψ
local instance instIsOverδ : (L.δ).IsOver (Spec (.of 𝕜)) := L.isOverδ

/-- `κ(x) ≇ κ(y)`: the two exceptional divisors are distinguished by their function fields. -/
theorem not_resEquiv_xy : ¬ ResEquiv 𝕜 L.x L.y := fun h =>
  L.not_resEquiv_yx (Work.Motivic.ResEquiv.symm h)

/-- `κ(x) ≇ κ(z₀)`: the `ℙ¹ × S'`-divisor does not match the base point.  Derived from the
Totaro input `not_resEquiv_yx` and from `resEquiv_y` (the identification of the other exceptional
divisor with the base point). -/
theorem not_resEquiv_x : ¬ ResEquiv 𝕜 L.x L.z₀ := fun h =>
  L.not_resEquiv_yx
    (Work.Motivic.ResEquiv.symm
      (Work.Motivic.ResEquiv.trans h (Work.Motivic.ResEquiv.symm L.resEquiv_y)))

/-- The two exceptional divisors contribute `1` and `0` to the coefficient at `z₀`. -/
theorem excCount_pair : excCount 𝕜 L.z₀ L.ψ.symm = 1 ∧ excCount 𝕜 L.z₀ L.ψ = 0 :=
  Work.LLink.excCount_pair_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.P) (Y := L.P) L.z₀ L.ψ
    L.exDiv_ψ L.exDiv_ψ_symm L.not_resEquiv_x L.resEquiv_y

/-- **The coefficient of the K3 link itself is `1`**: `c(ψ_𝕜)` evaluated at the class
`[κ(S)(t)]` is `1`, i.e. `[S_𝕜 × ℙ¹] − [S'_𝕜 × ℙ¹]` has coefficient `1 − 0` there. -/
theorem cInv_ψ : cInv 𝕜 L.z₀ L.ψ = 1 :=
  Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.P) (Y := L.P) L.z₀ L.ψ
    L.exDiv_ψ L.exDiv_ψ_symm L.not_resEquiv_x L.resEquiv_y

/-- The affine transport does not change the coefficient (`c(φ) = c(ψ)`, because the two
identifications are strongly rational). -/
theorem cInv_toBirationalMap_eq : cInv 𝕜 L.z₀ L.toBirationalMap = cInv 𝕜 L.z₀ L.ψ := by
  have h : L.toBirationalMap = Work.K3.transport L.ε L.ψ L.δ := rfl
  rw [h]
  exact cInv_transport_eq_of_eq_zero L.ε L.ψ L.δ L.z₀ L.cInv_ε L.cInv_δ

/-- The coefficient of the transported map is exactly `1`. -/
theorem inv_eq_one : L.inv = 1 := by
  have h : L.inv = cInv 𝕜 L.z₀ L.toBirationalMap := rfl
  rw [h, cInv_toBirationalMap_eq, cInv_ψ]

/-- **Main theorem of this file.**  The transported K3 link is a Cremona transformation of `𝔸⁴`
over `𝕜` whose `[κ(S)(t)]`-coefficient is exactly `1`: the L-link is motivically non-trivial. -/
theorem inv_ne_zero : L.inv ≠ 0 := by
  rw [L.inv_eq_one]
  norm_num

/-- **Sharpness.**  If the two exceptional divisors had the same function field — i.e. if `S` and
`S'` were stably birational — the coefficient would vanish.  So the input `not_resEquiv_yx`
(Totaro) is exactly what makes the link non-trivial. -/
theorem inv_eq_zero_of_resEquiv_yx (h : ResEquiv 𝕜 L.y L.x) : L.inv = 0 := by
  have hyz : ResEquiv 𝕜 L.y L.z₀ := L.resEquiv_y
  have hxz : ResEquiv 𝕜 L.x L.z₀ :=
    Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm h) L.resEquiv_y
  have hψ : cInv 𝕜 L.z₀ L.ψ = 0 :=
    Work.LLink.cInv_eq_zero_of_exDiv_eq_singletons_of_resEquiv (𝕜 := 𝕜) (X := L.P) (Y := L.P)
      L.z₀ L.ψ L.exDiv_ψ L.exDiv_ψ_symm hxz hyz
  have hinv : L.inv = cInv 𝕜 L.z₀ L.toBirationalMap := rfl
  rw [hinv, cInv_toBirationalMap_eq, hψ]

/-- The same coefficient, computed at the exceptional divisor `y` as base point. -/
theorem invAtY_eq_one : L.invAtY = 1 := by
  have h : L.invAtY = cInv 𝕜 L.y L.ψ := rfl
  rw [h]
  exact Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.P) (Y := L.P) L.y L.ψ
    L.exDiv_ψ L.exDiv_ψ_symm L.not_resEquiv_xy (Work.Motivic.ResEquiv.refl 𝕜 L.y)

/-- The `[κ(S)(t)]`-coefficient of the link is nonzero, with base point `y`. -/
theorem invAtY_ne_zero : L.invAtY ≠ 0 := by
  rw [L.invAtY_eq_one]
  norm_num

end Aux

/-- Existence form, in the exact shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`: the
transported K3 link is a Cremona transformation of `𝔸⁴` over `𝕜` with non-vanishing
`[κ(S)(t)]`-coefficient. -/
theorem exists_cInv_ne_zero (L : K3Link 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Affine4 𝕜).BirationalMap (Affine4 𝕜)) ≠ 0 :=
  ⟨L.P, L.varietyP.over, L.z₀, L.transportCr, L.inv_ne_zero⟩

end K3Link

end Work.K3
