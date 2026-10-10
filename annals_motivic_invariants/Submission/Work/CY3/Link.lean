import Submission.Work.CY3.Section
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Link` — the CY3 L-link and its invariant coefficient

This file records **Layers 2–3** of the CY3 construction of Lin–Shinder,
*Motivic invariants of birational maps* (Annals **199** (1), 2024, `thm:CY3`), in the shape in
which the theorem-level argument consumes it, and computes the resulting invariant coefficient in
the per-coefficient vocabulary of Part A (`Work.Motivic.Defs`).

## The link

Over a field `𝕜`, `thm:CY3` produces a motivically non-trivial smooth projective L-link

```
        X_𝕜
      /     \
  Bl_{Z_𝕜}  Bl_{Z'_𝕜}
   /          \
 Z_𝕜 ⊂ G/P --ψ--> G/P' ⊃ Z'_𝕜
```

where `G/P`, `G/P'` are the five-dimensional `G₂`-Grassmannians and `Z_𝕜`, `Z'_𝕜` are `K`-trivial
threefolds of Picard rank one.  Its two exceptional divisors are birational to `ℙ¹ × Z'_𝕜` and
`ℙ¹ × Z_𝕜` respectively, so that (paper Lemma `lemma:L-link` (2) with `m = m' = 2`)

`c(ψ_𝕜) = [ℙ¹ × Z_𝕜] − [ℙ¹ × Z'_𝕜] ≠ 0`

because `Z_𝕜` and `Z'_𝕜` are not stably birational (Totaro, `cor-CYnSB`; see
`Submission/Work/CY3/Totaro.lean`).

## What is an input and what is proved

* **Inputs** (fields of `CY3Data`/`CY3Link`): the layer-1 `G₂` infrastructure and the layer-2
  general section/blow-up data (inherited from `CY3Section`), the two `K`-triviality and
  Picard-rank-one facts of the centres `Z`, `Z'` (paper `lem-nSBG2`; named predicates), a model
  `ZW` of `Z × ℙ¹` with a base point `z₀` and the identification `κ(y) ≅ κ(z₀) = κ(Z)(t)`, the
  `ℙ¹`-bundle bridge (`ResEquiv 𝕜 y x → StablyBirational 𝕜 Z Z'`) — the (F1)–(F3) residual of the
  L-link analysis — and the two transports `ε : 𝔸⁵ ⤏ G/P`, `δ : G/P' ⤏ 𝔸⁵` with vanishing
  coefficient at `z₀` (which is what moves the link into the challenge's `Cr 𝕜 5 = Bir(𝔸⁵/𝕜)`);
  `CY3Link` adds `¬ ResEquiv 𝕜 y x`, i.e. `κ(Z)(t) ≇ κ(Z')(t)`, which is where Totaro's
  `cor-CYnSB` enters.
* **Proved here**: the counting (`excCount 𝕜 z₀ ψ = 0`, `excCount 𝕜 z₀ ψ⁻¹ = 1`), the coefficient
  `cInv 𝕜 z₀ ψ = 1`, the fact that the transported Cremona map `φ = ε ∘ ψ ∘ δ` has the same
  coefficient as `ψ` (`cInv_toBirationalMap_eq`, from additivity of the invariant), the conclusion
  `inv = 1 ≠ 0`, the sharpness converse `inv_eq_zero_of_resEquiv_yx`, and the existence form
  `exists_cInv_ne_zero` in exactly the shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Layer 3 of `thm:CY3`: the geometric data of the CY3 L-link.**

Extends Layer 2 (`Work.CY3.CY3Section`) by

* the two `K`-triviality and Picard-rank-one facts about the centres `Z_𝕜`, `Z'_𝕜` (paper
  `lem-nSBG2`: `Z_𝕜`, `Z'_𝕜` are `K`-trivial threefolds of Picard rank one, because the blow-up
  `X_𝕜 → G_𝕜/P_𝕜` is a `ℙ¹`-bundle and `ρ(X_𝕜) = 2` by Grothendieck–Lefschetz, whence
  `ρ(Z_𝕜) = 1`; `K`-triviality is adjunction for the blow-up and the trivial canonical bundle of
  the `G₂`-Grassmannian);
* a model `ZW` of `Z_𝕜 × ℙ¹` with a base point `z₀` and the identification `κ(y) ≅ κ(z₀)`, i.e.
  the base point of the invariant is the generic point of `Z_𝕜 × ℙ¹` (`κ(z₀) = κ(Z)(t)`);
* the `ℙ¹`-bundle bridge: an isomorphism of the function fields of the two exceptional divisors
  forces `Z_𝕜` and `Z'_𝕜` to be stably birational;
* the two transports `ε : 𝔸⁵ ⤏ G/P`, `δ : G/P' ⤏ 𝔸⁵` with `cInv 𝕜 z₀ ε = cInv 𝕜 z₀ δ = 0`,
  which move the link into the challenge's `Cr 𝕜 5 = Bir(𝔸⁵/𝕜)` at the cost of nothing (see
  `Submission/Work/CY3/NOTES.md` §3.1 for why these are inputs and not a consequence of layer 1).

This is the datum produced by the paper's construction over an infinite field `𝕜` (Layer 2's
Bertini step needs `Infinite 𝕜`; the structure itself does not mention it). -/
structure CY3Data (𝕜 : Type) [Field 𝕜] extends CY3Section 𝕜 where
  /-- **Named predicate** (`lem-nSBG2`, adjunction): the first centre is `K`-trivial. -/
  isKTrivial_Z : IsKTrivial 𝕜 Z
  /-- **Named predicate**: the second centre is `K`-trivial. -/
  isKTrivial_Z' : IsKTrivial 𝕜 Z'
  /-- **Named predicate** (`lem-nSBG2` + Grothendieck–Lefschetz): the first centre has Picard
  rank one. -/
  picardOne_Z : PicardRankOne 𝕜 Z
  /-- **Named predicate**: the second centre has Picard rank one. -/
  picardOne_Z' : PicardRankOne 𝕜 Z'
  /-- a model of `Z_𝕜 × ℙ¹` (`Z_𝕜 × ℙ¹` itself is not expressible: `ℙ¹` is only available here as
  `Work.CY3.ProjectiveLine`, and no birational geometry of it is in Mathlib). -/
  ZW : Scheme.{0}
  [overZW : ZW.Over (Spec (.of 𝕜))]
  /-- the base point of the invariant: the generic point of `Z_𝕜 × ℙ¹`. -/
  z₀ : ZW
  /-- `κ(y) ≅ κ(z₀)`: both are the function field `κ(Z)(t)` of `Z_𝕜 × ℙ¹`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- **The `ℙ¹`-bundle bridge.**  The exceptional divisor `y` of `ψ⁻¹` is birational to
  `ℙ¹ × Z_𝕜` and `x` to `ℙ¹ × Z'_𝕜` (paper Lemma `lemma:L-link` (2), with (L3) for the
  irreducibility of the exceptional divisors); hence a `𝕜`-isomorphism of their function fields —
  the function fields of the two `ℙ¹`-bundles — forces `Z_𝕜` and `Z'_𝕜` to be stably birational.
  This is the (F1)–(F3) residual of `Submission/Work/LLink/NOTES.md` §6: "stable birationality of
  smooth projective varieties with a `ℙ¹`-factor is detected by the birational type of the
  factor".  It transfers the conclusion of Totaro's `cor-CYnSB` from the centres to the link. -/
  bridge : ResEquiv 𝕜 y x → StablyBirational 𝕜 Z Z'
  /-- **(F1) of `lemma:L-link` (2) for the CY3 link, on the target.**  The exceptional divisor
  `y_𝕜` of `ψ⁻¹` is birational to `ℙ¹ × Z_𝕜`: its residue field is `RatFunc (funField Z)`, the
  cylinder field `κ(Z)(t)`.

  This is the same clause that the K3 area carries as `Work.K3Inputs.IsP1BundleOver`
  (`Work.K3Inputs.LinkCore.y_cylinder`), and it is a *geometric* statement about the link that the
  field `bridge` above does *not* carry: `bridge` records only the resulting *implication*
  `ResEquiv 𝕜 y x → StablyBirational 𝕜 Z Z'`.  It is needed by the stabilisation
  `c(φ × id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W] ≠ 0` of `thm:bir-generation` (c)
  (`Submission/Work/CY3Stab`, `Work.CY3Stab.CY3P1Bundle`): the coefficient count there has to know
  that the cylinder points over `y` and over `x` are `Z × ℙ¹ × W` and `Z' × ℙ¹ × W` respectively,
  which is exactly this clause. -/
  p1Bundle_y : Work.K3Inputs.IsP1BundleOver 𝕜 y Z
  /-- **(F1) of `lemma:L-link` (2) for the CY3 link, on the source.**  The exceptional divisor
  `x_𝕜` of `ψ` is birational to `ℙ¹ × Z'_𝕜`: its residue field is `RatFunc (funField Z')`. -/
  p1Bundle_x : Work.K3Inputs.IsP1BundleOver 𝕜 x Z'
  /-- **The transport to affine space**: a birational identification `ε : 𝔸⁵ ⤏ G/P` over `𝕜`.

  The challenge's Cremona group is `Cr 𝕜 5 = Bir(𝔸⁵/𝕜)`, while the link `ψ` lives on `G/P`, so
  the link has to be transported to affine space.  These transports are *inputs*, not consequences
  of layer 1: between `𝔸⁵` and a projective fivefold no transport has all its coefficients zero
  (`ℙ¹` and `𝔸¹` are already wrongly matched — see `Submission/Work/CY3/StronglyRational.lean`),
  so only their vanishing at the base point `z₀` is required, which is the weakest form of strong
  rationality sufficient for `c(φ) = c(ψ)`.  It is automatic for the transports coming from
  `lem:GP-strongly-rational`: their exceptional divisors are rational (`κ(ℙ⁴)`), while
  `κ(z₀) = κ(Z)(t)` is not rational — `Z` is `K`-trivial of Picard rank one, hence not rational.
  (Same convention as the K3 area, `Submission/Work/K3/NOTES.md` §7 (4).) -/
  eps : (Affine 𝕜 5).BirationalMap P
  [isOverEps : eps.IsOver (Spec (.of 𝕜))]
  /-- **The transport back from the target**: a birational identification `δ : G/P' ⤏ 𝔸⁵` over
  `𝕜`.  It comes from the strong rationality of `G/P'` (the target of `ψ`), while `eps` transports
  *into* the source `G/P`. -/
  delta : P'.BirationalMap (Affine 𝕜 5)
  [isOverDelta : delta.IsOver (Spec (.of 𝕜))]
  /-- `cInv 𝕜 z₀ ε = 0`: the transport `ε` contributes nothing to the coefficient at `z₀`. -/
  cInv_eps : cInv 𝕜 z₀ eps = 0
  /-- `cInv 𝕜 z₀ δ = 0`. -/
  cInv_delta : cInv 𝕜 z₀ delta = 0

attribute [instance] CY3Data.overZW CY3Data.isOverEps CY3Data.isOverDelta

/-- **The CY3 L-link**: the geometric data together with the non-triviality input
`κ(y) ≇ κ(x)`, i.e. `κ(Z)(t) ≇ κ(Z')(t)`.  Since `Z` and `Z'` are `K`-trivial threefolds of
Picard rank one and are not isomorphic (paper `lem-nSBG2`: the two cubic self-intersections
`c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³` differ), Totaro's Corollary `cor-CYnSB` gives this input —
see `Work.CY3.CY3Data.not_resEquiv_yx_of_totaro`. -/
structure CY3Link (𝕜 : Type) [Field 𝕜] extends CY3Data 𝕜 where
  /-- `κ(y) ≇ κ(x)`: the function fields `κ(Z)(t)` and `κ(Z')(t)` of the two exceptional divisors
  are not `𝕜`-isomorphic, i.e. `Z_𝕜` and `Z'_𝕜` are not stably birational. -/
  not_resEquiv_yx : ¬ ResEquiv 𝕜 y x

namespace CY3Data

variable {𝕜 : Type} [Field 𝕜] (D : CY3Data 𝕜)

local instance instVarietyB : Variety 𝕜 D.B := D.varietyB
local instance instVarietyP : Variety 𝕜 D.P := D.varietyP
local instance instVarietyP' : Variety 𝕜 D.P' := D.varietyP'
local instance instOverZW : D.ZW.Over (Spec (.of 𝕜)) := D.overZW

local instance instEpsOver : D.eps.IsOver (Spec (.of 𝕜)) := D.isOverEps
local instance instDeltaOver : D.delta.IsOver (Spec (.of 𝕜)) := D.isOverDelta
local instance instPsiOver : D.psi.IsOver (Spec (.of 𝕜)) := D.isOverPsi

/-- The **transported CY3 link**: the birational map `ε ∘ ψ ∘ δ` of `𝔸⁵`, an element of the
Cremona group `Cr 𝕜 5` of the challenge. -/
noncomputable def transportCr (D : CY3Data 𝕜) : Cr 𝕜 5 :=
  Work.CY3.transportCr 5 D.eps D.psi D.delta

/-- The underlying birational self-map of `𝔸⁵`. -/
noncomputable def toBirationalMap (D : CY3Data 𝕜) : (Affine 𝕜 5).BirationalMap (Affine 𝕜 5) :=
  Work.CY3.transport 5 D.eps D.psi D.delta

@[simp]
theorem transportCr_coe : ((D.transportCr : Cr 𝕜 5) :
    (Affine 𝕜 5).BirationalMap (Affine 𝕜 5)) = D.toBirationalMap := rfl

theorem toBirationalMap_def : D.toBirationalMap = transport 5 D.eps D.psi D.delta := rfl

/-- **The affine transport does not change the coefficient** (the paper's `c(φ) = c(ψ)`, from
the vanishing of the coefficients of the two transports at the base point). -/
theorem cInv_toBirationalMap_eq : cInv 𝕜 D.z₀ D.toBirationalMap = cInv 𝕜 D.z₀ D.psi :=
  cInv_transport_eq_of_eq_zero 5 D.eps D.psi D.delta D.z₀ D.cInv_eps D.cInv_delta

end CY3Data

namespace CY3Link

variable {𝕜 : Type} [Field 𝕜] (L : CY3Link 𝕜)

local instance instVarietyB : Variety 𝕜 L.B := L.varietyB
local instance instVarietyP : Variety 𝕜 L.P := L.varietyP
local instance instVarietyP' : Variety 𝕜 L.P' := L.varietyP'
local instance instVarietyZ : Variety 𝕜 L.Z := L.varietyZ
local instance instVarietyZ' : Variety 𝕜 L.Z' := L.varietyZ'
local instance instOverZW : L.ZW.Over (Spec (.of 𝕜)) := L.overZW
local instance instEpsOver : L.eps.IsOver (Spec (.of 𝕜)) := L.isOverEps
local instance instDeltaOver : L.delta.IsOver (Spec (.of 𝕜)) := L.isOverDelta
local instance instPsiOver : L.psi.IsOver (Spec (.of 𝕜)) := L.isOverPsi

/-- `κ(x) ≇ κ(y)`: the two exceptional divisors are distinguished by their function fields. -/
theorem not_resEquiv_xy : ¬ ResEquiv 𝕜 L.x L.y := fun h =>
  L.not_resEquiv_yx (Work.Motivic.ResEquiv.symm h)

/-- `κ(x) ≇ κ(z₀)`: the `ℙ¹ × Z'`-divisor does not match the base point.  Derived from Totaro's
input `not_resEquiv_yx` and from `resEquiv_y` (the identification of the other exceptional divisor
with the base point `z₀`). -/
theorem not_resEquiv_x : ¬ ResEquiv 𝕜 L.x L.z₀ := fun h =>
  L.not_resEquiv_yx
    (Work.Motivic.ResEquiv.symm
      (Work.Motivic.ResEquiv.trans h (Work.Motivic.ResEquiv.symm L.resEquiv_y)))

/-- The two exceptional divisors contribute `1` and `0` to the coefficient at `z₀`:
`excCount 𝕜 z₀ ψ⁻¹ = 1` (the `ℙ¹ × Z`-divisor matches `κ(Z)(t)`) and `excCount 𝕜 z₀ ψ = 0` (the
`ℙ¹ × Z'`-divisor does not). -/
theorem excCount_pair : excCount 𝕜 L.z₀ L.psi.symm = 1 ∧ excCount 𝕜 L.z₀ L.psi = 0 :=
  Work.LLink.excCount_pair_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.P) (Y := L.P') L.z₀ L.psi
    L.exDiv_psi L.exDiv_psi_symm L.not_resEquiv_x L.resEquiv_y

/-- **The coefficient of the link itself is `1`**: `c(ψ_𝕜)` evaluated at the class `[κ(Z)(t)]` is
`1`, i.e. `[ℙ¹ × Z_𝕜] − [ℙ¹ × Z'_𝕜]` has coefficient `1 − 0` there (paper `lemma:L-link` (2)). -/
theorem cInv_psi : cInv 𝕜 L.z₀ L.psi = 1 :=
  Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.P) (Y := L.P') L.z₀ L.psi
    L.exDiv_psi L.exDiv_psi_symm L.not_resEquiv_x L.resEquiv_y

/-- **The invariant coefficient of the CY3 link**: the `[κ(Z)(t)]`-coefficient of the transported
Cremona map `φ = ε ∘ ψ ∘ δ ∈ Cr 𝕜 5`.  This is the number whose non-vanishing Theorem 1.2 (3)
needs. -/
noncomputable def inv : ℤ := cInv 𝕜 L.z₀ L.toBirationalMap

/-- The same coefficient, computed with base point the exceptional divisor `y` itself (which has
the same function field `κ(Z)(t)` as `z₀`). -/
noncomputable def invAtY : ℤ := cInv 𝕜 L.y L.psi

/-- The coefficient of the transported map is exactly `1`. -/
theorem inv_eq_one : L.inv = 1 := by
  have h : L.inv = cInv 𝕜 L.z₀ L.toBirationalMap := rfl
  rw [h, L.cInv_toBirationalMap_eq, L.cInv_psi]

/-- **Main theorem of this file.**  The transported CY3 link is a Cremona transformation of `𝔸⁵`
over `𝕜` whose `[κ(Z)(t)]`-coefficient is exactly `1`: the L-link is motivically non-trivial. -/
theorem inv_ne_zero : L.inv ≠ 0 := by
  rw [L.inv_eq_one]
  norm_num

/-- **Sharpness.**  If the two exceptional divisors had the same function field — i.e. if `Z` and
`Z'` were stably birational — the coefficient would vanish.  So the input `not_resEquiv_yx`
(Totaro's `cor-CYnSB`) is exactly what makes the link non-trivial. -/
theorem inv_eq_zero_of_resEquiv_yx (h : ResEquiv 𝕜 L.y L.x) : L.inv = 0 := by
  have hyz : ResEquiv 𝕜 L.y L.z₀ := L.resEquiv_y
  have hxz : ResEquiv 𝕜 L.x L.z₀ :=
    Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm h) L.resEquiv_y
  have hψ : cInv 𝕜 L.z₀ L.psi = 0 :=
    Work.LLink.cInv_eq_zero_of_exDiv_eq_singletons_of_resEquiv (𝕜 := 𝕜) (X := L.P) (Y := L.P')
      L.z₀ L.psi L.exDiv_psi L.exDiv_psi_symm hxz hyz
  have hinv : L.inv = cInv 𝕜 L.z₀ L.toBirationalMap := rfl
  rw [hinv, L.cInv_toBirationalMap_eq, hψ]

/-- The same coefficient, computed at the exceptional divisor `y` as base point: the
base-point-free form of the computation, where the only input is `not_resEquiv_yx`. -/
theorem invAtY_eq_one : L.invAtY = 1 := by
  have h : L.invAtY = cInv 𝕜 L.y L.psi := rfl
  rw [h]
  exact Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := L.P) (Y := L.P') L.y L.psi
    L.exDiv_psi L.exDiv_psi_symm L.not_resEquiv_xy (Work.Motivic.ResEquiv.refl 𝕜 L.y)

/-- The `[κ(ℙ¹ × Z)]`-coefficient of the link is nonzero, with base point `y`. -/
theorem invAtY_ne_zero : L.invAtY ≠ 0 := by
  rw [L.invAtY_eq_one]
  norm_num

/-- Existence form, in the exact shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`: the
transported CY3 link is a Cremona transformation of `𝔸⁵` over `𝕜` with non-vanishing
`[κ(Z)(t)]`-coefficient. -/
theorem exists_cInv_ne_zero (L : CY3Link 𝕜) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Affine 𝕜 5).BirationalMap (Affine 𝕜 5)) ≠ 0 :=
  ⟨L.ZW, L.overZW, L.z₀, L.transportCr, by rw [CY3Data.transportCr_coe]; exact L.inv_ne_zero⟩

end CY3Link

end

end Work.CY3
