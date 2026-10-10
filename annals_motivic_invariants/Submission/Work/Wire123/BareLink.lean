import Submission.Work.Wire123.MinLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.BareLink` — the link data alone, with the single remaining field isolated

`Work.Wire123.MinLink` consists of

1. a link `ψ : P ⇢ P'` whose two exceptional divisors are single points `x`, `y` of different
   birational classes at the base point `z₀` (so `cInv 𝕜 z₀ ψ = 1`),
2. one birational map `γ : P ⇢ P'` over `𝕜` with `cInv 𝕜 z₀ γ ≠ 1`,
3. one birational map `𝔸⁵ ⇢ P` over `𝕜`.

`BareLink 𝕜` is (1) + (3): the *link data and the transport only*.  Its content is what the
Crauder–Katz one-sided-link machinery produces for a field with a non-square
(`Work.Wire123.exists_twoSidedLink_of_not_isSquare`, `Work.Wire123.constants_separate_cylinder`):
the two charts `D(X₀)`, `D(X₀² − c)` of `𝔸⁵` carry an L-link whose two exceptional divisors have
residue fields `𝕜(t₁,…,t₄)` and `𝕜(√c)(t₁,…,t₄)`.

**So the `n = 5` case of Theorem 1.2 (3) over such a field is reduced to the single field (2)** —
one birational map `γ : P ⇢ P'` over `𝕜` whose `[κ(z₀)]`-coefficient differs from that of the link
(in the paper `γ` is the strong birationality (L2) of the two sides of the link, whose coefficients
all vanish).  Nothing else is missing: `BareLink.toMinLink` only has to be handed such a `γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The link data alone**: an L-link with two distinguished exceptional divisors of different
classes at the base point, and one birational map `𝔸⁵ ⇢ P`. -/
structure BareLink (𝕜 : Type) [Field 𝕜] where
  /-- the source fivefold of the link. -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- the target fivefold of the link. -/
  P' : Scheme.{0}
  [varietyP' : Variety 𝕜 P']
  /-- the L-link. -/
  psi : P.BirationalMap P'
  [isOverPsi : psi.IsOver (Spec (.of 𝕜))]
  /-- the exceptional divisor of `ψ`. -/
  x : P
  /-- the exceptional divisor of `ψ⁻¹`. -/
  y : P'
  /-- `ψ` has no other exceptional divisor. -/
  exDiv_psi : exDiv psi = {x}
  /-- `ψ⁻¹` has no other exceptional divisor. -/
  exDiv_psi_symm : exDiv psi.symm = {y}
  /-- the base point. -/
  ZW : Scheme.{0}
  [overZW : ZW.Over (Spec (.of 𝕜))]
  /-- the base point itself. -/
  z₀ : ZW
  /-- `κ(y) ≅ κ(z₀)`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- `κ(x) ≇ κ(z₀)`. -/
  not_resEquiv_x : ¬ ResEquiv 𝕜 x z₀
  /-- a birational map `𝔸⁵ ⇢ P` over `𝕜`. -/
  iota : (Work.CY3.Affine 𝕜 5).BirationalMap P
  [isOverIota : iota.IsOver (Spec (.of 𝕜))]

attribute [instance] BareLink.varietyP BareLink.varietyP' BareLink.isOverPsi BareLink.overZW
  BareLink.isOverIota

namespace BareLink

variable {𝕜 : Type} [Field 𝕜] (D : BareLink 𝕜)

/-- The link contributes `1` at the base point. -/
theorem cInv_psi : cInv 𝕜 D.z₀ D.psi = 1 :=
  Work.LLink.cInv_eq_one_of_exDiv_eq_singletons (𝕜 := 𝕜) (X := D.P) (Y := D.P')
    D.z₀ D.psi D.exDiv_psi D.exDiv_psi_symm D.not_resEquiv_x D.resEquiv_y

/-- **The only remaining field.**  A birational map `γ : P ⇢ P'` over `𝕜` whose coefficient at the
base point differs from that of the link turns the link data into the sharpest residual
`Work.Wire123.MinLink 𝕜`. -/
def toMinLink (γ : D.P.BirationalMap D.P') [γ.IsOver (Spec (.of 𝕜))]
    (hγ : cInv 𝕜 D.z₀ γ ≠ 1) : MinLink 𝕜 where
  P := D.P
  varietyP := D.varietyP
  P' := D.P'
  varietyP' := D.varietyP'
  psi := D.psi
  isOverPsi := D.isOverPsi
  x := D.x
  y := D.y
  exDiv_psi := D.exDiv_psi
  exDiv_psi_symm := D.exDiv_psi_symm
  ZW := D.ZW
  overZW := D.overZW
  z₀ := D.z₀
  resEquiv_y := D.resEquiv_y
  not_resEquiv_x := D.not_resEquiv_x
  gamma := γ
  isOverGamma := ‹γ.IsOver (Spec (.of 𝕜))›
  cInv_gamma_ne := hγ
  iota := D.iota
  isOverIota := D.isOverIota

/-- The `n = 5` case of Theorem 1.2 (3) from the link data and the single map `γ`. -/
theorem not_gen_five (γ : D.P.BirationalMap D.P') [γ.IsOver (Spec (.of 𝕜))]
    (hγ : cInv 𝕜 D.z₀ γ ≠ 1) : ¬ GenByPseudoRegularizable 𝕜 5 :=
  MinLink.not_gen_five (D.toMinLink γ hγ)

end BareLink

end

end Work.Wire123
