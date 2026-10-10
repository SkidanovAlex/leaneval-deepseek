import Submission.Work.CY3.Link
import Submission.Work.Wire123.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.LeanLink` — the `CY3Data` fields the counting chain actually consumes

`Work.CY3.CY3Data 𝕜` carries, besides its mathematical content, the whole `G₂`/Layer-2 scaffolding
(`G2Grassmannian` and `CY3Section`: the group scheme, the flag variety, the two Grassmannians, the
general section, the blow-up identifications, the `ℙ¹`-fibrations, the strong rationality of the two
quotients).  None of that is consumed by the `n ≥ 5` counting chain — `Work.CY3Stab`'s
`exists_cInv_ne_zero_of_CY3Data` and this directory's
`Work.Wire123.exists_cInv_ne_zero_of_CY3Data_sep` use only

`Z`, `Z'` (the two centres), `x`, `y` (the two exceptional divisors), `psi` with `exDiv psi = {x}`,
`exDiv psi.symm = {y}`, the base point `z₀` with `κ(y) ≅ κ(z₀)`, the two transports
`ε : 𝔸⁵ ⇢ P`, `δ : P' ⇢ 𝔸⁵` with vanishing coefficient at `z₀`, the two `ℙ¹`-bundle
identifications, the two `bridge`/separation clauses, the *strong* birationality
`StronglyBirational 𝕜 P P'` (which builds the vanishing cylinder `S`), and the two fieldless
predicates `IsKTrivial`, `PicardRankOne`.

`LeanLink 𝕜` is exactly that list, with the *same field names* as `CY3Data`, so that the chain's
proof transfers verbatim.  It is the interface a produced L-link (e.g.
`Work.Wire123.exists_twoSidedLink_of_not_isSquare`) can populate without any `G₂` input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The content of `Work.CY3.CY3Data 𝕜`**: the two centres, the link with its two exceptional
divisors, the base point, the two transports with vanishing coefficient, the two `ℙ¹`-bundle
identifications, the bridge and the non-stable-birationality — and nothing else. -/
structure LeanLink (𝕜 : Type) [Field 𝕜] where
  /-- the ambient fivefold of the link (`G/P` in the paper). -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- the target fivefold of the link (`G/P'` in the paper). -/
  P' : Scheme.{0}
  [varietyP' : Variety 𝕜 P']
  /-- the L-link `ψ = τ' ∘ τ⁻¹`. -/
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
  /-- the first centre. -/
  Z : Scheme.{0}
  [varietyZ : Variety 𝕜 Z]
  /-- the second centre. -/
  Z' : Scheme.{0}
  [varietyZ' : Variety 𝕜 Z']
  /-- `K`-triviality of the first centre (fieldless named predicate). -/
  isKTrivial_Z : Work.CY3.IsKTrivial 𝕜 Z
  /-- `K`-triviality of the second centre. -/
  isKTrivial_Z' : Work.CY3.IsKTrivial 𝕜 Z'
  /-- Picard rank one of the first centre (fieldless named predicate). -/
  picardOne_Z : Work.CY3.PicardRankOne 𝕜 Z
  /-- Picard rank one of the second centre. -/
  picardOne_Z' : Work.CY3.PicardRankOne 𝕜 Z'
  /-- a model of `Z × ℙ¹` (only its point `z₀` and the identification are used). -/
  ZW : Scheme.{0}
  [overZW : ZW.Over (Spec (.of 𝕜))]
  /-- the base point of the invariant. -/
  z₀ : ZW
  /-- `κ(y) ≅ κ(z₀)`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- (F1): `y` is a `ℙ¹`-bundle over the first centre. -/
  p1Bundle_y : Work.K3Inputs.IsP1BundleOver 𝕜 y Z
  /-- (F1): `x` is a `ℙ¹`-bundle over the second centre. -/
  p1Bundle_x : Work.K3Inputs.IsP1BundleOver 𝕜 x Z'
  /-- the transport `𝔸⁵ ⇢ P`. -/
  eps : (Work.CY3.Affine 𝕜 5).BirationalMap P
  [isOverEps : eps.IsOver (Spec (.of 𝕜))]
  /-- the transport `P' ⇢ 𝔸⁵`. -/
  delta : P'.BirationalMap (Work.CY3.Affine 𝕜 5)
  [isOverDelta : delta.IsOver (Spec (.of 𝕜))]
  /-- `ε` contributes nothing at the base point. -/
  cInv_eps : cInv 𝕜 z₀ eps = 0
  /-- `δ` contributes nothing at the base point. -/
  cInv_delta : cInv 𝕜 z₀ delta = 0
  /-- **(L2)**: the two sides of the link are *strongly* birational to each other — the input the
  delivered chain consumes (through `Work.CY3.G2Grassmannian.stronglyBirational`) to build the
  vanishing cylinder `S : P' × 𝔸ᵏ ⇢ P × 𝔸ᵏ`.  For the paper's `G/P`, `G/P'` it is
  `lem:GP-strongly-rational`; it is *not* implied by the other fields (a link with `cInv ≠ 0` at the
  cylinder point of `x` cannot be strongly birational to its own inverse). -/
  stronglyBirational : Work.CY3.StronglyBirational 𝕜 P P'
  /-- the `ℙ¹`-bundle bridge: an isomorphism of the two cylinder fields forces stable
  birationality of the two centres. -/
  bridge : ResEquiv 𝕜 y x → Work.CY3.StablyBirational 𝕜 Z Z'
  /-- the conclusion of Totaro's `cor-CYnSB` at the two centres. -/
  not_stablyBirat : ¬ Work.CY3.StablyBirational 𝕜 Z' Z

attribute [instance] LeanLink.varietyP LeanLink.varietyP' LeanLink.isOverPsi LeanLink.varietyZ
  LeanLink.varietyZ' LeanLink.overZW LeanLink.isOverEps LeanLink.isOverDelta

end

end Work.Wire123
