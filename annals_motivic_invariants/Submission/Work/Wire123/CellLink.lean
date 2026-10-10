import Submission.Work.Wire123.BigCell
import Submission.Work.Wire123.TransLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.CellLink` — the residual with (L2) replaced by *concrete* cell data

`Work.Wire123.TransLink 𝕜` (and the delivered `Work.CY3.CY3Data 𝕜`) carries the (L2) clause of an
L-link as an opaque field, `Work.CY3.StronglyBirational 𝕜 P P'`.  By
`Work.Wire123.stronglyBirational_of_bigCell` (the paper's `lem:GP-strongly-rational`, proved in this
directory) that clause is *derived* from concrete geometry: a dense open `U ⊆ P` over `𝕜` with
`U ≅ 𝔸⁵` whose complement is a single divisor of the class of a hyperplane — exactly the Bruhat big
cell of the paper's `G/P`, `G/P'`.

`CellLink 𝕜` is the residual with that substitution: the link data of `TransLink` with the opaque
`stronglyBirational` field replaced by `cellP`, `cellP'` (the two big cells, one on each side).

`Work.Wire123.CellLink.toTransLink` (delegated) is the comparison: a `CellLink` is a `TransLink`, so
the whole `n ≥ 5` wiring applies to it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The `n ≥ 5` residual with (L2) replaced by the paper's big-cell hypothesis.** -/
structure CellLink (𝕜 : Type) [Field 𝕜] where
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
  /-- a model of `Z × ℙ¹`. -/
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
  /-- the transport `𝔸⁵ ⇢ P` (no coefficient condition). -/
  iota : (Work.CY3.Affine 𝕜 5).BirationalMap P
  [isOverIota : iota.IsOver (Spec (.of 𝕜))]
  /-- the `ℙ¹`-bundle bridge. -/
  bridge : ResEquiv 𝕜 y x → Work.CY3.StablyBirational 𝕜 Z Z'
  /-- the conclusion of Totaro's `cor-CYnSB` at the two centres. -/
  not_stablyBirat : ¬ Work.CY3.StablyBirational 𝕜 Z' Z
  /-- **the big cell of the source fivefold** (paper `lem:GP-strongly-rational`). -/
  cellP : BigCell 𝕜 5
  /-- it is a big cell *of `P`*, compatibly with the structure morphisms over `𝕜`
  (`Work.CY3.IsoOver`, the form in which `Work.CY3.StronglyBirational.congr` transports it). -/
  hcellP : Work.CY3.IsoOver 𝕜 cellP.X P
  /-- **the big cell of the target fivefold**. -/
  cellP' : BigCell 𝕜 5
  /-- it is a big cell *of `P'`**. -/
  hcellP' : Work.CY3.IsoOver 𝕜 cellP'.X P'

attribute [instance] CellLink.varietyP CellLink.varietyP' CellLink.isOverPsi CellLink.varietyZ
  CellLink.varietyZ' CellLink.overZW CellLink.isOverIota

end

end Work.Wire123
