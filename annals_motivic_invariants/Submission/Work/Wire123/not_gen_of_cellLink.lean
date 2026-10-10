import Mathlib
import Submission.Work.Wire123.CellLink
import Submission.Work.Wire123.TransLinkChallenge
import Submission.Work.Wire123.stronglyBirational_of_bigCell

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.not_gen_of_cellLink` — Theorem 1.2 (3) from the big-cell residual

The big-cell residual `Work.Wire123.CellLink 𝕜` (the `n ≥ 5` link data with the opaque (L2) clause
`Work.CY3.StronglyBirational 𝕜 P P'` replaced by the paper's *concrete* big cells
`cellP : BigCell 𝕜 5`, `cellP' : BigCell 𝕜 5` on the two sides) implies the challenge conclusion
`¬ GenByPseudoRegularizable 𝕜 n` for every `n ≥ 5`.

The proof is the comparison `CellLink.toTransLink` — a `CellLink` is a `TransLink` — together with
the transport-free wiring `Work.Wire123.theorem_1_2_3_of_transLink`:

* the only structural field of `TransLink` not copied verbatim from `CellLink` is the (L2) clause
  `StronglyBirational 𝕜 P P'`.  It is *derived* from the two big cells:
  `stronglyBirational_of_bigCell` (the paper's `lem:GP-strongly-rational`) turns each of
  `cellP`, `cellP'` into `StronglyBirational 𝕜 cellP.X (ℙ⁵)`, the identifications
  `hcellP : IsoOver 𝕜 cellP.X P` (resp. `hcellP'`) transport these along the isomorphisms over `𝕜`
  (`StronglyBirational.congr`), and the two sides are glued through `ℙ⁵`
  (`StronglyBirational.trans`, `.symm`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- A `CellLink` is a `TransLink`: the (L2) clause required by the transport-free residual is
*proved* from the two big cells of the `CellLink`, through
`stronglyBirational_of_bigCell` (`lem:GP-strongly-rational`) and the invariance of strong
birationality under the isomorphisms over `𝕜` supplied by `hcellP`, `hcellP'`. -/
def CellLink.toTransLink {𝕜 : Type} [Field 𝕜] (D : CellLink 𝕜) : TransLink 𝕜 where
  P := D.P
  P' := D.P'
  psi := D.psi
  x := D.x
  y := D.y
  exDiv_psi := D.exDiv_psi
  exDiv_psi_symm := D.exDiv_psi_symm
  Z := D.Z
  Z' := D.Z'
  isKTrivial_Z := D.isKTrivial_Z
  isKTrivial_Z' := D.isKTrivial_Z'
  picardOne_Z := D.picardOne_Z
  picardOne_Z' := D.picardOne_Z'
  ZW := D.ZW
  z₀ := D.z₀
  resEquiv_y := D.resEquiv_y
  p1Bundle_y := D.p1Bundle_y
  p1Bundle_x := D.p1Bundle_x
  stronglyBirational := by
    -- `P` is strongly birational to `ℙ⁵` via its big cell, transported along `hcellP`
    have hP : Work.CY3.StronglyBirational 𝕜 D.P (Work.CY3.ProjectiveSpace 𝕜 5) :=
      Work.CY3.StronglyBirational.congr (stronglyBirational_of_bigCell (by norm_num) D.cellP)
        D.hcellP (Work.CY3.IsoOver.refl 𝕜 (Work.CY3.ProjectiveSpace 𝕜 5))
    -- and so is `P'`, transported along `hcellP'`
    have hP' : Work.CY3.StronglyBirational 𝕜 D.P' (Work.CY3.ProjectiveSpace 𝕜 5) :=
      Work.CY3.StronglyBirational.congr (stronglyBirational_of_bigCell (by norm_num) D.cellP')
        D.hcellP' (Work.CY3.IsoOver.refl 𝕜 (Work.CY3.ProjectiveSpace 𝕜 5))
    exact Work.CY3.StronglyBirational.trans hP (Work.CY3.StronglyBirational.symm hP')
  iota := D.iota
  bridge := D.bridge
  not_stablyBirat := D.not_stablyBirat

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from the big-cell residual `CellLink 𝕜`.** -/
theorem not_gen_of_cellLink {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (D : Work.Wire123.CellLink 𝕜) : ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n :=
  theorem_1_2_3_of_transLink hn 𝕜 D.toTransLink

end

end Work.Wire123
