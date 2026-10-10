import Submission.Work.Totaro.Interface
import Submission.Work.K3Inputs.Main

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro.Cylinder` — the Totaro input in the vocabulary of the K3-INPUTS area

The K3-INPUTS area (`Submission/Work/K3Inputs`) carries out the ℙ¹-bundle bridge and the cylinder
calculus of the K3 link in the *instance-free* model `Work.K3Inputs.StablyBirat` of stable
birationality, and states the distinguishing which the `cInv` count needs as the non-isomorphism of
the cylinder function fields `κ(S)(t) ≇ κ(S')(t)` (`Work.K3Inputs.SameCylinderField`), given the
cylinder rigidity (F2) (`Work.K3Inputs.CylinderRigid`).

This module provides the same statements with the *cohomological input* in place of the chapter's
`TotaroInput` (and with the paper's `cor-CYnSB` in place of it as well), so that the K3 packaging
can be run off `Work.Totaro.CohDistinguishing` end to end:

* `Work.Totaro.not_sameCylinderField_of_distinguishing` — the `z₀`-cylinder-field distinguishing
  from `CohDistinguishing` (this is `Work.K3Inputs.not_sameCylinderField_of_totaro` with
  `Work.K3.TotaroInput` replaced by `Work.Totaro.totaroInput_K3`);
* `Work.Totaro.not_sameCylinderField_of_CorCYnSB` — the same from the paper's `cor-CYnSB`;
* `Work.Totaro.not_stablyBirat_of_cohom` — a per-pair certificate gives the instance-free
  non-stable-birationality of `Work.K3Inputs.StablyBirat`.

`𝔸¹` is our model of `ℙ¹` throughout (only the birational class matters), exactly as in the K3-INPUTS
area.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The `z₀`-cylinder-field distinguishing from the cohomological input.**  For the two centres
`S`, `S'` of an L-link (non-isomorphic `K`-trivial varieties of Picard rank one, with the cylinder
rigidity (F2)), the cylinder function fields `κ(S)(t)` and `κ(S')(t)` are not isomorphic — the
input `¬ ResEquiv 𝕜 y x` of `Work.K3.K3Link`, at the level of the function fields of the two
exceptional divisors. -/
theorem not_sameCylinderField_of_distinguishing {S S' : Scheme.{0}} [Variety 𝕜 S]
    [Variety 𝕜 S'] (hrigid : Work.K3Inputs.CylinderRigid 𝕜 S S')
    (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜))
    (hS : IsKTrivial 𝕜 S) (hS' : IsKTrivial 𝕜 S')
    (pS : Work.K3.PicardRankOneGeom 𝕜 S) (pS' : Work.K3.PicardRankOneGeom 𝕜 S')
    (hne : ¬ IsoOver 𝕜 S S') : ¬ Work.K3Inputs.SameCylinderField 𝕜 S S' :=
  Work.K3Inputs.not_sameCylinderField_of_totaro hrigid
    ((totaroInput_K3 h).toInputAt 𝕜 hS hS' pS pS') hne

/-- The same, from the paper's `cor-CYnSB` (`Submission/Work/Totaro/Paper.lean`) instead of the
cohomological input. -/
theorem not_sameCylinderField_of_CorCYnSB {S S' : Scheme.{0}} [Variety 𝕜 S]
    [Variety 𝕜 S'] (hrigid : Work.K3Inputs.CylinderRigid 𝕜 S S')
    (C : CorCYnSB 𝕜 (Work.K3.PicardRankOneGeom 𝕜))
    (hS : IsKTrivial 𝕜 S) (hS' : IsKTrivial 𝕜 S')
    (pS : Work.K3.PicardRankOneGeom 𝕜 S) (pS' : Work.K3.PicardRankOneGeom 𝕜 S')
    (hne : ¬ IsoOver 𝕜 S S') : ¬ Work.K3Inputs.SameCylinderField 𝕜 S S' :=
  Work.K3Inputs.not_sameCylinderField_of_totaro hrigid
    ((totaroInput_K3_of_CorCYnSB C).toInputAt 𝕜 hS hS' pS pS') hne

/-- **A per-pair certificate gives the instance-free non-stable-birationality of
`Work.K3Inputs.StablyBirat`** (the relation used by the bridge and the cylinder calculus of the
K3-INPUTS area).  This is `Work.Totaro.CohSeparation.not_stablyBirational` transported across
`Work.K3Inputs.StablyBirat_to_stablyBirational`. -/
theorem not_stablyBirat_of_cohom {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (C : CohSeparation 𝕜 X Y) : ¬ Work.K3Inputs.StablyBirat 𝕜 X Y :=
  Work.K3Inputs.not_stablyBirat_of_not_stablyBirational X Y C.not_stablyBirational

/-- **The universal cohomological input gives the instance-free non-stable-birationality of the
two centres**, in the shape in which the K3-INPUTS cylinder layer consumes it. -/
theorem not_stablyBirat_of_distinguishing {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    {Pic1 : Pic1Family 𝕜} (h : CohDistinguishing 𝕜 Pic1)
    (hX : IsKTrivial 𝕜 X) (hY : IsKTrivial 𝕜 Y) (pX : Pic1 X) (pY : Pic1 Y)
    (hne : ¬ IsoOver 𝕜 X Y) : ¬ Work.K3Inputs.StablyBirat 𝕜 X Y :=
  not_stablyBirat_of_cohom (h X Y hX hY pX pY hne).some.toCohSeparation

end

end Work.Totaro
