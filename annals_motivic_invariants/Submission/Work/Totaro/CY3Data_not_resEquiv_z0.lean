import Mathlib
import Submission.Work.Totaro.Cohomology
import Submission.Work.CY3.Main

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Totaro

/-- **The `z₀`-residue-field distinguishing of the CY3 link, from the cohomological input.**  In the CY3 L-link the coefficient is computed at the base point `z₀` with `κ(z₀) = κ(Z)(t)` (`Work.CY3.CY3Data.resEquiv_y`: `κ(y) ≅ κ(z₀)`); the invariant coefficient `1` rests on the *other* exceptional divisor `x` being distinguished from `z₀`, i.e. `κ(x) ≇ κ(z₀)`.  This is `Work.CY3.CY3Link.not_resEquiv_x` with `Work.CY3.TotaroInput` replaced by the cohomological input. -/
theorem CY3Data_not_resEquiv_z0 {𝕜 : Type} [Field 𝕜] (D : Work.CY3.CY3Data 𝕜)
    (h : Work.Totaro.CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜))
    (hne : ¬ Work.Totaro.IsoOver 𝕜 D.Z D.Z') :
    ¬ ResEquiv 𝕜 D.x D.z₀ := by
  -- Assume `κ(x) ≅ κ(z₀)`.  Since `κ(y) ≅ κ(z₀)` too (`D.resEquiv_y`), transitivity gives
  -- `κ(y) ≅ κ(x)`, i.e. an isomorphism of the two exceptional divisors' function fields.
  intro hres
  have hyx : ResEquiv 𝕜 D.y D.x :=
    Work.Motivic.ResEquiv.symm
      (Work.Motivic.ResEquiv.trans hres (Work.Motivic.ResEquiv.symm D.resEquiv_y))
  -- The `ℙ¹`-bundle bridge then makes the two centres `Z`, `Z'` stably birational ...
  have hsb : Work.Totaro.StablyBirational 𝕜 D.Z D.Z' := D.bridge hyx
  -- ... which the cohomological distinguishing of the two centres forbids.
  exact Work.Totaro.not_stablyBirational_of_distinguishing h D.isKTrivial_Z D.isKTrivial_Z'
    D.picardOne_Z D.picardOne_Z' hne hsb

end Work.Totaro
