import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.bijective_proj_zeroComplementA

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann

/-- **The relative cohomology of the Thom pair of the tautological bundle vanishes below the
rank**, i.e. `H^j(D γ, S γ; ℤ) = 0` for `j < k`.

This is proved in the workspace for *every* real bundle of rank `n`
(`Work.Thom.subsingleton_OpenThom_genFibreA`, the fiber-general form of
`Work.Thom.subsingleton_OpenThom_of_lt_rank`), hence in particular for the tautological oriented
`k`-plane bundle `γ = tautologicalBundle k m`, whose fibre is `ℝ^k` (`Amb k`). -/
theorem openThomVanishesBelowRank (k m : ℕ) : Work.ThomBordism.Grassmann.OpenThomVanishesBelowRank k m :=
  fun j hj => Work.Thom.subsingleton_OpenThom_genFibreA (tautologicalBundle k m) j
    (by simpa [Amb] using hj)

end Work.ThomBordism.Grassmann
