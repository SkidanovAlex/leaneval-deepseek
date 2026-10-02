/-
# `Submission.Work.NAKANE` — Nakane's parameter Böttcher map: joint continuity, the exterior

Aggregator for the NAKANE area.  Everything below is axiom-clean (no `sorry`): the two classical
inputs of `Work.ParamRays.NakaneHomeo` are the *named* hypotheses `Work.NAKANE.PhiLocalHomeo` and
`Work.NAKANE.PhiInjOn` (`Submission/Work/NAKANE/Defs.lean`), and everything else is proved.

## Main exports

* `Work.NAKANE.continuous_jointGreen` (`NAKANE.GreenJoint.continuous_jointGreen`) —
  `(c,z) ↦ G_c z` is jointly continuous; consequences in the `greenFun` formulation
  (`Work.NAKANE.continuous_greenFun`), for the parameter potential
  (`Work.NAKANE.continuous_paramPotential`, `Work.NAKANE.continuous_potential`), the PARIMPL
  robustness input (`Work.NAKANE.exists_greenFun_pos_near`, `Work.NAKANE.exists_escaping_near`,
  and the discharge `Work.NAKANE.greenEscapeOpen : Work.PARIMPL.GreenEscapeOpen`), and the
  divergence of the potential (`Work.NAKANE.paramPotential_tendsto_atTop`,
  `Work.NAKANE.potential_tendsto_atTop`, `Work.NAKANE.isCompact_paramPotential_le`).
* `Work.NAKANE.continuousOn_jointVarphi` (`NAKANE.BottcherJoint`) — `(c,z) ↦ φ_c z` is jointly
  continuous on `{(c,z) | z ∈ critDomain c}`: the GATE input.  Consequences: the local formula
  `Work.NAKANE.exists_local_joint_formula`, `Work.NAKANE.continuousOn_varphiCrit_fixed`,
  `Work.NAKANE.continuousOn_jointVarphi_far` (`NAKANE.PhiApply`), and the continuity of the
  parameter map `Work.NAKANE.continuousOn_Phi` (`NAKANE.PhiContinuity`).
* `Work.NAKANE.uniformBottcherAsymptotic` (`NAKANE.Asymptotic`) —
  `Work.ParamRays.UniformBottcherAsymptotic`, **unconditionally**.
* `Work.NAKANE.exists_lipschitz_sub_id`, `Work.NAKANE.far_injOn_of_lipschitz`
  (`NAKANE.FarInjective`): `Φ - id` is `(1/2)`-Lipschitz on an outer annulus, and `Φ` is injective
  there, assuming the diagonal Lipschitz estimate of `Work.NAKANE.FarInj.exists_diagonal_lipschitz`
  for the Böttcher series (the route by which (R2) is eliminated).
* `Work.NAKANE.InjOfFar.isProperMap_phiExt` (`NAKANE.InjOfFar`): `phiExt : ↥Mbᶜ → ↥extDisc` is a
  *proper* map, and `Work.NAKANE.InjOfFar.injOn_of_localHomeo_of_farInj`: (R1) plus injectivity on
  one far annulus already gives (R2).
* Nakane's homeomorphism theorem.  The strongest forms are in `NAKANE.Assembly`:
  * `Work.NAKANE.phi_far_injective` — `Φ` is injective on an outer annulus, **unconditionally**;
  * `Work.NAKANE.injOn_of_localHomeo` — **(R2) follows from (R1) alone**;
  * `Work.NAKANE.nakaneHomeo_of_localHomeo (hloc : PhiLocalHomeo) : Work.ParamRays.NakaneHomeo`
    — **Nakane's homeomorphism theorem from the single classical input (R1)**;
  * `Work.NAKANE.phi_bijOn_of_localHomeo` — `Set.BijOn Φ Mbᶜ extDisc` from (R1).
  The two-input version `Work.NAKANE.nakaneHomeo_of_localHomeo_of_injOn` and the
  openness-based `Work.NAKANE.nakaneHomeo_of_openMap_of_injOn` are in `NAKANE.NakaneHomeo`,
  together with their supporting results (`Work.NAKANE.isOpen_image_Phi_of_localHomeo`,
  `Work.NAKANE.phiExt`, `Work.NAKANE.mem_image_Phi_of_localHomeo_of_one_lt`,
  `Work.NAKANE.PhiClosed.*`, `Work.NAKANE.PhiProper.*`).
-/
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.NAKANE.BottcherJoint
import Submission.Work.NAKANE.PhiContinuity
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.PhiApply
import Submission.Work.NAKANE.Asymptotic
import Submission.Work.NAKANE.NakaneHomeo
import Submission.Work.NAKANE.FarInjective
import Submission.Work.NAKANE.InjOfFar.injOn_of_localHomeo_of_farInj
import Submission.Work.NAKANE.FarInj.exists_diagonal_lipschitz
import Submission.Work.NAKANE.Assembly
import Submission.Work.NAKANE.PhiClosed.mem_image_Phi_of_mem_closure
import Submission.Work.NAKANE.PhiProper.isCompact_Phi_preimage
import Submission.Work.NAKANE.GreenEscapeOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

