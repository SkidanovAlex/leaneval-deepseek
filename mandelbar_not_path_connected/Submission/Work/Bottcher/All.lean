/-
# `Work.Bottcher` — the Böttcher chapter of the mandelbar project (BOT-2)

Single entry point importing the whole chapter.  See `NOTES.md` for the
documentation, in particular §4 for the branch defect of the product formula
`Work.Bottcher.bottcher` and §5 for the recommended API.

* definitions: `Submission.Work.Bottcher.Defs` (`Work.Bottcher.bottcher`,
  `Phi`, `green`, `CritDomain`, `dynamicRayOf`, `dynamicRay`, `paramRay`, …)
* the product formula: `Series/`, `Core/`
* the domain `{G_c > G_c(0)}` and the critical value: `Critical/`, `CritBasic.lean`
* **the existence of the Böttcher coordinate on the critical domain, the parameter
  coordinate at the critical value, and the dynamic rays of the analytic coordinate:
  `CritBottcherExists.lean`** (the main export `Work.Bottcher.bottcherExists_crit`)
* the construction of the logarithm of `p_c z / z^4`: `Contraction/`
* Green-function facts used here: `Green/`
* dynamic rays and the angle-doubling rule: `Rays/`
-/
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Contraction.preimage_pMap_eq_iff
import Submission.Work.Bottcher.Contraction.norm_pow_four_le_of_pMap_eq
import Submission.Work.Bottcher.Series.summable_bottcherTerm
import Submission.Work.Bottcher.Series.tendsto_bottcherPartial
import Submission.Work.Bottcher.Core.ProductFormulaTelescoping
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.bottcher_comm_pMap
import Submission.Work.Bottcher.Core.bottcher_comm_pMap_domain
import Submission.Work.Bottcher.Core.bottcher_comm_Tantibar_far
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Core.norm_bottcher_Tantibar
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green
import Submission.Work.Bottcher.Critical.mem_CritDomain_self_iff
import Submission.Work.Bottcher.Critical.CritDomain_escapes
import Submission.Work.Bottcher.Critical.CritDomain_pMap_mem
import Submission.Work.Bottcher.Critical.CritDomain_Tantibar_mem
import Submission.Work.Bottcher.Critical.CritDomain_Tantibar_ne_zero
import Submission.Work.Bottcher.Critical.norm_Phi_eq_exp_green
import Submission.Work.Bottcher.Critical.Phi_isBigO_atTop
import Submission.Work.Bottcher.Critical.potential_eq_green
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.Bottcher.Green.green_eq_zero_iff_bounded
import Submission.Work.Bottcher.Green.bounded_or_escapes
import Submission.Work.Bottcher.Green.eventually_not_mem_mandelbar
import Submission.Work.Bottcher.Rays.dynamicRay_period
import Submission.Work.Bottcher.Rays.Tantibar_maps_dynamicRayOf
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Contraction.green_eq_greenFun
import Submission.Work.Bottcher.Contraction.isPreconnected_green_le_greenParam
import Submission.Work.Bottcher.Contraction.exists_orbit_zero_bound
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_le
import Submission.Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero_of_preconnected
import Submission.Work.Bottcher.Contraction.analyticOnNhd_log_of_exp_eq_CritDomain
import Submission.Work.Bottcher.Contraction.exists_continuous_log_of_monodromy_CritDomain
import Submission.Work.Bottcher.Contraction.exists_analytic_log_normFactor_of_CritDomain
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic_tail
import Submission.Work.Bottcher.Contraction.exists_analyticBottcher_of_CritDomain
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_on_CritDomain
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

