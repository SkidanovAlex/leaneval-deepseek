/-
# `Work.ParamRaysCrit`: the critical-domain Böttcher theory of the mandelbar (entry point)

`IsDynBottcher c φ` (a Böttcher coordinate on the whole escaping set `{G_c > 0}`) is satisfiable
**iff `c ∈ M*`**; for the parameter plane one must use the *critical domain*

  `critDomain c = {z | paramPotential c < greenFun c z} = {z | G_c 0 < G_c z}`,

on which `T_c` is (anti-)conformal, which contains the critical value `c` for `c ∉ M*`
(`self_mem_critDomain`), and on which Böttcher's theorem does hold for every `c`
(`BottcherExists`).  This directory is that theory.

Importing this module gives the whole parameter-plane Böttcher interface:

* the critical domain and its elementary properties, and the relation between the two Böttcher
  predicates (`CritDomain.lean`): `critDomain_subset_escapingSet`, `Tantibar_mem_critDomain`,
  `orbit_mem_critDomain`, `self_mem_critDomain`, `critDomain_eq_escapingSet`,
  `IsDynBottcher.isCritBottcher`, `isCritBottcher_iff_isDynBottcher`, `paramPotential_pos`;
* the two-sided bound `|G_c w - log ‖w‖| ≤ log 2` above the escape radius and its consequences
  (`GreenBound.lean`): `abs_greenFun_sub_log_le`, `exists_mem_critDomain_gt_norm`;
* the preconnectedness of the critical domain (`GreenLevel.lean`):
  `isPreconnected_greenFun_gt`, `isPreconnected_critDomain`;
* the modulus of a critical Böttcher coordinate (`CritBottcher/IsCritBottcher_modulus.lean`);
* uniqueness (`CritUnique/isCritBottcher_unique.lean`);
* the symmetries `c ↦ conj c` and `c ↦ ω c` (`CritTransport.lean`,
  `CritTransport/isCritBottcher_conj.lean`, `CritTransport/isCritBottcher_smul_omega.lean`);
* the abstract endgame datum at the parameters of the mandelbar:
  `Work.ParamRaysCrit.nakaneData : NakaneInput → Top.NakaneData Mb Phi`, from the divergence of
  the potential at infinity (`NakaneData/potential_tendsto_atTop.lean`) — so
  `Top.NakaneData Mb Phi` is *non-vacuous* (`NakaneDataBridge.lean`).

The definitions themselves (`critDomain`, `IsCritBottcher`, `BottcherExists`) live in
`Submission/Work/ParamRays/Bottcher.lean`, together with their dynamical counterparts.

## The public API in `Work.ParamRays`

`PublicAPI.lean` restates the main results under their `Work.ParamRays.*` names (the names used
by `ParamRays/Interface.lean`, `ParamRays/PhiUnique.lean`, `ParamRays/Phi_conj.lean`,
`ParamRays/Phi_smul_omega.lean` and by the notes `NOTES_LEAD_bottcher_iface.md` §2).
-/
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRaysCrit.GreenBound
import Submission.Work.ParamRaysCrit.GreenLevel
import Submission.Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus
import Submission.Work.ParamRaysCrit.CritUnique.isCritBottcher_unique
import Submission.Work.ParamRaysCrit.CritTransport
import Submission.Work.ParamRaysCrit.CritTransport.isCritBottcher_conj
import Submission.Work.ParamRaysCrit.CritTransport.isCritBottcher_smul_omega
import Submission.Work.ParamRaysCrit.PublicAPI
import Submission.Work.ParamRaysCrit.NakaneData.potential_tendsto_atTop
import Submission.Work.ParamRaysCrit.NakaneDataBridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

