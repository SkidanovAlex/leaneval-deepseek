/-
# The critical-domain Böttcher interface under its `Work.ParamRays.*` names

The main results of the `ParamRaysCrit` area are proved in submodules whose namespaces follow
their file paths (`Work.ParamRaysCrit.CritBottcher.*`, `Work.ParamRaysCrit.CritUnique.*`,
`Work.ParamRaysCrit.CritTransport.*`).  This file restates them under the names requested by
`Submission/Work/NOTES_LEAD_bottcher_iface.md` §2, in the namespace `Work.ParamRays` where the
rest of the parameter-ray interface lives, so that a caller can use the whole interface with the
single import `Submission.Work.ParamRaysCrit.All`.

The remaining items of §2 already live in this namespace:

* `Work.ParamRays.critDomain`, `Work.ParamRays.IsCritBottcher`, `Work.ParamRays.BottcherExists`
  (`ParamRays/Bottcher.lean`);
* `Work.ParamRays.critDomain_subset_escapingSet`, `Work.ParamRays.Tantibar_mem_critDomain`,
  `Work.ParamRays.self_mem_critDomain`, `Work.ParamRays.critDomain_eq_escapingSet`,
  `Work.ParamRays.IsDynBottcher.isCritBottcher`,
  `Work.ParamRays.isCritBottcher_iff_isDynBottcher`, `Work.ParamRays.paramPotential_pos`
  (`ParamRaysCrit/CritDomain.lean`);
* `Work.ParamRays.isPreconnected_critDomain` (`ParamRaysCrit/GreenLevel.lean`);
* `Work.ParamRays.greenFun_conj`, `Work.ParamRays.mem_critDomain_conj`,
  `Work.ParamRays.mem_critDomain_smul_omega` (`ParamRaysCrit/CritTransport.lean`).
-/
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRaysCrit.GreenBound
import Submission.Work.ParamRaysCrit.GreenLevel
import Submission.Work.ParamRaysCrit.CritTransport
import Submission.Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus
import Submission.Work.ParamRaysCrit.CritUnique.isCritBottcher_unique
import Submission.Work.ParamRaysCrit.CritTransport.isCritBottcher_conj
import Submission.Work.ParamRaysCrit.CritTransport.isCritBottcher_smul_omega

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

/-- The modulus of a critical Böttcher coordinate is the exponential of the Green function. -/
theorem IsCritBottcher_modulus {c : ℂ} {φ : ℂ → ℂ} (h : IsCritBottcher c φ) {z : ℂ}
    (hz : z ∈ critDomain c) : ‖φ z‖ = Real.exp (greenFun c z) :=
  Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus h hz

/-- Two critical Böttcher coordinates of `T_c` agree on the critical domain. -/
theorem isCritBottcher_unique {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsCritBottcher c φ)
    (hψ : IsCritBottcher c ψ) {z : ℂ} (hz : z ∈ critDomain c) : φ z = ψ z :=
  Work.ParamRaysCrit.CritUnique.isCritBottcher_unique hφ hψ hz

/-- Complex conjugation transports critical Böttcher coordinates. -/
theorem isCritBottcher_conj {c : ℂ} {φ : ℂ → ℂ} (hφ : IsCritBottcher c φ) :
    IsCritBottcher (conj c) (fun w : ℂ => conj (φ (conj w))) :=
  Work.ParamRaysCrit.CritTransport.isCritBottcher_conj hφ

/-- The rotation `c ↦ ω c` transports critical Böttcher coordinates. -/
theorem isCritBottcher_smul_omega {c : ℂ} {φ : ℂ → ℂ} (hφ : IsCritBottcher c φ) :
    IsCritBottcher (omega * c) (fun w : ℂ => omega * φ (w / omega)) :=
  Work.ParamRaysCrit.CritTransport.isCritBottcher_smul_omega hφ

end Work.ParamRays
