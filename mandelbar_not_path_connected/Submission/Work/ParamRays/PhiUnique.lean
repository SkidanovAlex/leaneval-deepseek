/-
# The parameter Böttcher map and Böttcher coordinates: the bridge and its symmetries

`Work.ParamRays.Phi c` is defined by `Classical.choose` from the existence of a **critical**
Böttcher coordinate of `T_c` (`IsCritBottcher c φ`, a Böttcher coordinate on the critical domain
`critDomain c = {G_c > G_c 0}`); `isCritBottcher_unique` makes this canonical, and this file
records the resulting *bridge*: `Phi c` is the value at the critical value of every critical
Böttcher coordinate.

## Main results

* `Work.ParamRays.Phi_eq_of_isCritBottcher` : `Phi c = φ c` for `c ∉ Mb` and any *critical*
  Böttcher coordinate `φ` of `T_c` (this is the form used by the parameter-ray theory).
* `Work.ParamRays.Phi_eq_of_isDynBottcher` : the same for a *dynamical* Böttcher coordinate
  `IsDynBottcher c φ` (kept for compatibility; that predicate is satisfiable only for
  `c ∈ M*`, so its content off the mandelbar is empty).
* `Work.ParamRays.Phi_ne_zero`, `Work.ParamRays.Phi_eq_iff` : consequences.
-/
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRaysCrit.CritUnique.isCritBottcher_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The bridge.**  Off the mandelbar, `Phi c` is the value of *every* critical Böttcher
coordinate of `T_c` at the critical value `c`. -/
theorem Phi_eq_of_isCritBottcher {c : ℂ} (hc : c ∉ Mb) {φ : ℂ → ℂ}
    (hφ : IsCritBottcher c φ) : Phi c = φ c := by
  have h : ∃ ψ : ℂ → ℂ, IsCritBottcher c ψ := ⟨φ, hφ⟩
  rw [Phi_eq_choose hc h]
  exact Work.ParamRaysCrit.CritUnique.isCritBottcher_unique
    (Classical.choose_spec h) hφ (self_mem_critDomain hc)

/-- The same bridge for a *dynamical* Böttcher coordinate.  (Kept for compatibility: by
`IsDynBottcher.isCritBottcher` such a `φ` is in particular a critical Böttcher coordinate.  Note
that `IsDynBottcher c φ` is satisfiable only for `c ∈ M*`.) -/
theorem Phi_eq_of_isDynBottcher {c : ℂ} (hc : c ∉ Mb) {φ : ℂ → ℂ}
    (hφ : IsDynBottcher c φ) : Phi c = φ c :=
  Phi_eq_of_isCritBottcher hc hφ.isCritBottcher

/-- Two Böttcher coordinates of `T_c` give the same value at the critical value `c` whenever the
critical value escapes, i.e. outside the mandelbar. -/
theorem IsDynBottcher.eq_at_criticalValue {c : ℂ} (hc : c ∉ Mb) {φ ψ : ℂ → ℂ}
    (hφ : IsDynBottcher c φ) (hψ : IsDynBottcher c ψ) : φ c = ψ c :=
  isDynBottcher_unique hφ hψ (escapes_criticalValue hc)

/-- Two critical Böttcher coordinates of `T_c` agree at the critical value outside the
mandelbar (where the critical value lies in the critical domain). -/
theorem IsCritBottcher.eq_at_criticalValue {c : ℂ} (hc : c ∉ Mb) {φ ψ : ℂ → ℂ}
    (hφ : IsCritBottcher c φ) (hψ : IsCritBottcher c ψ) : φ c = ψ c :=
  Work.ParamRaysCrit.CritUnique.isCritBottcher_unique hφ hψ (self_mem_critDomain hc)

/-- `Phi` does not vanish outside the mandelbar. -/
theorem Phi_ne_zero (hB : BottcherExists) {c : ℂ} (hc : c ∉ Mb) : Phi c ≠ 0 := by
  intro h
  have h1 : ‖Phi c‖ = 0 := by rw [h, norm_zero]
  have h2 : 1 < ‖Phi c‖ := one_lt_norm_Phi hB hc
  linarith

end Work.ParamRays
