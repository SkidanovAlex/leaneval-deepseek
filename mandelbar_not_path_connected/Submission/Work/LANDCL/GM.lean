/-
Copyright: subproject `Submission/Work/LANDCL/` of `mandelbar_not_path_connected`.

# `gm` : Goldberg–Milnor B.1 in the parameter form

The target of this file is `Work.FSeed.RepellingRayParamStable` (row `gm` of the delivery table
of `Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §4): a parameter at which the dynamic ray
`R_c(θ)` lands at a *repelling* periodic point is not a limit point of the parameter ray `R(θ)`.

It is proved here from three inputs:

* `Work.LANDCL.GoldbergMilnorB1` — the *dynamical* form of Goldberg–Milnor B.1: at a ray landing
  at a repelling periodic point the landing is stable in the parameter (points of the critical
  rays at nearby parameters, at levels tending to `1`, accumulate only at the landing point);
* `Work.ParamRays.NakaneInput` — the parameter Böttcher map, through
  `Work.ParamRays.continuous_potential` (the potential is continuous with value `0` on the
  mandelbar), giving the level `‖Φ cₙ‖ → 1` along the parameter ray;
* `Work.LANDCL.DynBottcherOnlyOnMandelbar` — a Böttcher coordinate on the *whole* escaping set
  exists only inside the mandelbar (`landsAt` therefore forces `c ∈ Mb`).

The reduction: if `cₙ ∈ R(θ)` and `cₙ → c`, then the critical value `cₙ = T_{cₙ}(0)` is a point
of the critical ray of `T_{cₙ}` at angle `θ` (`Work.LANDCL.GM.mem_critRaySet_of_mem_paramRay`)
at level `‖Φ cₙ‖ → 1`, so `cₙ → y` by Goldberg–Milnor B.1; but `cₙ → c`, so `c = y`, and `y` is
a *repelling* periodic point while `c = T_c(0)` is the critical value — impossible by
`Work.LANDCL.not_isRepelling_criticalValue`. -/
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.GM.mem_mandelbar_of_landsAt
import Submission.Work.LANDCL.GM.mem_critRaySet_of_mem_paramRay
import Submission.Work.LANDCL.GM.tendsto_norm_Phi_of_tendsto_paramRay
import Submission.Work.LANDCL.Critical.not_isRepelling_criticalValue
import Submission.Work.ParamRays.PhiUnique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LANDCL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **`gm` — Goldberg–Milnor B.1 in the parameter form** (`Work.FSeed.RepellingRayParamStable`).

`hN` is the parameter Böttcher input of the `ParamRays` area, `hB1` the dynamical stability of
the landing at a repelling point (`Work.LANDCL.GoldbergMilnorB1`), and `honMb` the scope
statement that a Böttcher coordinate on the whole escaping set exists only in the mandelbar. -/
theorem repellingRayParamStable (hN : Work.ParamRays.NakaneInput) (hB1 : GoldbergMilnorB1)
    (honMb : DynBottcherOnlyOnMandelbar) : Work.FSeed.RepellingRayParamStable := by
  intro c k y θ hrep hland hc
  obtain ⟨cn, hmem, htend⟩ := mem_closure_iff_seq_limit.mp hc
  have hcMb : c ∈ Mandelbar := GM.mem_mandelbar_of_landsAt honMb hland
  have hlev : Tendsto (fun n : ℕ => ‖Work.ParamRays.Phi (cn n)‖) atTop (𝓝 1) :=
    GM.tendsto_norm_Phi_of_tendsto_paramRay hN hcMb hmem htend
  have hcrit : ∀ n : ℕ, ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher (cn n) φ ∧
      cn n ∈ Work.ParamRays.critDomain (cn n) ∧ φ (cn n) = Work.ParamRays.Phi (cn n) := by
    intro n
    have hnm : cn n ∉ Mandelbar := (Work.ParamRays.mem_paramRay.mp (hmem n)).1
    obtain ⟨φ, hφ⟩ := hN.bottcher (cn n) hnm
    exact ⟨φ, hφ, Work.ParamRays.self_mem_critDomain hnm,
      (Work.ParamRays.Phi_eq_of_isCritBottcher hnm hφ).symm⟩
  have hray : ∀ n : ℕ, ∃ r : ℝ, 1 < r ∧
      Work.ParamRays.Phi (cn n) = (r : ℂ) * Work.ParamRays.rayDir θ :=
    fun n => (Work.ParamRays.mem_paramRay.mp (hmem n)).2
  have hy : c = y := hB1 c θ k y hrep hland cn (fun n : ℕ => Work.ParamRays.Phi (cn n)) cn
    hcrit hray htend hlev c htend
  exact Critical.not_isRepelling_criticalValue c k (by simpa [hy.symm] using hrep)

/-! ## The `hθ` clause -/

/-- **`hθ` in the vocabulary of `LANDCL`**: at a parameter at which the window ray `R(23/63)`
lands at a repelling periodic point (the `repAngle` deliverable,
`Work.Final.ParamAngleRepelling c`), the parameter ray `R(23/63)` does not accumulate. -/
theorem notMem_closure_paramRay_windowAngle (hgm : Work.FSeed.RepellingRayParamStable)
    {c : ℂ} (hrep : Work.Final.ParamAngleRepelling c) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) := by
  obtain ⟨k, y, hkrep, hkland⟩ := hrep
  exact hgm c k y Work.Landing.paramAngle hkrep hkland

end Work.LANDCL
