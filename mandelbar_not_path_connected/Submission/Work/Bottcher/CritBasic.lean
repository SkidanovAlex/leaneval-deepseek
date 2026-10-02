/-
# The critical domain `CritDomain c = {G_c > G_c 0}`: basic API

This file collects the elementary facts about the Böttcher chapter's critical domain
`Work.Bottcher.CritDomain c = {z | greenParam c < green c z}` which the construction of the
analytic Böttcher coordinate needs.  It is the bridge between the *escape* chapter
(`Work.Escape`, whence `green`) and the *parameter-ray* chapter (`Work.ParamRays`), and it makes
`Work.Bottcher.CritDomain c` literally `Work.ParamRays.critDomain c`, so that the topological
work of the `ParamRaysCrit` area (`isPreconnected_critDomain`, `exists_mem_critDomain_gt_norm`)
is available here.

## Main results

* `Work.Bottcher.CritBasic.critDomain_eq` : `CritDomain c = ParamRays.critDomain c`.
* `Work.Bottcher.CritBasic.isOpen_CritDomain`, `...isPreconnected_CritDomain`,
  `...nonempty_CritDomain`.
* `Work.Bottcher.CritBasic.Tantibar_mem_CritDomain`, `...pMap_mem_CritDomain`,
  `...pMap_iterate_mem_CritDomain`, `...zero_notMem_CritDomain`.
* `Work.Bottcher.CritBasic.normFactor_ne_zero_of_mem_CritDomain`,
  `...analyticOnNhd_normFactor_CritDomain`.
* `Work.Bottcher.CritBasic.exists_mem_CritDomain_gt_norm`, `...critFarRadius`,
  `...critFar_subset_CritDomain` : the Böttcher coordinate is analytic on the region
  `{critFarRadius c < ‖z‖}`, which is contained in `CritDomain c`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.continuous_green
import Submission.Work.Escape.log_half_le_green
import Submission.Work.Escape.greenParam_eq_paramPotential
import Submission.Work.Bottcher.Contraction.green_eq_greenFun
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRaysCrit.GreenBound
import Submission.Work.ParamRaysCrit.GreenLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.CritBasic

open Filter
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The escape chapter's Green function of the tricorn family is the parameter-ray chapter's. -/
theorem green_eq (c z : ℂ) : Work.Bottcher.green c z = Work.ParamRays.greenFun c z :=
  Work.Bottcher.Contraction.green_eq_greenFun c z

/-- The two definitions of the critical potential agree. -/
theorem greenParam_eq (c : ℂ) : Work.Bottcher.greenParam c = Work.ParamRays.paramPotential c :=
  Work.Escape.greenParam_eq_paramPotential c

/-- **The critical domain is the `ParamRays` critical domain.** -/
theorem critDomain_eq (c : ℂ) : Work.Bottcher.CritDomain c = Work.ParamRays.critDomain c := by
  ext z
  rw [Work.Bottcher.mem_CritDomain, Work.ParamRays.mem_critDomain, green_eq, greenParam_eq]

theorem isOpen_CritDomain (c : ℂ) : IsOpen (Work.Bottcher.CritDomain c) :=
  isOpen_lt continuous_const
    (Work.Escape.continuous_green (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl)

theorem isPreconnected_CritDomain (c : ℂ) : IsPreconnected (Work.Bottcher.CritDomain c) := by
  rw [critDomain_eq]
  exact Work.ParamRays.isPreconnected_critDomain c

theorem nonempty_CritDomain (c : ℂ) : (Work.Bottcher.CritDomain c).Nonempty := by
  obtain ⟨z, _, hz⟩ := Work.ParamRays.exists_mem_critDomain_gt_norm c 0
  exact ⟨z, by rw [critDomain_eq]; exact hz⟩

/-- The critical domain meets the exterior of every ball around the origin. -/
theorem exists_mem_CritDomain_gt_norm (c : ℂ) (R : ℝ) :
    ∃ z : ℂ, R < ‖z‖ ∧ z ∈ Work.Bottcher.CritDomain c := by
  obtain ⟨z, hR, hz⟩ := Work.ParamRays.exists_mem_critDomain_gt_norm c R
  exact ⟨z, hR, by rw [critDomain_eq]; exact hz⟩

/-- The critical point `0` is not in the critical domain (it is the boundary value of `G_c`). -/
theorem zero_notMem_CritDomain (c : ℂ) : (0 : ℂ) ∉ Work.Bottcher.CritDomain c := by
  rw [Work.Bottcher.mem_CritDomain, Work.Bottcher.greenParam_def]
  exact lt_irrefl _

/-- The critical domain is `T_c`-invariant. -/
theorem Tantibar_mem_CritDomain {c z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) :
    Tantibar c z ∈ Work.Bottcher.CritDomain c := by
  rw [critDomain_eq] at hz ⊢
  exact Work.ParamRays.Tantibar_mem_critDomain hz

/-- The critical domain is invariant along the `T_c`-orbit. -/
theorem orbit_mem_CritDomain {c z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) (n : ℕ) :
    (Tantibar c)^[n] z ∈ Work.Bottcher.CritDomain c := by
  induction n with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact Tantibar_mem_CritDomain ih

theorem green_pMap_four (c z : ℂ) :
    Work.Bottcher.green c (Work.Bottcher.pMap c z) = 4 * Work.Bottcher.green c z := by
  have h : Work.Bottcher.pMap c z = Tantibar c (Tantibar c z) := by
    rw [Work.Bottcher.pMap_eq_iterate_two,
      show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp only [Function.iterate_one]
  rw [h, Work.Bottcher.Green.green_comm, Work.Bottcher.Green.green_comm]
  ring

/-- The critical domain is invariant under the second iterate `p_c`. -/
theorem pMap_mem_CritDomain {c z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) :
    Work.Bottcher.pMap c z ∈ Work.Bottcher.CritDomain c := by
  rw [Work.Bottcher.pMap_eq_iterate_two]
  exact orbit_mem_CritDomain hz 2

theorem pMap_iterate_mem_CritDomain {c z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) (k : ℕ) :
    (Work.Bottcher.pMap c)^[k] z ∈ Work.Bottcher.CritDomain c := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact pMap_mem_CritDomain ih

/-- The normalised factor `p_c z / z^4` does not vanish on the critical domain. -/
theorem normFactor_ne_zero_of_mem_CritDomain {c z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) :
    Work.Bottcher.normFactor c z ≠ 0 := by
  rw [Work.Bottcher.normFactor, div_ne_zero_iff]
  have hz0 : z ≠ 0 := fun h => zero_notMem_CritDomain c (h ▸ hz)
  refine ⟨?_, pow_ne_zero 4 hz0⟩
  intro hp
  have h := green_pMap_four c z
  rw [hp, ← Work.Bottcher.greenParam_def] at h
  have hz' := Work.Bottcher.mem_CritDomain.mp hz
  have h0 : 0 ≤ Work.Bottcher.greenParam c := by
    simpa [Work.Bottcher.greenParam_def] using Work.Bottcher.Green.green_nonneg c 0
  nlinarith

/-- `normFactor c` is differentiable on the critical domain. -/
theorem differentiableOn_normFactor_CritDomain (c : ℂ) :
    DifferentiableOn ℂ (Work.Bottcher.normFactor c) (Work.Bottcher.CritDomain c) := by
  intro z hz
  exact ((Work.Bottcher.Core.hasDerivAt_normFactor c z
    (fun h => zero_notMem_CritDomain c (h ▸ hz))).differentiableAt).differentiableWithinAt

/-- `normFactor c` is analytic on the critical domain. -/
theorem analyticOnNhd_normFactor_CritDomain (c : ℂ) :
    AnalyticOnNhd ℂ (Work.Bottcher.normFactor c) (Work.Bottcher.CritDomain c) :=
  (differentiableOn_normFactor_CritDomain c).analyticOnNhd (isOpen_CritDomain c)

/-! ## A radius above which the critical domain contains everything -/

/-- A radius large enough that the exterior of the ball of radius `critFarRadius c` lies in
`CritDomain c` and in the region where the product formula is the Böttcher coordinate. -/
noncomputable def critFarRadius (c : ℂ) : ℝ :=
  max (Work.Bottcher.escapeRadius c) (2 * Real.exp (Work.Bottcher.greenParam c + Real.log 2))

theorem escapeRadius_le_critFarRadius (c : ℂ) :
    Work.Bottcher.escapeRadius c ≤ critFarRadius c := le_max_left _ _

theorem critFarRadius_pos (c : ℂ) : 0 < critFarRadius c :=
  (Work.Bottcher.Core.escapeRadius_pos c).trans_le (escapeRadius_le_critFarRadius c)

/-- Above `critFarRadius c` the Green function exceeds the critical potential:
`{critFarRadius c < ‖z‖} ⊆ CritDomain c`. -/
theorem critFar_subset_CritDomain (c : ℂ) :
    {z : ℂ | critFarRadius c < ‖z‖} ⊆ Work.Bottcher.CritDomain c := by
  intro z hz
  rw [Work.Bottcher.mem_CritDomain]
  have hR : Work.Bottcher.escapeRadius c < ‖z‖ :=
    lt_of_le_of_lt (escapeRadius_le_critFarRadius c) hz
  have hmax : max 2 ‖c‖ < ‖z‖ := by
    have h1 : (2 : ℝ) ≤ Work.Bottcher.escapeRadius c := by
      rw [Work.Bottcher.escapeRadius]; nlinarith [norm_nonneg c]
    have h2 : ‖c‖ ≤ Work.Bottcher.escapeRadius c := by
      rw [Work.Bottcher.escapeRadius]; nlinarith [norm_nonneg c]
    have h3 : max 2 ‖c‖ ≤ Work.Bottcher.escapeRadius c := max_le_iff.mpr ⟨h1, h2⟩
    linarith
  have hexp : Real.exp (Work.Bottcher.greenParam c + Real.log 2) < ‖z‖ / 2 := by
    have h2 : 2 * Real.exp (Work.Bottcher.greenParam c + Real.log 2) < ‖z‖ :=
      lt_of_le_of_lt (le_max_right _ _) hz
    linarith
  have hzpos : 0 < ‖z‖ := (Work.Bottcher.Core.escapeRadius_pos c).trans hR
  have hlog : Real.log (‖z‖ / 2) ≤ Work.Bottcher.green c z :=
    Work.Escape.log_half_le_green (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl hmax
  have hlt : Work.Bottcher.greenParam c + Real.log 2 < Real.log (‖z‖ / 2) := by
    rw [← Real.log_exp (Work.Bottcher.greenParam c + Real.log 2),
      Real.log_lt_log_iff (Real.exp_pos _) (by linarith)]
    exact hexp
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

end Work.Bottcher.CritBasic
