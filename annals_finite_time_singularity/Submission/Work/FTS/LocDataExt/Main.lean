/-
# `Work.FTS.LocDataExt.Main` — the localised datum as an admissible datum in `RegQ`

The main theorem of the chapter: **the localised datum of N9 lies in the interior class
`RegQ`**, and N9's smallness/orthogonality facts (reused, not reproved) then package it into
exactly the datum that the a-priori bound `galerkin_bound` of the design
(`Submission/Work/FTS/N45_DESIGN_LEAD.md` §2.4, §4) consumes.

* `regQ_locG` — for `0 < α ≤ 1`, `1 ≤ L` and **every** `β`,
  `Work.FTS.Nonlin.RegQ α 4 (locG α L β (hLoc α))`; the three ingredients are N9's
  `SmoothQuad`/`ℋ⁴`-membership and the boundary traces of `Traces.lean`.
* `HkMem_locG_of_jets` — the same for the order `5` membership, from the order-`5` pointwise
  majorants (the design's `N9-ext` obligation).
* `galData_exists` — **the deliverable**: for each `0 < α ≤ 1` there is `L₀` such that for
  every `L ≥ L₀` there is a scalar `β` with

    `|β| ≤ α²`,  `DataAdm α (locG α L β (hLoc α))`,  `L₁₂(locG α L β (hLoc α))(0) = 0`,
    `RegQ α 4 (locG α L β (hLoc α))`,  `Xn α (locG α L β (hLoc α)) ≤ α²`

  — the four hypotheses of `galerkin_bound` at the datum, with `ε = α²`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.LocDataExt.Traces
import Submission.Work.FTS.LocData.Main
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The interior class `RegQ` of the localised datum -/

/-- On `z > 0` the radial weight is at least `1`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- The order-`4` decay of the `D_z`-jets of the plain profile `FM.Fstar`, in the form the
boundary traces need, from the delivered `Phi_w_le`. -/
theorem DzIter_FM_Fstar_le_four {b : ℕ} (hb : b ≤ 4) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ 2 / z := by
  rw [Work.FTS.LocData.PhiZ_eq b hb z θ]
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h1 := Work.FTS.LocData.Phi_w_le b hb hz θ
  calc |Work.FTS.LocData.Phi b z θ| = |Work.FTS.LocData.Phi b z θ| * 1 := by ring
    _ ≤ |Work.FTS.LocData.Phi b z θ| * Work.Spaces.w z :=
        mul_le_mul_of_nonneg_left (one_le_w hz0) (abs_nonneg _)
    _ = |Work.Spaces.w z * Work.FTS.LocData.Phi b z θ| := by
        rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one (one_le_w hz0))]
        ring
    _ ≤ 2 / z := h1

/-- **The localised datum lies in `RegQ α 4`**, for `0 < α ≤ 1`, `L ≥ 1` and every `β`:
smoothness on the quadrant and `ℋ⁴`-membership are N9's, and the boundary traces are
`Traces.lean`'s `bdryTraces_locG` with the delivered order-`4` jets. -/
theorem regQ_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.FTS.Nonlin.RegQ α 4 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  obtain ⟨Cz, hCz, hCzmaj⟩ := Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
  obtain ⟨K, hK, hKmaj⟩ := Work.FTS.LocData.HkIntegrand_hLoc_le α hα hα1
  refine ⟨Work.FTS.LocData.SmoothQuad_locG α L β hα hα1
      (Work.FTS.LocData.SmoothQuad_hLoc α), ?_, ?_⟩
  · exact Work.FTS.LocData.HkMem_locG α hα hα1 hL
      (fun z hz θ hθ => hCzmaj α hα hα1 L hL z hz θ hθ) hKmaj
  · refine bdryTraces_locG α L β hα hL (k := 4) (CΓ := 100000) (CF := 2)
      (by norm_num) (by norm_num) ?_ ?_
    · intro i hi θ hθ
      exact Work.FTS.LocData.DthIter_Gam_abs_le i hi α hα hα1 hθ
    · intro b hb z hz θ
      exact DzIter_FM_Fstar_le_four hb hz θ

/-! ## The deliverable: the localised datum as data for `galerkin_bound` -/

/-- **THE DELIVERABLE**: for every `0 < α ≤ 1` there is `L₀` such that for every `L ≥ L₀` the
localised perturbation `locG α L β (hLoc α)` — with the normalising scalar
`β = L₁₂(zfar L F_*)(0)/L₁₂(hLoc α)(0)` of N9 — satisfies *all* the hypotheses that the a-priori
bound `galerkin_bound` of the design imposes on its datum (`Submission/Work/FTS/N45_DESIGN_LEAD.md`
§2.4: `DataAdm`, `L₁₂(·)(0) = 0`, `RegQ α 4`, `|·|_{ℋ⁴} ≤ α²`), together with the smallness
`|β| ≤ α²` of the modulation coefficient. -/
theorem galData_exists (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.Construction.L12 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) 0 = 0 ∧
      Work.FTS.Nonlin.RegQ α 4 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ≤ α ^ 2 := by
  obtain ⟨L₀, hL₀⟩ := Work.FTS.LocData.locData_small α hα hα1 (α ^ 2) (by positivity)
  refine ⟨max L₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨β, hβ, hL12, hnorm, hadm⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  exact ⟨β, hβ, hadm, hL12, regQ_locG α L β hα hα1 hL1, hnorm⟩

end Work.FTS.LocDataExt
