/-
# `Work.FTS.LocDataExt.Final` — the unconditional admissibility lemmas for the localised datum

The end of the chapter: the order-`4` and order-`5` interior-regularity statements of the
localised datum of N9, now **unconditional** (the two radial jet inputs of `LocG5.lean` are
discharged by `Zfar5.lean` and `FMJet5.lean`), and the packaging of the four hypotheses of the
a-priori bound `galerkin_bound` (design §2.4, §4) — with `RegQ α 4` and, additionally,
`RegQ α 5` (the design's `N9-ext` obligation).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.LocDataExt.Main
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.LocDataExt.Zfar5

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

/-- **The localised datum lies in `RegQ α 5`** — unconditionally, for `0 < α ≤ 1`, `L ≥ 1` and
every `β` (the design's `N9-ext` statement). -/
theorem regQ_locG5_uncond (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.FTS.Nonlin.RegQ α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  obtain ⟨A, hA, hAz⟩ := zfarR_jet_le5_clean
  obtain ⟨CF, hCF, hF⟩ := FM_Fstar_jet_le5
  exact regQ_locG5 α L β hα hα1 hL (le_of_lt hA) (le_of_lt hCF)
    (fun j hj z hz θ => hAz L hL j hj z hz θ) hF

/-- **The localised datum lies in `RegQ α 4`** — through the monotonicity of `RegQ` in the
order, from the order-`5` statement. -/
theorem regQ_locG4_uncond (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.FTS.Nonlin.RegQ α 4 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) :=
  RegQ_mono (by norm_num) (regQ_locG5_uncond α L β hα hα1 hL)

/-- **The order-`5` deliverable, unconditional**: the localised datum satisfies the hypotheses
of `galerkin_bound` with `RegQ α 5` in place of `RegQ α 4`. -/
theorem galData_exists5_uncond (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.Construction.L12 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) 0 = 0 ∧
      Work.FTS.Nonlin.RegQ α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ≤ α ^ 2 := by
  obtain ⟨A, hA, hAz⟩ := zfarR_jet_le5_clean
  obtain ⟨CF, hCF, hF⟩ := FM_Fstar_jet_le5
  exact galData_exists5 α hα hα1 (le_of_lt hA) (le_of_lt hCF) (fun L' hL' => hAz L' hL') hF

/-- **THE ADMISSIBILITY LEMMA** in the strongest available form: for every `0 < α ≤ 1` there is
`L₀ > 0` such that for every `L ≥ L₀` the localised perturbation `locG α L β (hLoc α)` — with
N9's normalising scalar `β` — satisfies `|β| ≤ α²`, `DataAdm α (·)`, `L₁₂(·)(0) = 0`, the
interior classes `RegQ α 4` **and** `RegQ α 5`, and `Xn α (·) ≤ α²`. -/
theorem galData_exists_both (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.Construction.L12 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) 0 = 0 ∧
      Work.FTS.Nonlin.RegQ α 5 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.FTS.Nonlin.RegQ α 4 (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) ≤ α ^ 2 := by
  obtain ⟨L₀, hL₀, h⟩ := galData_exists5_uncond α hα hα1
  refine ⟨L₀, hL₀, fun L hL => ?_⟩
  obtain ⟨β, hβ, hadm, hL12, hreg5, hnorm⟩ := h L hL
  exact ⟨β, hβ, hadm, hL12, hreg5, RegQ_mono (by norm_num) hreg5, hnorm⟩

end Work.FTS.LocDataExt
