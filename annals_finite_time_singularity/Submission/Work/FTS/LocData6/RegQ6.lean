/-
# `Work.FTS.LocData6.RegQ6` — the localised datum lies in `RegQ α 6`, unconditionally

This module instantiates the conditional assembly `LocData6.LocG6Aux.regQ_locG6_of_jets` with
the order-`6` jet lemmas of the chapter:

* `LocData6.zfarR_jet_le6_clean` (the far factor `zfarR L`, uniformly in `L ≥ 1`, `j ≤ 6`);
* `LocData6.FM_Fstar_jet_le6` (the plain profile);
* `LocData6.DthIter_Gam_abs_le6` (the angular factor `Γ`, `i ≤ 6`);
* `LocData6.hLoc_majorant6` (the `ℋ⁶`-majorant of the bump `hLoc α`).

The result is the unconditional interior-regularity statement of the chapter,

  `Work.FTS.Nonlin.RegQ α 6 (locG α L β (hLoc α))`  for every `0 < α ≤ 1`, `L ≥ 1`, `β`,

the order-`6` companion of `Work.FTS.LocDataExt.regQ_locG5_uncond`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData6.LocG6Aux
import Submission.Work.FTS.LocData6.ZfarJetIci6
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.LocData6.hLoc_majorant6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The squared angular bound `(D_θ^i Γ)² ≤ 10¹⁰·Γ²` on `Iθ` for `i ≤ 6`, obtained by squaring
the order-`6` jet bound `LocData6.DthIter_Gam_abs_le6`. -/
theorem hGam6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : i ≤ 6) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
  have h := DthIter_Gam_abs_le6 i hi α hα hα1 hθ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at h2
  have h10 : ((100000 : ℝ)) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (100000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := h2
    _ = (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by rw [h10]

/-- **The localised datum lies in `RegQ α 6`** — unconditionally, for `0 < α ≤ 1`, `L ≥ 1` and
every `β`.  This is the order-`6` form of the design's `N9-ext` obligation: `SmoothQuad`,
`HkMem α 6` and the vanishing boundary traces `BdryTraces α 6`. -/
theorem regQ_locG6_uncond (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) := by
  obtain ⟨A, hA, hAz⟩ := zfarR_jet_le6_clean
  obtain ⟨CF, hCF, hF⟩ := FM_Fstar_jet_le6
  obtain ⟨Kb, hKb0, hKb⟩ := hLoc_majorant6 α hα hα1
    (fun i hi θ hθ => hGam6 α hα hα1 hi hθ)
  refine regQ_locG6_of_jets α L β hα hα1 hL (le_of_lt hA) (by norm_num)
    (fun j hj z hz θ => hAz L hL j hj z hz θ)
    (fun i hi θ hθ => hGam6 α hα hα1 hi hθ)
    (fun i hi θ hθ => DthIter_Gam_abs_le6 i hi α hα hα1 hθ)
    hKb0 hKb (le_of_lt hCF) hF

end Work.FTS.LocData6
