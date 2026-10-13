/-
# `Transfer/CommSm_L1.lean` — the level-1 algebraic package of the transfer, in `Q0Sm` form

`Transfer/CoreDefs.lean` fixes the objects of the corrected transfer induction: the pairing
package `CommSm α n IP` whose `add` field takes the finite-order class `Q0Sm` (smoothness on
the open quadrant) plus `HkMem`, instead of the analytic `RegQ` of `Assembly.Comm2`.  This
file discharges the base case `CommSm α 1 (H1IP α)`.

The four clauses:

* `congr` — membership-free congruence of `H1IP` in its first argument on `Qd`
  (`StepAssembly.H1IP_congr_qd`, re-exported through `Assembly.Comm2_L1`);
* `add` — additivity of `H1IP` from `Q0Sm 1` of the three arguments and their `HkMem`.
  `Q0Sm 1` gives continuity of the three blocks `X`, `D_z X`, `D_θ X` on `Qd`
  (`Q0Sm.mixed_continuousOn`, e.g. `mixed 1 0 X = D_z X`), which is exactly the
  block-continuity input of `Transfer.H1IP_add_weak`; the two derivative identities
  `D_z (f₁+f₂) = D_z f₁ + D_z f₂`, `D_θ (f₁+f₂) = …` are `Q0Sm.dz_add` / `Q0Sm.dth_add`;
* `dthC`, `dzC` — the two exact commutator identities of `Lhat`, which are
  `SmoothQuad`-statements and hence transported verbatim from `Assembly.Comm2_L1`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_add_weak
import Submission.Work.FTS.CoercivityFix.Assembly.Instantiate
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

noncomputable section

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-1 algebraic inputs of the transfer, in `Q0Sm` form.** -/
theorem CommSm_L1 (α : ℝ) (hα : 0 < α) :
    Work.FTS.CoercivityFix.Transfer.CommSm α 1 (Work.Coercivity.H1IP α) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Work.FTS.CoercivityFix.Assembly.Comm2_L1 α hα).congr
  · intro f₁ f₂ g h
    obtain ⟨h1, h2, hg, hm1, hm2, hmg⟩ := h
    exact H1IP_add_weak α hm1 hm2 hmg
      (h1.mixed_continuousOn (a := 0) (b := 0) (by norm_num))
      (h2.mixed_continuousOn (a := 0) (b := 0) (by norm_num))
      (hg.mixed_continuousOn (a := 0) (b := 0) (by norm_num))
      (h1.mixed_continuousOn (a := 0) (b := 1) (by norm_num))
      (h2.mixed_continuousOn (a := 0) (b := 1) (by norm_num))
      (hg.mixed_continuousOn (a := 0) (b := 1) (by norm_num))
      (h1.mixed_continuousOn (a := 1) (b := 0) (by norm_num))
      (h2.mixed_continuousOn (a := 1) (b := 0) (by norm_num))
      (hg.mixed_continuousOn (a := 1) (b := 0) (by norm_num))
      (Q0Sm.dz_add h1 h2) (Q0Sm.dth_add h1 h2)
  · exact (Work.FTS.CoercivityFix.Assembly.Comm2_L1 α hα).dthC
  · exact (Work.FTS.CoercivityFix.Assembly.Comm2_L1 α hα).dzC

end

end Work.FTS.CoercivityFix.Transfer
