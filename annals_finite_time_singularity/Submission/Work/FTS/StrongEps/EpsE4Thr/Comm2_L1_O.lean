import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO
import Submission.Work.FTS.CoercivityFix.Assembly.Instantiate
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dth_Lhat_O
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- **The level-`1` algebraic inputs of the corrected induction, in the open class.**  This is
the open-class (`RegQo`/`SmoothOpen`) twin of `CoercivityFix.Assembly.Comm2_L1`:

* `congr` is `StepAssembly.H1IP_congr_qd`, which is membership-free (derivatives are local and
  the open quadrant is co-null);
* `add` is `Transfer.H1IP_add_weak` with its block hypotheses discharged from `SmoothOpen`
  (this is exactly the `n = 0` clause of `IPGen.Comm2o_zero`, whose hypotheses
  `SmoothOpen` + `HkMem α 1` are immediate from `RegQo α 1`);
* the two commutator identities of `𝓛̂` are `LhatCommOpen`, the open-quadrant form of
  `LhatCalc.Dth_Lhat` / `LhatCalc.Dz_Lhat` (no hypothesis on the datum at `z ≤ 0` is used). -/
theorem Comm2_L1_O (α : ℝ) (hα : 0 < α) :
    Work.FTS.StrongEps.EpsE4Thr.Comm2O α 1 (Work.Coercivity.H1IP α) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun _f _f' _g h => Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd α h
  · intro f₁ f₂ g h₁ h₂ h₃
    exact (Work.FTS.IPGen.Comm2o_zero α).add f₁ f₂ g h₁.1 h₂.1 h₃.1 h₁.2.1 h₂.2.1 h₃.2.1
  · intro f hf z θ hzθ
    exact (Work.FTS.StrongPersist.H6Aux.LhatCommOpen hf).1 z θ hzθ
  · intro f hf z θ hzθ
    exact (Work.FTS.StrongPersist.H6Aux.LhatCommOpen hf).2 z θ hzθ

end Work.FTS.StrongEps.EpsE4Thr
