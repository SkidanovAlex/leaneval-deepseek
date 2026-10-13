import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Instantiate
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

theorem Comm2_levels (α : ℝ) (hα : 0 < α)
    {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    Work.FTS.CoercivityFix.Assembly.Comm2 α 2
        (Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α)
      ∧ Work.FTS.CoercivityFix.Assembly.Comm2 α 3
        (Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α)
      ∧ Work.FTS.CoercivityFix.Assembly.Comm2 α 4
        (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) := by
  -- The base level `Comm2 α 1 (H1IP α)`, then three applications of the induction step.
  have h1 : Comm2 α 1 (Work.Coercivity.H1IP α) := Comm2_L1 α hα
  have h2 : Comm2 α 2 (IP2 c₁ c₂ α) := Comm2_succ α hα 1 h1
  have h3 : Comm2 α 3 (IP3 c₁ c₂ c₁' c₂' α) := Comm2_succ α hα 2 h2
  have h4 : Comm2 α 4 (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) := Comm2_succ α hα 3 h3
  exact ⟨h2, h3, h4⟩

end Work.FTS.CoercivityFix.Assembly
