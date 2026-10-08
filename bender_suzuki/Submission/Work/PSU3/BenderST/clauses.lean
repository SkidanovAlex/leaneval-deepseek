import Mathlib
import Submission.Work.PSU3.BenderST.Defs
import Submission.Work.PSU3.BenderST.psl2_standard_clause
import Submission.Work.PSU3.BenderST.sz_standard_clause
import Submission.Work.PSU3.BenderST.psu3_standard_clause
import Submission.Work.Models.ModelData.pSL2ModelData
import Submission.Work.Models.ModelData.szModelData
import Submission.Work.Models.ModelData.psu3ModelData_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BenderST.clauses` — `StdClause` for the three models

The three delegated model computations (`psl2_standard_clause`, `sz_standard_clause`,
`psu3_standard_clause`) are the three clauses of `BenderSTProp` for the *standard* split
rank-one datum of `PSL(2,2ⁿ)`, `Sz(2^(2n+1))` and `PSU(3,2ⁿ)`.  Here they are packaged as
`StdClause P` (`Submission/Work/PSU3/BenderST/Defs.lean`), ready for the transfer
`benderSTProp_of_stdClause`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.BenderST

/-- The standard datum of `PSL(2,2ⁿ)` satisfies the `PSL2` clause. -/
theorem psl2_stdClause (n : ℕ) (hn : 2 ≤ n) :
    StdClause (Submission.PSL2.pSL2BenderPair n hn) := by
  intro s r hs hs2 hr hsr
  exact Or.inl (psl2_standard_clause n hn
    (benderPair_isSplitRankOne _ Submission.PSL2.weylPSL_mul_self) s r hs hs2 hr hsr)

/-- The standard datum of `Sz(2^(2n+1))` satisfies the `Sz` clause. -/
theorem sz_stdClause (n : ℕ) (hn : 1 ≤ n) :
    StdClause (Submission.Sz.szBenderPair n hn) := by
  intro s r hs hs2 hr hsr
  exact Or.inr (Or.inl (sz_standard_clause n hn
    (benderPair_isSplitRankOne _ (Work.Models.ModelData.szWgM_mul_self n)) s r hs hs2 hr hsr))

/-- The standard datum of `PSU(3,2ⁿ)` satisfies the `PSU3` clause. -/
theorem psu3_stdClause (n : ℕ) (hn : 2 ≤ n) :
    StdClause (Submission.PSU3.psu3BenderPair n hn) := by
  intro s r hs hs2 hr hsr
  exact Or.inr (Or.inr (psu3_standard_clause n hn
    (benderPair_isSplitRankOne _ (Work.Models.ModelData.psu3Weyl_mul_self n)) s r hs hs2 hr hsr))

end Work.PSU3.BenderST
