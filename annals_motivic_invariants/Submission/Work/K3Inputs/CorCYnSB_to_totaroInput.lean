import Mathlib
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.Totaro

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **Totaro's `cor-CYnSB` yields the input the K3 chapter consumes.**

`Work.K3Inputs.CorCYnSB 𝕜` is the paper's Corollary (tex 3103–3115): non-isomorphic `K`-trivial
varieties of Picard number one over a field are not stably birational (in either the
same-`W` form of the paper or the `W = 𝔸ⁿ` form with two exponents).  `Work.K3.TotaroInput 𝕜` is
exactly the `𝔸ⁿ` clause with the two exponents allowed to differ, so this is a repackaging of the
second field. -/
theorem CorCYnSB_to_totaroInput (𝕜 : Type) [Field 𝕜] (h : Work.K3Inputs.CorCYnSB 𝕜) :
    Work.K3.TotaroInput 𝕜 := by
  refine ⟨fun X Y _ _ hX hY hpX hpY hne hsb => ?_⟩
  obtain ⟨n, m, vX, vY, hb⟩ := hsb
  exact h.not_birational_affine X Y hX hY hpX hpY hne n m vX vY hb

end Work.K3Inputs
