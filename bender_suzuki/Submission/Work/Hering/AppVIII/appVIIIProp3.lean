import Mathlib
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Hering.AppVIII.BAut

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVIII

/-- **App. VIII, Prop. 3**: `Aut(B(n,1,ε))` is solvable for `ε` satisfying the anisotropy
condition of the source. -/
theorem appVIIIProp3 : AppVIIIProp3 := by
  intro n ε hε
  haveI : Fact (Irreducible (Work.Hering.AppVIII.quadPoly (GaloisField 2 n) ε)) :=
    ⟨Work.Hering.AppVIII.quadPoly_irreducible (GaloisField 2 n) hε⟩
  exact isSolvable_mulAut_B hε

end Work.Hering.AppVIII
