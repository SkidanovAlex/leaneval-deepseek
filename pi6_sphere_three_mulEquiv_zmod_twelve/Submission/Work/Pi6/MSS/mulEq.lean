import Mathlib
import Submission.Work.Pi6.MSS.pagesData
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem mulEq (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (D : Work.Pi6.MSS.PagesData 𝕜 W)
    (r s n s' n' : ℕ) : D.mul r s n s' n' = Work.Pi6.MSS.pd_mul r s n s' n' := by
  apply LinearMap.ext; intro u
  apply LinearMap.ext; intro v
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) u
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) v
  rw [D.mul_nat r s n s' n' x y, pd_mul_nat r s n s' n' x y]
  congr 1
  exact Subtype.ext (by rw [D.mulZ_val, pd_mulZ_val])

end
end Work.Pi6.MSS
