import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

lemma zpow_emod_eq {M : Type*} [Group M] (x : M) (hx : x ^ 3 = 1) (z : ℤ) :
    x ^ z = x ^ (z % 3) := by
  exact zpow_eq_zpow_emod z (by simpa using hx)

end Work.ThmF.ChV3.Prove
