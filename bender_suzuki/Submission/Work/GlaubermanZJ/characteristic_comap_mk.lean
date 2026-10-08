import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

-- The preimage of a characteristic subgroup under the quotient map `X → X ⧸ M` is
-- characteristic in `X`, for characteristic `M` (used to lift `Z(J(S)) char G/O_{p'}(G)`
-- back to `G`, where `M = O_{p'}(G)` is characteristic).
theorem characteristic_comap_mk {X : Type*} [Group X] (M : Subgroup X) [M.Normal]
    (hM : M.Characteristic) {K : Subgroup (X ⧸ M)} (hK : K.Characteristic) :
    (K.comap (QuotientGroup.mk' M)).Characteristic := by
  exact Subgroup.Characteristic.comap_quotient_mk (hH := hM) hK

end Work.GlaubermanZJ
