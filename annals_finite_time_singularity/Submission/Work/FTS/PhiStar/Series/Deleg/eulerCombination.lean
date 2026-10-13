import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem eulerCombination {α lam K sn sp P Q cz W1 W2 : ℝ}
    (hW1 : W1 = K * (sn * P + sp * Q))
    (hW2 : W2 = K * (sn * (sn - 1) * P + sp * (sp - 1) * Q + (sn - sp) * cz))
    (hind1 : -α ^ 2 * sn * (sn - 1) - α * (5 + α) * sn + lam = 0)
    (hind2 : -α ^ 2 * sp * (sp - 1) - α * (5 + α) * sp + lam = 0)
    (hK : α ^ 2 * K * (sp - sn) = 1) :
    -α ^ 2 * W2 - α * (5 + α) * W1 + lam * (K * (P + Q)) = cz := by
  linear_combination (-α ^ 2) * hW2 + (-(α * (5 + α))) * hW1
    + (K * P) * hind1 + (K * Q) * hind2 + cz * hK

end Work.FTS.PhiStar.Series.Deleg
