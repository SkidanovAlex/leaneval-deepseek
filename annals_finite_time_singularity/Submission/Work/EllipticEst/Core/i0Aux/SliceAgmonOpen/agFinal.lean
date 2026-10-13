import Mathlib.Algebra.Order.Archimedean.Real.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonOpen

theorem agFinal {A P N J eta : ℝ} (heta : 0 < eta)
    (hc : (1 + eta) * (1 / 200) ≤ 1 - eta) (hA : 0 ≤ A)
    (hL : A + P - 2 * eta * N - 2 * eta * (1 + eta) * J ≤ 0)
    (hJ : (1 + eta) ^ 2 * J ≤ A) :
    (1 / 200) * A + P ≤ 2 * eta * N := by
  -- Key arithmetic content of `hc`:  2η/(1+η) ≤ 199/200.
  have hpos : 0 < 1 + eta := by linarith
  have hc' : 2 * eta / (1 + eta) ≤ 199 / 200 := by
    rw [div_le_iff₀ hpos]
    linarith [hc]
  -- From `hJ`, using `2η(1+η) = (2η/(1+η))·(1+η)²`, we get
  --   2η(1+η)J ≤ (199/200)·A .
  have hkey : 2 * eta * (1 + eta) * J ≤ (199 / 200) * A := by
    have h2 : 2 * eta * (1 + eta) * J
        = (2 * eta / (1 + eta)) * ((1 + eta) ^ 2 * J) := by
      field_simp
    rw [h2]
    calc (2 * eta / (1 + eta)) * ((1 + eta) ^ 2 * J)
        ≤ (2 * eta / (1 + eta)) * A := by
          apply mul_le_mul_of_nonneg_left hJ
          positivity
      _ ≤ (199 / 200) * A := mul_le_mul_of_nonneg_right hc' hA
  -- Add to `hL`:  A + P - 2ηN - 2η(1+η)J ≤ 0  and  2η(1+η)J ≤ 199A/200
  -- give  A/200 + P - 2ηN ≤ 0.
  linarith

end Work.EllipticEst.Core.i0Aux.SliceAgmonOpen
