import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Scalar bookkeeping behind the far-field Taylor bound: the four terms on the left are
each exactly of the form `(coefficient) * r ^ (1 + c)`, so the inequality is an equality
(with `hc`, `hc1` used only to guarantee that the divisions are by nonzero reals, as in the
paper's setting). -/
theorem taylor_bound_arith {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (r : ℝ) (hr : 0 < r) :
    (2 * r) ^ c * (12 * Real.pi * r) + 4 * Real.pi * (2 * r) ^ (c + 1) / (c + 1)
        + 4 * r * (4 * Real.pi * (2 * r) ^ c / c)
        + 1024 * r ^ (2:ℕ) * (4 * Real.pi * (2 * r) ^ (c - 1) / (1 - c))
      ≤ (12 * Real.pi * 2 ^ c + 4 * Real.pi * 2 ^ (c + 1) / (c + 1)
          + 16 * Real.pi * 2 ^ c / c + 4096 * Real.pi * 2 ^ (c - 1) / (1 - c))
        * r ^ (1 + c) := by
  have h2nn : (0:ℝ) ≤ 2 := by norm_num
  have hrnn : (0:ℝ) ≤ r := le_of_lt hr
  -- Term 1: `(2r)^c * (12πr) = 12π·2^c·r^{1+c}`.
  have h1 : (2 * r) ^ c * (12 * Real.pi * r) = 12 * Real.pi * 2 ^ c * r ^ (1 + c) := by
    rw [Real.mul_rpow h2nn hrnn]
    rw [show (1:ℝ) + c = c + 1 by ring, Real.rpow_add_one hr.ne' c]
    ring
  -- Term 2: `4π(2r)^{c+1}/(c+1) = (4π·2^{c+1}/(c+1))·r^{1+c}`.
  have h2 : 4 * Real.pi * (2 * r) ^ (c + 1) / (c + 1)
      = 4 * Real.pi * 2 ^ (c + 1) / (c + 1) * r ^ (1 + c) := by
    rw [show (1:ℝ) + c = c + 1 by ring]
    rw [Real.mul_rpow h2nn hrnn]
    ring
  -- Term 3: `4r·(4π(2r)^c/c) = (16π·2^c/c)·r^{1+c}`.
  have h3 : 4 * r * (4 * Real.pi * (2 * r) ^ c / c)
      = 16 * Real.pi * 2 ^ c / c * r ^ (1 + c) := by
    rw [show (1:ℝ) + c = c + 1 by ring, Real.rpow_add_one hr.ne' c]
    rw [Real.mul_rpow h2nn hrnn]
    ring
  -- Term 4: `1024·r^2·(4π(2r)^{c-1}/(1-c)) = (4096π·2^{c-1}/(1-c))·r^{1+c}`.
  have h4 : 1024 * r ^ (2:ℕ) * (4 * Real.pi * (2 * r) ^ (c - 1) / (1 - c))
      = 4096 * Real.pi * 2 ^ (c - 1) / (1 - c) * r ^ (1 + c) := by
    rw [show (1:ℝ) + c = c + 1 by ring]
    rw [Real.mul_rpow h2nn hrnn]
    have hrpow : r ^ (2:ℕ) * r ^ (c - 1) = r ^ (c + 1) := by
      rw [show r ^ (2:ℕ) = r ^ (2:ℝ) from (Real.rpow_natCast r 2).symm]
      rw [← Real.rpow_add hr 2 (c - 1)]
      congr 1
      ring
    calc 1024 * r ^ (2:ℕ) * (4 * Real.pi * (2 ^ (c - 1) * r ^ (c - 1)) / (1 - c))
        = 1024 * 4 * Real.pi * 2 ^ (c - 1) * (r ^ (2:ℕ) * r ^ (c - 1)) / (1 - c) := by ring
      _ = 1024 * 4 * Real.pi * 2 ^ (c - 1) * r ^ (c + 1) / (1 - c) := by rw [hrpow]
      _ = 4096 * Real.pi * 2 ^ (c - 1) / (1 - c) * r ^ (c + 1) := by ring
  rw [h1, h2, h3, h4]
  exact le_of_eq (by ring)

end Work.CoreResiduals.BiotSavart
