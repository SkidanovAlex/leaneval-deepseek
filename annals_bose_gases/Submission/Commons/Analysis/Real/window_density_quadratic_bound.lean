import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Real

theorem window_density_quadratic_bound {μ δ d x : ℝ} (hμ : 0 ≤ μ) (hδ : 0 ≤ δ)
    (hd : 0 < d) (hx : 0 ≤ x) (hwin : |x / d - μ| ≤ μ * δ) :
    x ^ 2 / d + μ ^ 2 * d ≤ ((1 + δ) ^ 2 + 1) * (μ ^ 2 * d) := by
  have hxd_sub : x / d - μ ≤ μ * δ := (abs_le.mp hwin).2
  have hxd : x / d ≤ μ * (1 + δ) := by linarith
  have hxle : x ≤ (μ * (1 + δ)) * d := (div_le_iff₀ hd).mp hxd
  have hsq : x ^ 2 ≤ ((μ * (1 + δ)) * d) ^ 2 := pow_le_pow_left₀ hx hxle 2
  have hsq' : x ^ 2 ≤ μ ^ 2 * d ^ 2 * (1 + δ) ^ 2 := by
    calc
      x ^ 2 ≤ ((μ * (1 + δ)) * d) ^ 2 := hsq
      _ = μ ^ 2 * d ^ 2 * (1 + δ) ^ 2 := by ring
  have hsum : x ^ 2 + μ ^ 2 * d ^ 2 ≤ μ ^ 2 * d ^ 2 * (1 + δ) ^ 2 + μ ^ 2 * d ^ 2 := by
    nlinarith [hsq']
  have hfin : x ^ 2 + μ ^ 2 * d ^ 2 ≤ ((1 + δ) ^ 2 + 1) * (μ ^ 2 * d ^ 2) := by
    calc
      x ^ 2 + μ ^ 2 * d ^ 2 ≤ μ ^ 2 * d ^ 2 * (1 + δ) ^ 2 + μ ^ 2 * d ^ 2 := hsum
      _ = ((1 + δ) ^ 2 + 1) * (μ ^ 2 * d ^ 2) := by ring
  have hdne : d ≠ 0 := ne_of_gt hd
  have hmul : (x ^ 2 / d + μ ^ 2 * d) * d ≤ (((1 + δ) ^ 2 + 1) * (μ ^ 2 * d)) * d := by
    calc
      (x ^ 2 / d + μ ^ 2 * d) * d = x ^ 2 + μ ^ 2 * d ^ 2 := by
        field_simp [hdne]
      _ ≤ ((1 + δ) ^ 2 + 1) * (μ ^ 2 * d ^ 2) := hfin
      _ = (((1 + δ) ^ 2 + 1) * (μ ^ 2 * d)) * d := by ring
  exact le_of_mul_le_mul_right hmul hd

end Commons.Analysis.Real