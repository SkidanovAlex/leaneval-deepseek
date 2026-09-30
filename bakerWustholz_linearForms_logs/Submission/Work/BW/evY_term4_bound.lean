import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem evY_term4_bound {S D u : ℝ} (hS : 608 ≤ S) (hD : 262144 ≤ D) (hu : 1 ≤ u)
    (huD : u ≤ D) :
    2 * Real.log (4 * u * S) + 3 ≤ 0.04 * S * D := by
  have hSpos : (0:ℝ) < S := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  have hupos : (0:ℝ) < u := by linarith
  have h4uSpos : (0:ℝ) < 4 * u * S := by positivity
  have hle : 4 * u * S ≤ 4 * D * S := by nlinarith [hSpos, huD]
  have hlogmono : Real.log (4 * u * S) ≤ Real.log (4 * D * S) :=
    Real.log_le_log h4uSpos hle
  have hsplit : Real.log (4 * D * S) = Real.log (4 * D) + Real.log S := by
    rw [show (4:ℝ) * D * S = (4 * D) * S by ring, Real.log_mul]
    · exact ne_of_gt (by positivity : (0:ℝ) < 4 * D)
    · exact ne_of_gt hSpos
  have hlog4D : Real.log (4 * D) ≤ 4 * D - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogS : Real.log S ≤ S := Real.log_le_self (le_of_lt hSpos)
  have h1 : 2 * Real.log (4 * D) + 3 ≤ 0.02 * S * D := by
    have hS' : (12.16:ℝ) ≤ 0.02 * S := by linarith
    have hDnn : (0:ℝ) ≤ D := le_of_lt hDpos
    have hstep : (12.16:ℝ) * D ≤ 0.02 * S * D := by
      calc (12.16:ℝ) * D ≤ (0.02 * S) * D := mul_le_mul_of_nonneg_right hS' hDnn
        _ = 0.02 * S * D := by ring
    have h8 : 2 * Real.log (4 * D) + 3 ≤ 8 * D + 1 := by linarith
    have h816 : (8:ℝ) * D + 1 ≤ 12.16 * D := by linarith
    linarith
  have h2 : 2 * Real.log S ≤ 0.02 * S * D := by
    have hD2 : (2:ℝ) ≤ 0.02 * D := by linarith
    have hSnn : (0:ℝ) ≤ S := le_of_lt hSpos
    have hstep : 2 * S ≤ 0.02 * S * D := by
      calc 2 * S ≤ (0.02 * D) * S := mul_le_mul_of_nonneg_right hD2 hSnn
        _ = 0.02 * S * D := by ring
    linarith
  calc 2 * Real.log (4 * u * S) + 3
      ≤ 2 * Real.log (4 * D * S) + 3 := by linarith
    _ = 2 * (Real.log (4 * D) + Real.log S) + 3 := by rw [hsplit]
    _ = (2 * Real.log (4 * D) + 3) + 2 * Real.log S := by ring
    _ ≤ 0.02 * S * D + 0.02 * S * D := by linarith
    _ = 0.04 * S * D := by ring

end Work.BW
