import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.phiC_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- The argument `W(u,v) = u² + 2uv` is monotone in both variables on the honest range:
if `u ≥ u_lo > 0`, `v ≥ v_lo` and `u_lo + 2v_lo > 0`, then `W(u,v) ≥ W(u_lo,v_lo)`.

Indeed `u² + 2uv − (u_lo² + 2u_lo v_lo) = (u−u_lo)(u+u_lo+2v) + 2u_lo(v−v_lo)`, and
`u + u_lo + 2v ≥ 2(u_lo + v_lo) > 0`. -/
private lemma sq_add_two_mul_le_sq_add_two_mul {u_lo v_lo u v : ℝ}
    (hul : 0 < u_lo) (h2v : 0 < u_lo + 2 * v_lo)
    (hu : u_lo ≤ u) (hv : v_lo ≤ v) :
    u_lo ^ 2 + 2 * u_lo * v_lo ≤ u ^ 2 + 2 * u * v := by
  have h1 : 0 ≤ u - u_lo := by linarith
  have h2 : 0 ≤ v - v_lo := by linarith
  have h3 : 0 ≤ u + u_lo + 2 * v := by linarith
  nlinarith [mul_nonneg h1 h3, mul_nonneg h2 hul.le]

/-- **Pointwise box bound for the `u`-derivative of `phiC`.**  For `u ≥ u_lo > 0`, `v_lo ≤ v ≤ v_hi`
and `u_lo² + 2u_lo v_lo > 0` (so every square root below is taken at a positive argument),

  `|v²/(S·D)| ≤ M²/(S_lo · D_lo)`,  `S = u+v+√(u²+2uv)`, `D = √(u²+2uv)`, `M = max |v_lo| |v_hi|`,
  `D_lo = √(u_lo²+2u_lo v_lo)`, `S_lo = u_lo + v_lo + D_lo`.

This is the bound on `|∂_u phiC| = v²/(S·D)`.  Route: `|v| ≤ M`, `S ≥ S_lo`, `D ≥ D_lo`, where
`D` and `S` are increasing in both arguments on the honest range (`u²+2uv` is increasing in `u`
and `v` for `u > 0`, `u + 2v > 0`). -/
theorem phiC_du_bound {u_lo u_hi v_lo v_hi u v : ℝ}
    (hul : 0 < u_lo) (hW : 0 < u_lo ^ 2 + 2 * u_lo * v_lo)
    (hu : u_lo ≤ u) (hv : v_lo ≤ v) (hv2 : v ≤ v_hi) :
    |v ^ 2 / ((u + v + Real.sqrt (u ^ 2 + 2 * u * v)) * Real.sqrt (u ^ 2 + 2 * u * v))|
      ≤ (max |v_lo| |v_hi|) ^ 2
          / ((u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
              * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)) := by
  -- `M := max |v_lo| |v_hi|` is a nonnegative upper bound for `|v|`
  have hM0 : 0 ≤ max |v_lo| |v_hi| := le_trans (abs_nonneg v_lo) (le_max_left _ _)
  have hvabs : |v| ≤ max |v_lo| |v_hi| := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le v_lo, le_max_left |v_lo| |v_hi|],
           by linarith [le_abs_self v_hi, le_max_right |v_lo| |v_hi|]⟩
  have hvsq : v ^ 2 ≤ (max |v_lo| |v_hi|) ^ 2 := by
    calc v ^ 2 = |v| ^ 2 := (sq_abs v).symm
      _ = |v| * |v| := by ring
      _ ≤ (max |v_lo| |v_hi|) * (max |v_lo| |v_hi|) :=
          mul_self_le_mul_self (abs_nonneg v) hvabs
      _ = (max |v_lo| |v_hi|) ^ 2 := by ring
  -- the two square-root arguments
  have h2v : 0 < u_lo + 2 * v_lo := by
    have hfac : u_lo ^ 2 + 2 * u_lo * v_lo = u_lo * (u_lo + 2 * v_lo) := by ring
    exact pos_of_mul_pos_right (by rwa [← hfac]) hul.le
  have hWbig : u_lo ^ 2 + 2 * u_lo * v_lo ≤ u ^ 2 + 2 * u * v :=
    sq_add_two_mul_le_sq_add_two_mul hul h2v hu hv
  have hDl : 0 < Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := Real.sqrt_pos.mpr hW
  have hD : Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) ≤ Real.sqrt (u ^ 2 + 2 * u * v) :=
    Real.sqrt_le_sqrt hWbig
  have hD0 : 0 < Real.sqrt (u ^ 2 + 2 * u * v) := lt_of_lt_of_le hDl hD
  -- the two denominators, positive and ordered
  have hub : 0 < u_lo + v_lo := by linarith
  have hS : u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)
      ≤ u + v + Real.sqrt (u ^ 2 + 2 * u * v) := by linarith
  have hS0 : 0 < u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := by linarith
  have hden0 : 0 < (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) * Real.sqrt (u ^ 2 + 2 * u * v) :=
    mul_pos (by linarith) hD0
  have hden0' : 0 < (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
      * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo) := mul_pos hS0 hDl
  have hdenle : (u_lo + v_lo + Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo))
        * Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)
      ≤ (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) * Real.sqrt (u ^ 2 + 2 * u * v) :=
    mul_le_mul hS hD (Real.sqrt_nonneg _)
      (by linarith : (0 : ℝ) ≤ u + v + Real.sqrt (u ^ 2 + 2 * u * v))
  rw [abs_of_nonneg (div_nonneg (sq_nonneg v) hden0.le)]
  exact div_le_div₀ (sq_nonneg _) hvsq hden0' hdenle

end Work.BoseBogFS
