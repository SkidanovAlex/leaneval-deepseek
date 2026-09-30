import Mathlib
import Submission.Work.BW.split_E23_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! The `D`-division identity used by `Work.BW.split_E23`:
`pD r d σ / (r^r d^r ∏σ) = log(2rd) · 2^(5r+6) d`. -/

namespace Work.BW

theorem split_E23_Ddiv {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ) (hP : 0 < ∏ j, σ j) :
    pD r d σ / ((r:ℝ)^r * (d:ℝ)^r * ∏ j, σ j)
      = Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ)) := by
  have hrne : (r:ℝ) ≠ 0 := by
    have h : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
    exact ne_of_gt h
  have hdne : (d:ℝ) ≠ 0 := by
    have h : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    exact ne_of_gt h
  have hPne : (∏ j, σ j) ≠ 0 := ne_of_gt hP
  have hDdiv : pD r d σ / (∏ j, σ j)
      = 2*(r:ℝ)^r*(32*(d:ℝ))^(r+1)*Real.log (2*(r:ℝ)*d) := by
    rw [pD]; field_simp
  have hdd : (d:ℝ)^(r+1)/(d:ℝ)^r = (d:ℝ) := by
    rw [div_eq_iff (pow_ne_zero r hdne), pow_succ']
  calc pD r d σ / ((r:ℝ)^r * (d:ℝ)^r * ∏ j, σ j)
      = (pD r d σ / (∏ j, σ j)) / ((r:ℝ)^r * (d:ℝ)^r) := by field_simp
    _ = (2*(r:ℝ)^r*(32*(d:ℝ))^(r+1)*Real.log (2*(r:ℝ)*d)) / ((r:ℝ)^r * (d:ℝ)^r) := by rw [hDdiv]
    _ = 2*(32*(d:ℝ))^(r+1)*Real.log (2*(r:ℝ)*d) / (d:ℝ)^r := by field_simp
    _ = 2*((2:ℝ)^(5*(r+1))*(d:ℝ)^(r+1))*Real.log (2*(r:ℝ)*d) / (d:ℝ)^r := by
        rw [show (32:ℝ) = (2:ℝ)^5 by norm_num, mul_pow, ← pow_mul]
    _ = 2*(2:ℝ)^(5*(r+1))*((d:ℝ)^(r+1)/(d:ℝ)^r)*Real.log (2*(r:ℝ)*d) := by
        field_simp
    _ = 2*(2:ℝ)^(5*(r+1))*(d:ℝ)*Real.log (2*(r:ℝ)*d) := by rw [hdd]
    _ = (2:ℝ)^(5*r+6)*(d:ℝ)*Real.log (2*(r:ℝ)*d) := by
        rw [← pow_succ', show 5*(r+1)+1 = 5*r+6 by ring]
    _ = Real.log (2*(r:ℝ)*d) * ((2:ℝ)^(5*r+6)*(d:ℝ)) := by ring

end Work.BW
