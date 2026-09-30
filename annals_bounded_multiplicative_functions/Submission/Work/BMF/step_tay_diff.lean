import Mathlib
import Submission.Work.BMF.adi_descent
import Submission.Work.BMF.abs_tay_sub_log_le
import Submission.Work.BMF.step_geom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

theorem step_tay_diff (p : ADIPar) (hp : ADIHyp p) (j : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (p.x / (p.a : ℝ)) ((p.x + p.L) / (p.a : ℝ))) :
    |(Tay j p.x).eval ((p.a : ℝ) * t) - (Tay j p.x).eval ((p.b : ℝ) * t) -
        Real.log ((p.a : ℝ) / (p.b : ℝ))|
      ≤ 2 * (p.L / p.x) ^ (j + 1) + 2 * (3 * p.C₀ ^ 2 * p.L / p.x) ^ (j + 1) := by
  obtain ⟨hLhalf, hChalf, hbdd⟩ := step_geom p hp
  obtain ⟨hatb, hbtb⟩ := hbdd t ht
  rcases hp with ⟨hC0, _hdeg, hL2, _hN100, _hQm, hxpos, _hNL, _hxNL, hb1, hba, _ha, _hNa⟩
  have hapos : (0:ℝ) < p.a := by
    have : 0 < p.a := lt_of_lt_of_le (by norm_num) hba
    exact_mod_cast this
  have hbpos : (0:ℝ) < p.b := by exact_mod_cast (show 0 < p.b by omega)
  have htlo : p.x / (p.a:ℝ) ≤ t := ht.1
  have htpos : 0 < t := by
    have h : 0 < p.x / (p.a:ℝ) := div_pos hxpos hapos
    linarith
  have hatpos : 0 < (p.a:ℝ) * t := mul_pos hapos htpos
  have hbtpos : 0 < (p.b:ℝ) * t := mul_pos hbpos htpos
  have hlogterm : Real.log (((p.a:ℝ)*t)/p.x) - Real.log (((p.b:ℝ)*t)/p.x)
      = Real.log ((p.a:ℝ)/(p.b:ℝ)) := by
    rw [Real.log_div (ne_of_gt hatpos) (ne_of_gt hxpos),
      Real.log_div (ne_of_gt hbtpos) (ne_of_gt hxpos)]
    rw [Real.log_mul (ne_of_gt hapos) (ne_of_gt htpos),
      Real.log_mul (ne_of_gt hbpos) (ne_of_gt htpos)]
    rw [Real.log_div (ne_of_gt hapos) (ne_of_gt hbpos)]
    ring
  have hkey : (Tay j p.x).eval ((p.a:ℝ)*t) - (Tay j p.x).eval ((p.b:ℝ)*t)
      - Real.log ((p.a:ℝ)/(p.b:ℝ))
      = ((Tay j p.x).eval ((p.a:ℝ)*t) - Real.log (((p.a:ℝ)*t)/p.x))
        - ((Tay j p.x).eval ((p.b:ℝ)*t) - Real.log (((p.b:ℝ)*t)/p.x)) := by
    rw [← hlogterm]; ring
  have hu1 : |(p.a:ℝ)*t - p.x| ≤ p.x/2 := le_trans hatb hLhalf
  have hu2 : |(p.b:ℝ)*t - p.x| ≤ p.x/2 := le_trans hbtb hChalf
  have hA := abs_tay_sub_log_le (j := j) (x := p.x) hxpos hu1
  have hB := abs_tay_sub_log_le (j := j) (x := p.x) hxpos hu2
  have hAt : |(Tay j p.x).eval ((p.a:ℝ)*t) - Real.log (((p.a:ℝ)*t)/p.x)|
      ≤ 2 * (p.L/p.x)^(j+1) := by
    refine le_trans hA ?_
    have hle : |(p.a:ℝ)*t - p.x|/p.x ≤ p.L/p.x :=
      div_le_div_of_nonneg_right hatb (le_of_lt hxpos)
    have hnn : 0 ≤ |(p.a:ℝ)*t - p.x|/p.x := div_nonneg (abs_nonneg _) (le_of_lt hxpos)
    have hp' := pow_le_pow_left₀ hnn hle (j+1)
    exact mul_le_mul_of_nonneg_left hp' (by norm_num)
  have hBt : |(Tay j p.x).eval ((p.b:ℝ)*t) - Real.log (((p.b:ℝ)*t)/p.x)|
      ≤ 2 * (3 * p.C₀^2 * p.L/p.x)^(j+1) := by
    refine le_trans hB ?_
    have hle : |(p.b:ℝ)*t - p.x|/p.x ≤ (3 * p.C₀^2 * p.L)/p.x :=
      div_le_div_of_nonneg_right hbtb (le_of_lt hxpos)
    have hnn : 0 ≤ |(p.b:ℝ)*t - p.x|/p.x := div_nonneg (abs_nonneg _) (le_of_lt hxpos)
    have hp' := pow_le_pow_left₀ hnn hle (j+1)
    exact mul_le_mul_of_nonneg_left hp' (by norm_num)
  rw [hkey]
  calc |((Tay j p.x).eval ((p.a:ℝ)*t) - Real.log (((p.a:ℝ)*t)/p.x))
        - ((Tay j p.x).eval ((p.b:ℝ)*t) - Real.log (((p.b:ℝ)*t)/p.x))|
      ≤ |(Tay j p.x).eval ((p.a:ℝ)*t) - Real.log (((p.a:ℝ)*t)/p.x)|
        + |(Tay j p.x).eval ((p.b:ℝ)*t) - Real.log (((p.b:ℝ)*t)/p.x)| := abs_sub _ _
    _ ≤ 2*(p.L/p.x)^(j+1) + 2*(3*p.C₀^2*p.L/p.x)^(j+1) := add_le_add hAt hBt

end Work.BMF
