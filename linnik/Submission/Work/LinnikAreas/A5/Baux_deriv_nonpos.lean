import Mathlib
import Submission.Work.LinnikAreas.A5.Baux_lim_ratio
import Submission.Work.LinnikAreas.A5.Baux_exp_ineqs

namespace Work.LinnikAreas.A5

theorem Baux_deriv_nonpos (K t : ℝ) (hK : 0 < K) (ht : 0 < t) :
    deriv (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s) + 2 * (s - 1 + Real.exp (-s)) / s ^ 2) t ≤ 0 := by
  have h1 : 3 * K * t ≠ 0 := by positivity
  have h2 : t ^ 2 ≠ 0 := by positivity
  -- atomic derivative facts
  have hde : deriv (fun s : ℝ => 1 - Real.exp (-s)) t = Real.exp (-t) := by
    rw [show (fun s : ℝ => 1 - Real.exp (-s)) = ((fun s : ℝ => 1) - (fun s : ℝ => Real.exp (-s))) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), deriv_const]
    rw [deriv_exp (f := fun s : ℝ => -s) (by fun_prop), deriv_neg'']
    ring
  have hd3 : deriv (fun s : ℝ => 3 * K * s) t = 3 * K := by
    rw [show (fun s : ℝ => 3 * K * s) = (fun s : ℝ => (3 * K) * s) from rfl]
    rw [deriv_const_mul (3 * K) (by fun_prop), deriv_id'']
    ring
  have hd2 : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
    rw [deriv_pow_field 2]
    norm_num
  have hdnum2 : deriv (fun s : ℝ => 2 * (s - 1 + Real.exp (-s))) t = 2 * (1 - Real.exp (-t)) := by
    rw [deriv_const_mul (2 : ℝ) (by fun_prop)]
    rw [show (fun s : ℝ => s - 1 + Real.exp (-s)) =
          (((fun s : ℝ => s) - (fun s : ℝ => 1)) + (fun s : ℝ => Real.exp (-s))) from rfl]
    rw [deriv_add (by fun_prop) (by fun_prop), deriv_sub (by fun_prop) (by fun_prop),
        deriv_id'', deriv_const]
    rw [deriv_exp (f := fun s : ℝ => -s) (by fun_prop), deriv_neg'']
    ring
  have hdt1 : deriv (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s)) t
      = ((t + 1) * Real.exp (-t) - 1) / (3 * K * t ^ 2) := by
    rw [show (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s)) =
          ((fun s : ℝ => 1 - Real.exp (-s)) / (fun s : ℝ => 3 * K * s)) from rfl]
    rw [deriv_div (c := fun s : ℝ => 1 - Real.exp (-s)) (d := fun s : ℝ => 3 * K * s)
          (x := t) (by fun_prop) (by fun_prop) h1, hde, hd3]
    field_simp
    ring
  have hdt2 : deriv (fun s : ℝ => 2 * (s - 1 + Real.exp (-s)) / s ^ 2) t
      = 2 * (2 - t - (t + 2) * Real.exp (-t)) / t ^ 3 := by
    rw [show (fun s : ℝ => 2 * (s - 1 + Real.exp (-s)) / s ^ 2) =
          ((fun s : ℝ => 2 * (s - 1 + Real.exp (-s))) / (fun s : ℝ => s ^ 2)) from rfl]
    rw [deriv_div (c := fun s : ℝ => 2 * (s - 1 + Real.exp (-s))) (d := fun s : ℝ => s ^ 2)
          (x := t) (by fun_prop) (by fun_prop) h2, hdnum2, hd2]
    field_simp
    ring
  have hderiv : deriv (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s) + 2 * (s - 1 + Real.exp (-s)) / s ^ 2) t
      = ((t + 1) * Real.exp (-t) - 1) / (3 * K * t ^ 2)
        + 2 * (2 - t - (t + 2) * Real.exp (-t)) / t ^ 3 := by
    rw [show (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s) + 2 * (s - 1 + Real.exp (-s)) / s ^ 2)
          = (fun s : ℝ => (1 - Real.exp (-s)) / (3 * K * s))
            + (fun s : ℝ => 2 * (s - 1 + Real.exp (-s)) / s ^ 2) from rfl]
    rw [deriv_add (by fun_prop) (by fun_prop), hdt1, hdt2]
  rw [hderiv]
  obtain ⟨hexp1, hexp2⟩ := Baux_exp_ineqs t ht.le
  have hA : ((t + 1) * Real.exp (-t) - 1) / (3 * K * t ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hB : 2 * (2 - t - (t + 2) * Real.exp (-t)) / t ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

end Work.LinnikAreas.A5
