import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

/-- `φ(s) = log(2 − 3s)/(1 − s)` is non-increasing on `[0, 1/3]` (its derivative has the sign of `(2−3s)log(2−3s) − 3(1−s) = u log u − (u+1) ≤ 0` for `u = 2−3s ∈ [1,2]`). -/
theorem phi_antitone : AntitoneOn (fun s : ℝ => Real.log (2 - 3 * s) / (1 - s)) (Set.Icc 0 (1/3)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1/3))
  · exact ContinuousOn.div
      (ContinuousOn.log (by fun_prop) (by intro x hx; linarith [hx.2]))
      (by fun_prop)
      (by intro x hx; linarith [hx.2])
  · rw [interior_Icc]
    exact DifferentiableOn.div
      (DifferentiableOn.log (by fun_prop) (by intro x hx; linarith [hx.2]))
      (by fun_prop)
      (by intro x hx; linarith [hx.2])
  · rw [interior_Icc]
    intro x hx
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1/3 := hx.2
    have hpos : 0 < 2 - 3*x := by linarith
    have hne : (1 - x) ≠ 0 := by linarith
    have hnum : HasDerivAt (fun s : ℝ => 2 - 3*s) (-3) x := by
      have h : HasDerivAt (fun s : ℝ => 2 - 3*s) (-(3*1)) x :=
        ((hasDerivAt_id x).const_mul (3:ℝ)).const_sub (2:ℝ)
      simpa using h
    have hlog : HasDerivAt (fun s : ℝ => Real.log (2 - 3*s)) ((-3)/(2-3*x)) x :=
      hnum.log (ne_of_gt hpos)
    have hden : HasDerivAt (fun s : ℝ => 1 - s) (-1) x := by
      have h : HasDerivAt (fun s : ℝ => 1 - s) (-(1:ℝ)) x := (hasDerivAt_id x).const_sub (1:ℝ)
      simpa using h
    have hd := hlog.div hden hne
    have hder : deriv (fun s : ℝ => Real.log (2 - 3 * s) / (1 - s)) x
        = (((-3)/(2-3*x))*(1-x) - Real.log (2-3*x)*(-1))/(1-x)^2 := hd.deriv
    refine le_of_eq_of_le hder ?_
    have hlog_le : Real.log (2 - 3*x) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos hpos
      linarith
    have key : (2-3*x) * Real.log (2-3*x) - 3*(1-x) ≤ 0 := by
      have h2 : (2-3*x) * Real.log (2-3*x) ≤ (2-3*x) := by
        have h := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hpos)
        simpa using h
      linarith
    have hnumeq : ((-3)/(2-3*x))*(1-x) - Real.log (2-3*x)*(-1)
        = ((2-3*x)*Real.log (2-3*x) - 3*(1-x))/(2-3*x) := by
      field_simp
      ring
    apply div_nonpos_of_nonpos_of_nonneg
    · rw [hnumeq]
      exact div_nonpos_of_nonpos_of_nonneg key (le_of_lt hpos)
    · positivity

end Work.NumberTheory.Chen.BTermCount
