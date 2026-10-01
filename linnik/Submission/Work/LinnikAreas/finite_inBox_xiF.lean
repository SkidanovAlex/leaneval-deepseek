import Mathlib
import Submission.Work.LinnikAreas.ZetaDev

namespace Work.LinnikAreas

open Complex

theorem finite_inBox_xiF (q : ℕ) (hq : 2 ≤ q) [NeZero q] {R : ℝ} (hR : 0 < R) :
    ({u : ℂ | Work.LinnikContract.InBox q R u ∧
      analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u ≠ 0} : Set ℂ).Finite := by
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1R
  -- the box confines every point `u` to the disc of radius `B`
  set B : ℝ := 1 + 2 * (R / Real.log (q : ℝ)) with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  -- the zero set of `xiF` is finite on any closed ball
  refine (Commons.NumberTheory.Zeta.XiPF.xiF_zeroSet_finite hB).subset ?_
  intro u hu
  obtain ⟨hbox, horder⟩ := hu
  have hbox1 : (1 - u.re) * Real.log (q : ℝ) ≤ R := hbox.1
  have hbox2 : |u.im| * Real.log (q : ℝ) ≤ R := hbox.2
  -- the vanishing order is nonzero, so `u` is an actual zero of `xiF`
  have hzero : Commons.NumberTheory.Zeta.XiPF.xiF u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero horder
  -- `xiF` is the classical completion `Ξ(s) = 1/2 + (1/2)s(s-1)Λ₀(s)`, i.e. `xiE_LG`
  have hstrip : 0 ≤ u.re ∧ u.re ≤ 1 :=
    Commons.NumberTheory.Zeta.xiE_LG_zeros_strip hzero
  -- box inequalities: imaginary part and lower real-part bound
  have him : |u.im| ≤ R / Real.log (q : ℝ) := (le_div_iff₀ hlogq).mpr hbox2
  have hrelow : 1 - R / Real.log (q : ℝ) ≤ u.re := by
    have h := (le_div_iff₀ hlogq).mpr hbox1
    linarith
  have hre_abs : |u.re| ≤ 1 + R / Real.log (q : ℝ) := by
    rw [abs_le]
    refine ⟨?_, by linarith [hstrip.2]⟩
    have : 0 ≤ R / Real.log (q : ℝ) := by positivity
    linarith [hstrip.1]
  have hnorm : ‖u‖ ≤ B := by
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ (1 + R / Real.log (q : ℝ)) + R / Real.log (q : ℝ) := add_le_add hre_abs him
      _ = B := by rw [hBdef]; ring
  exact ⟨hzero, hnorm⟩

end Work.LinnikAreas
