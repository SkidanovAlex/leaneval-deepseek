import Mathlib

namespace Work.CPhi

theorem exists_differentiableOn_log_ball {c : ℂ} {r : ℝ} {V : ℂ → ℂ}
    (hV : DifferentiableOn ℂ V (Metric.ball c r)) (hne : ∀ z ∈ Metric.ball c r, V z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, Complex.exp (L z) = V z := by
  by_cases hr : r ≤ 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro z hz
      exact absurd hz (by rw [Metric.ball_eq_empty.mpr hr]; exact Set.notMem_empty z)
    · intro z hz
      exact absurd hz (by rw [Metric.ball_eq_empty.mpr hr]; exact Set.notMem_empty z)
  · have hr' : 0 < r := not_le.mp hr
    have hball : IsOpen (Metric.ball c r) := Metric.isOpen_ball
    have hpc : IsPreconnected (Metric.ball c r) := (convex_ball c r).isPreconnected
    have hmem : c ∈ Metric.ball c r := by
      rw [Metric.mem_ball]; simpa using hr'
    have hf : DifferentiableOn ℂ (fun z => deriv V z / V z) (Metric.ball c r) :=
      (hV.deriv Metric.isOpen_ball).div hV hne
    obtain ⟨g, hgc, hg⟩ := (hf.isExactOn_ball).with_val_at c (Complex.log (V c))
    have hgdiff : DifferentiableOn ℂ g (Metric.ball c r) := fun z hz =>
      (hg z hz).differentiableAt.differentiableWithinAt
    set h : ℂ → ℂ := fun z => Complex.exp (g z) / V z with hh
    have hhdiff : DifferentiableOn ℂ h (Metric.ball c r) := by
      rw [hh]
      exact hgdiff.cexp.div hV hne
    have hderiv : Set.EqOn (deriv h) 0 (Metric.ball c r) := by
      intro z hz
      have hz0 : V z ≠ 0 := hne z hz
      have hgz : HasDerivAt g (deriv V z / V z) z := hg z hz
      have hexpz : HasDerivAt (fun w => Complex.exp (g w))
          (Complex.exp (g z) * (deriv V z / V z)) z := hgz.cexp
      have hVz : HasDerivAt V (deriv V z) z :=
        (hV.differentiableAt (hball.mem_nhds hz)).hasDerivAt
      have hquot := hexpz.div hVz hz0
      have hnum : Complex.exp (g z) * (deriv V z / V z) * V z -
          Complex.exp (g z) * deriv V z = 0 := by
        rw [mul_assoc, div_mul_cancel₀ (deriv V z) hz0, sub_self]
      have hder' : deriv ((fun w => Complex.exp (g w)) / V) z = 0 := by
        rw [hquot.deriv, hnum, zero_div]
      rw [hh]
      exact hder'
    have hc1 : h c = 1 := by
      rw [hh]
      simp only [hgc, Complex.exp_log (hne c hmem), div_self (hne c hmem)]
    refine ⟨g, hgdiff, fun z hz => ?_⟩
    have hcz : h z = h c :=
      (IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball hpc hhdiff hderiv hmem hz).symm
    have hz1 : h z = 1 := by rw [hcz, hc1]
    have : Complex.exp (g z) / V z = 1 := by simpa only [hh] using hz1
    exact (div_eq_one_iff_eq (hne z hz)).mp this

end Work.CPhi
