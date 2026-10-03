import Mathlib
import Submission.Work.Pert.pert2v2.mem_Qreg_of_deep_close
import Submission.Work.Pert.pert2v2.deep_arith
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.pert2v2

theorem Xc_ray_aux {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {Ra : ℝ}
    (hasym1 : ∀ w ∈ MandelDim.QLeft d.ξ₀, Ra < ‖w‖ →
      ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖ < 1)
    {Ξ' B N : ℝ} (hB : 0 ≤ B) (hN0 : 0 ≤ N)
    (hN : ∀ x : ℝ, N ≤ x → 2 * ‖a‖ * Real.log (x + 1) +
        2 * (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)) + Ξ' < x)
    {u : ℂ} (hre : u.re ≤ B) (himN : N + B + 1 ≤ |u.im|) (hQ : u ∈ MandelDim.QLeft d.ξ₀)
    (hRa : Ra < |u.im|) :
    u ∈ d.Dφ ∧ Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
  refine ⟨d.Q_sub hQ, ?_⟩
  have hs1 : (1 : ℝ) ≤ |u.im| := by linarith
  have hsB : B + 1 ≤ |u.im| := by linarith
  have hu1 : (1 : ℝ) ≤ ‖u‖ := le_trans hs1 (Complex.abs_im_le_norm u)
  have hX : N ≤ -u.re + |u.im| := by linarith
  -- `‖u‖` is at most `(|Re u| + |Im u|)`, and `|Re u| + |Im u| ≤ (X+1)(2B+1)` with
  -- `X := -u.re + |u.im|`: this is the only place where the two-sided control of `Re u` enters.
  have hnum : ‖u‖ ≤ (-u.re + |u.im| + 1) * (2 * B + 1) := by
    have hnb : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    by_cases hr : 0 ≤ u.re
    · have ha : |u.re| = u.re := abs_of_nonneg hr
      have hkey : u.re + |u.im| ≤ (|u.im| - B + 1) * (2 * B + 1) := by nlinarith
      have h4 : (|u.im| - B + 1) * (2 * B + 1) ≤ (-u.re + |u.im| + 1) * (2 * B + 1) := by
        have : |u.im| - B + 1 ≤ -u.re + |u.im| + 1 := by linarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      linarith [hnb, ha, hkey, h4]
    · have ha : |u.re| = -u.re := abs_of_neg (not_le.mp hr)
      have hX0 : (0 : ℝ) ≤ -u.re + |u.im| := by linarith [abs_nonneg u.im]
      have h4 : -u.re + |u.im| ≤ (-u.re + |u.im| + 1) * (2 * B + 1) := by nlinarith
      linarith [hnb, ha, h4]
  have hu_pos : (0 : ℝ) < ‖u‖ := by linarith
  have hXp : (0 : ℝ) < -u.re + |u.im| + 1 := by linarith
  have hlog : Real.log ‖u‖ ≤ Real.log (-u.re + |u.im| + 1) + Real.log (2 * B + 1) := by
    have h1 : Real.log ‖u‖ ≤ Real.log ((-u.re + |u.im| + 1) * (2 * B + 1)) :=
      Real.log_le_log hu_pos hnum
    have h2 : Real.log ((-u.re + |u.im| + 1) * (2 * B + 1)) =
        Real.log (-u.re + |u.im| + 1) + Real.log (2 * B + 1) :=
      Real.log_mul (by linarith) (by linarith)
    linarith [h1, h2]
  -- the logarithmic term of the asymptotic is controlled by `log ‖u‖`
  have hnlog : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
    have h := Work.Pert.norm_clog_le (-u)
    rw [norm_neg] at h
    rw [abs_of_nonneg (Real.log_nonneg hu1)] at h
    exact h
  have hAineq : ‖a * Complex.log (-u) + b‖ + 1 ≤
      ‖a‖ * Real.log (-u.re + |u.im| + 1) +
        (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)) := by
    have h1 : ‖a * Complex.log (-u) + b‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) + ‖b‖ := by
      have h0 : ‖a * Complex.log (-u) + b‖ ≤ ‖a * Complex.log (-u)‖ + ‖b‖ := norm_add_le _ _
      rw [norm_mul] at h0
      exact le_trans h0 (add_le_add_left (mul_le_mul_of_nonneg_left hnlog (norm_nonneg a)) _)
    have h2 : ‖a‖ * Real.log ‖u‖
        ≤ ‖a‖ * (Real.log (-u.re + |u.im| + 1) + Real.log (2 * B + 1)) :=
      mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
    have e1 : ‖a‖ * (Real.log ‖u‖ + Real.pi) = ‖a‖ * Real.log ‖u‖ + ‖a‖ * Real.pi := by ring
    have e2 : ‖a‖ * (Real.log (-u.re + |u.im| + 1) + Real.log (2 * B + 1))
        = ‖a‖ * Real.log (-u.re + |u.im| + 1) + ‖a‖ * Real.log (2 * B + 1) := by ring
    linarith [h1, h2, e1, e2]
  -- the threshold hypothesis at `x := -u.re + |u.im|`, which is `≥ N` because `u.re ≤ B`
  have harith : 2 * (‖a‖ * Real.log (-u.re + |u.im| + 1) +
        (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1))) + Ξ' < -u.re + |u.im| := by
    have hh := hN (-u.re + |u.im|) hX
    have e1 : (2 : ℝ) * (‖a‖ * Real.log (-u.re + |u.im| + 1) +
        (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)))
        = 2 * ‖a‖ * Real.log (-u.re + |u.im| + 1) +
          2 * (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)) := by ring
    linarith [hh, e1]
  have hclose : ‖Work.Pert.Xc d u - (u + (a * Complex.log (-u) + b))‖ < 1 := by
    have h := hasym1 u hQ (lt_of_lt_of_le hRa (Complex.abs_im_le_norm u))
    simpa only [Work.Pert.Xc, add_assoc] using h
  exact mem_Qreg_of_deep_close (z := Work.Pert.Xc d u)
    (A := a * Complex.log (-u) + b) (Ξ := Ξ')
    (c := ‖a‖ * Real.log (-u.re + |u.im| + 1) +
        (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)))
    hclose hAineq harith

end Work.Pert.pert2v2
