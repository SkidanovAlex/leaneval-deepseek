import Mathlib
import Submission.Work.Pert.dev_base_v3

namespace Work.Pert.PinLogDev

/-!
# `Work.Pert.PinLogDev.anchor_walk_margA`

The `A`-margin `margA Ξ α z = z.re - Ξ + (1/α).re + |z.im + (1/α).im|` of the gate
`Qm Ξ α` is compared at two depths `-M ≤ -x` of the datum's curve `Xc d`.

The only input is the datum's asymptotic
`Xc d (-t) = -t + a log t + b + O(1/1024)` for `t ≥ R`.  Writing `L := log (M/x) ≥ 0`,
the `re`-parts cancel exactly against the explicit `+ (M - x)` on the left, and the
remaining `|·|`- and `log`-terms are controlled by the elementary real facts
`Re a + |Im a| ≤ 2‖a‖` and `|P(log M)| - |P(log x)| ≤ |Im a| · L`.
-/

/-- `margA Ξ α` is `2`-Lipschitz in the complex norm, in the increasing direction. -/
lemma margA_le_add_two_norm (Ξ : ℝ) (α z w : ℂ) :
    Work.Pert.margA Ξ α z ≤ Work.Pert.margA Ξ α w + 2 * ‖z - w‖ := by
  have hre : z.re - w.re ≤ ‖z - w‖ := by
    have h := Complex.abs_re_le_norm (z - w)
    simp only [Complex.sub_re] at h
    linarith [le_abs_self (z.re - w.re)]
  have him : |z.im + (1 / α).im| - |w.im + (1 / α).im| ≤ ‖z - w‖ := by
    have h := abs_sub_abs_le_abs_sub (z.im + (1 / α).im) (w.im + (1 / α).im)
    have h2 : z.im + (1 / α).im - (w.im + (1 / α).im) = z.im - w.im := by ring
    rw [h2] at h
    have h3 : |z.im - w.im| ≤ ‖z - w‖ := by
      have h4 := Complex.abs_im_le_norm (z - w)
      simpa only [Complex.sub_im] using h4
    linarith
  simp only [Work.Pert.margA]
  linarith

/-- Explicit evaluation of `margA` at the linearised point `-x + a log x + b` (`x ≥ 0`). -/
lemma margA_asym (Ξ : ℝ) (α : ℂ) (a b : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Work.Pert.margA Ξ α (-(x : ℂ) + a * Complex.log (x : ℂ) + b)
      = -x + Real.log x * a.re + b.re - Ξ + (1 / α).re
        + |Real.log x * a.im + b.im + (1 / α).im| := by
  have hlog : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hx).symm
  rw [hlog, Work.Pert.margA]
  simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, neg_zero, mul_zero, sub_zero]
  ring_nf

/-- The elementary real core: with `sM = sx + L`, `L ≥ 0` and `ar + |ai| ≤ A`,
`sM·ar + |sM·ai + D + E| - A·L ≤ sx·ar + |sx·ai + D + E|`. -/
lemma linear_core {ar ai A sM sx L D E : ℝ} (hlogM : sM = sx + L) (hL : 0 ≤ L)
    (hA : ar + |ai| ≤ A) :
    sM * ar + |sM * ai + D + E| - A * L ≤ sx * ar + |sx * ai + D + E| := by
  subst hlogM
  have hP : |(sx + L) * ai + D + E| ≤ |sx * ai + D + E| + L * |ai| := by
    have h1 : (sx + L) * ai + D + E = (sx * ai + D + E) + L * ai := by ring
    rw [h1]
    calc |(sx * ai + D + E) + L * ai| ≤ |sx * ai + D + E| + |L * ai| := abs_add_le _ _
      _ = |sx * ai + D + E| + L * |ai| := by rw [abs_mul, abs_of_nonneg hL]
  have hkey : (ar + |ai|) * L ≤ A * L := mul_le_mul_of_nonneg_right hA hL
  nlinarith [hP, hkey]

theorem anchor_walk_margA {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R Ξ : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {α : ℂ} {x M : ℝ} (hRx : R ≤ x) (hRM : R ≤ M) (hx1 : 1 ≤ x) (hxM : x ≤ M) :
    Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ))) + (M - x)
        - 2 * ‖a‖ * Real.log (M / x) - 4 / 1024
      ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(x : ℂ))) := by
  have hxpos : 0 < x := by linarith
  have hMpos : 0 < M := by linarith
  have hLnn : 0 ≤ Real.log (M / x) := Real.log_nonneg (by rw [le_div_iff₀ hxpos]; linarith)
  have hlogM : Real.log M = Real.log x + Real.log (M / x) := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hxpos)]; ring
  have hcoef : a.re + |a.im| ≤ 2 * ‖a‖ := by
    have h1 : a.re ≤ ‖a‖ := Complex.re_le_norm a
    have h2 : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
    linarith
  have hcore : Work.Pert.margA Ξ α (-(M : ℂ) + a * Complex.log (M : ℂ) + b) + (M - x)
        - 2 * ‖a‖ * Real.log (M / x)
      ≤ Work.Pert.margA Ξ α (-(x : ℂ) + a * Complex.log (x : ℂ) + b) := by
    rw [margA_asym Ξ α a b (le_of_lt hMpos), margA_asym Ξ α a b (le_of_lt hxpos), hlogM]
    have h := linear_core (ar := a.re) (ai := a.im) (A := 2 * ‖a‖)
        (sM := Real.log x + Real.log (M / x)) (sx := Real.log x) (L := Real.log (M / x))
        (D := b.im) (E := (1 / α).im) (by ring) hLnn hcoef
    linarith [h]
  have hM1 : Work.Pert.margA Ξ α (Work.Pert.Xc d (-(M : ℂ)))
      ≤ Work.Pert.margA Ξ α (-(M : ℂ) + a * Complex.log (M : ℂ) + b) + 2 * (1 / 1024) := by
    have h := margA_le_add_two_norm Ξ α (Work.Pert.Xc d (-(M : ℂ)))
      (-(M : ℂ) + a * Complex.log (M : ℂ) + b)
    have h2 := hasym M hRM
    linarith
  have hx1' : Work.Pert.margA Ξ α (-(x : ℂ) + a * Complex.log (x : ℂ) + b)
      ≤ Work.Pert.margA Ξ α (Work.Pert.Xc d (-(x : ℂ))) + 2 * (1 / 1024) := by
    have h := margA_le_add_two_norm Ξ α (-(x : ℂ) + a * Complex.log (x : ℂ) + b)
      (Work.Pert.Xc d (-(x : ℂ)))
    have h2 := hasym x hRx
    have h3 : ‖(-(x : ℂ) + a * Complex.log (x : ℂ) + b) - Work.Pert.Xc d (-(x : ℂ))‖
        ≤ 1 / 1024 := by
      rw [norm_sub_rev]; exact h2
    linarith
  linarith

end Work.Pert.PinLogDev
