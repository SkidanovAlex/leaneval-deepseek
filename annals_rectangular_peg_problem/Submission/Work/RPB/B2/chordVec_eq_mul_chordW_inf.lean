import Mathlib
import Submission.Work.RPB.B2.PhaseDefs

/-!
# `chordVec = r * chordW` under mere smoothness (`C^∞`)

`chordW c τ t r = ∫_{s ∈ [-1,1]} c'(t + s r) ds` is by construction `chordVec / r`: the change of
variables `u = t + s r` in the interval integral turns it into
`r * ∫_{s ∈ [-1,1]} c'(t + s r) ds = ∫_{u ∈ t - r}^{t + r} c'(u) du`,
and the fundamental theorem of calculus gives `c τ (t + r) - c τ (t - r) = chordVec c τ t r`.
No hypothesis on `r` is needed: at `r = 0` both sides vanish.

The point of this file (compared with `chordVec_eq_mul_chordW`) is that the argument only ever
uses *smoothness* of the curve, i.e. the exponent `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞) = C^∞`, and not the
stronger analytic exponent `ω = (⊤ : WithTop ℕ∞)`: the fundamental theorem of calculus needs only
differentiability plus continuity of the derivative, both of which `C^∞` supplies.
-/

open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

theorem chordVec_eq_mul_chordW_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) (τ t r : ℝ) :
    Work.RPB.chordVec c τ t r = (r : ℂ) * Work.RPB.B2.chordW c τ t r := by
  -- the slice `u ↦ c τ u` is smooth, hence so is its derivative
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => c τ u) := by
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (τ, u)) :=
      contDiff_prodMk_right τ
    simpa [Function.comp_def] using hc.comp hg
  have hdiff : Differentiable ℝ (fun u : ℝ => c τ u) := hf.differentiable (by simp)
  have hcontd : Continuous (deriv (fun u : ℝ => c τ u)) := hf.continuous_deriv (by simp)
  -- fundamental theorem of calculus on the transformed interval
  have hftc : (∫ u in (t - r)..(t + r), deriv (fun u : ℝ => c τ u) u)
      = c τ (t + r) - c τ (t - r) :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff.differentiableAt)
      (hcontd.intervalIntegrable _ _)
  -- change of variables `u = t + r * s`, which produces exactly the factor `r`
  have hsub : (r : ℂ) * (∫ s in (-1:ℝ)..1, deriv (fun u : ℝ => c τ u) (t + s * r))
      = ∫ u in (t - r)..(t + r), deriv (fun u : ℝ => c τ u) u := by
    rw [show (∫ s in (-1:ℝ)..1, deriv (fun u : ℝ => c τ u) (t + s * r))
          = ∫ s in (-1:ℝ)..1, deriv (fun u : ℝ => c τ u) (t + r * s) from by
        congr 1; funext s; rw [mul_comm]]
    rw [← Complex.real_smul]
    rw [intervalIntegral.smul_integral_comp_add_mul]
    simp only [mul_neg, mul_one, sub_eq_add_neg]
  rw [Work.RPB.chordVec, Work.RPB.B2.chordW, hsub, hftc]

end Work.RPB.B2
