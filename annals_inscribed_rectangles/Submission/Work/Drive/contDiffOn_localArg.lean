import Mathlib

namespace Work.Drive

/-- **The local argument function of a smooth plane curve is smooth.**

For a `C^∞` curve `z : ℝ → ℂ` and a base parameter `t₀`, the function

`φ s = (Complex.arg (z t₀) + (Complex.log (z s / z t₀)).im) / π`

— the *lift* of the argument of `z` normalised by `z t₀`, i.e. the continuous branch of the angle
that agrees with `Complex.arg (z t₀)` at `s = t₀` — is `C^∞` on the set of parameters `s` for which
`z s / z t₀` lies in the slit plane.  Indeed `s ↦ z s / z t₀` is smooth, `Complex.log` is smooth on
`Complex.slitPlane`, and taking the imaginary part and dividing by `π` are smooth operations.

(When `z t₀ = 0` the set in question is empty and the statement is vacuous.) -/
theorem contDiffOn_localArg {z : ℝ → ℂ} (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z) (t₀ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => (Complex.arg (z t₀) + (Complex.log (z s / z t₀)).im) / Real.pi)
      {s : ℝ | z s / z t₀ ∈ Complex.slitPlane} := by
  set A : Set ℝ := {s : ℝ | z s / z t₀ ∈ Complex.slitPlane}
  have hdiv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => z s / z t₀) A :=
    (hz.div_const (z t₀)).contDiffOn
  have hlog : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.log Complex.slitPlane :=
    Complex.isOpen_slitPlane.contDiffOn_iff.2
      (fun x hx => (Complex.contDiffAt_log hx).restrict_scalars ℝ)
  have hcomp :
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => Complex.log (z s / z t₀)) A :=
    hlog.comp hdiv (fun s hs => hs)
  have him :
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (Complex.log (z s / z t₀)).im) A :=
    (Complex.imCLM.contDiff).comp_contDiffOn hcomp
  exact (contDiffOn_const.add him).div_const Real.pi

end Work.Drive
