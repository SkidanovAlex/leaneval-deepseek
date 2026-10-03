import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

/-- Shishikura (A.1.7)(ii), first display: for the covering coordinate
`τ_f(w) = σ/(1 - exp(-2πiαw))` (defined as `Work.Pert.tauC`) we have
`τ_f'(w) = -2πiα τ_f(w)(τ_f(w) - σ)/σ`.

The file should start with `import Mathlib`, `import Submission.Work.Pert.Basic`,
`namespace Work.Pert`, then `open Complex` (this is needed so that the notation `I` in the
hypothesis `hE` resolves to `Complex.I`, exactly as in `Basic.lean`).

Proof sketch: put `E y = Complex.exp (-(2 * Real.pi * I * α * y))`, prove
`he : HasDerivAt E (E w * (-(2 * Real.pi * I * α))) w` by composing `Complex.hasDerivAt_exp`
with `hasDerivAt_const_mul`, then `he1 : HasDerivAt (fun y => 1 - E y) (E w * (2*Real.pi*I*α)) w`
via `HasDerivAt.sub`, then apply `HasDerivAt.div` with `hasDerivAt_const σ` and the hypothesis
that `1 - E w ≠ 0`. Rewrite `Complex.exp (-(2*Real.pi*I*α*w))` to `(tauC σ α w - σ)/tauC σ α w`
using `Work.Pert.exp_eq_tauC` (note this rewrites both the numerator and `(1 - E w)^2`), then
prove the resulting value equality by `field_simp [ha, hσ]` + `ring` where
`ha : 1 - (tauC σ α w - σ)/tauC σ α w ≠ 0` comes from `hz` and `hσ`. Two traps: (1) do NOT use
`simpa` on a `HasDerivAt` goal — the function-space instances can differ and `simpa` fails; use
`rw [hv] at h; exact h` instead. (2) `hasDerivAt_const_mul` gives the function
`fun y => c * y`, so to match the goal `fun y => -(2*Real.pi*I*α*y)` use
`simpa only [neg_mul] using (hasDerivAt_const_mul c).neg` — or prove `HasDerivAt (fun y => -(c*y)) (-c) w`
via `HasDerivAt.neg`/`neg_mul`; `exact` works at the end for the `convert`-free assembly. -/
theorem deriv_tauC {σ α w : ℂ} (hσ : σ ≠ 0) (hz : tauC σ α w ≠ 0)
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1) :
    HasDerivAt (tauC σ α)
      (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ) w := by
  -- `open Complex` makes `I` below resolve to `Complex.I`, as in `Basic.lean`.
  open Complex in
  -- Chain rule for `E y = exp (-(2πiα y))`.
  have hExp : HasDerivAt (fun y : ℂ => Complex.exp (-(2 * Real.pi * I * α * y)))
      (Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))) w := by
    have h1 : HasDerivAt (fun y : ℂ => -(2 * Real.pi * I * α * y)) (-(2 * Real.pi * I * α)) w :=
      (hasDerivAt_const_mul (2 * Real.pi * I * α) (x := w)).neg
    exact (Complex.hasDerivAt_exp (-(2 * Real.pi * I * α * w))).comp w h1
  -- Derivative of the denominator `1 - E y`.
  have hg : HasDerivAt (fun y : ℂ => 1 - Complex.exp (-(2 * Real.pi * I * α * y)))
      (Complex.exp (-(2 * Real.pi * I * α * w)) * (2 * Real.pi * I * α)) w := by
    have h := (hasDerivAt_const (x := w) (c := (1 : ℂ))).sub hExp
    rw [show (0 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))
        = Complex.exp (-(2 * Real.pi * I * α * w)) * (2 * Real.pi * I * α) from by ring] at h
    exact h
  -- The denominator does not vanish at `w`.
  have hne : (1 : ℂ) - Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 0 := by
    intro h
    exact hE (sub_eq_zero.mp h).symm
  -- Quotient rule: `τ_f = σ / (1 - E)`.
  have hdiv := (hasDerivAt_const (x := w) (c := σ)).div hg hne
  -- The computed derivative equals the stated value.
  rw [show (0 * (1 - Complex.exp (-(2 * Real.pi * I * α * w)))
              - σ * (Complex.exp (-(2 * Real.pi * I * α * w)) * (2 * Real.pi * I * α)))
            / (1 - Complex.exp (-(2 * Real.pi * I * α * w))) ^ 2
        = -(2 * Real.pi * I * α) * (σ / (1 - Complex.exp (-(2 * Real.pi * I * α * w))))
            * ((σ / (1 - Complex.exp (-(2 * Real.pi * I * α * w)))) - σ) / σ from by
      field_simp
      ring] at hdiv
  unfold tauC
  exact hdiv

end Work.Pert
