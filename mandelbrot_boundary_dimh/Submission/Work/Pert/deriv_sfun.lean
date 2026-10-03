import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

open Complex

set_option linter.unusedVariables false

/-- The derivative of `τ_f(w) = σ/(1 - exp(-2πiαw))`, i.e. Shishikura (A.1.7)(ii) first display.
Proved here self-contained (the same computation as the sibling `Work.Pert.deriv_tauC`). -/
private theorem tauC_hasDerivAt {σ α w : ℂ} (hσ : σ ≠ 0) (hz : tauC σ α w ≠ 0)
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1) :
    HasDerivAt (tauC σ α)
      (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ) w := by
  have h1exp : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 0 := by
    intro h
    exact hE (sub_eq_zero.mp h).symm
  have hinner : HasDerivAt (fun y : ℂ => -(2 * Real.pi * I * α * y))
      (-(2 * Real.pi * I * α)) w :=
    (hasDerivAt_const_mul (2 * Real.pi * I * α)).neg
  have hexp : HasDerivAt (fun y : ℂ => Complex.exp (-(2 * Real.pi * I * α * y)))
      (Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))) w :=
    (Complex.hasDerivAt_exp _).comp w hinner
  have hsub : HasDerivAt (fun y : ℂ => 1 - Complex.exp (-(2 * Real.pi * I * α * y)))
      (0 - Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))) w :=
    (hasDerivAt_const w (1 : ℂ)).sub hexp
  have hd := (hasDerivAt_const w σ).div hsub h1exp
  have hv : (0 * (1 - Complex.exp (-(2 * Real.pi * I * α * w)))
        - σ * (0 - Complex.exp (-(2 * Real.pi * I * α * w)) * (-(2 * Real.pi * I * α))))
      / (1 - Complex.exp (-(2 * Real.pi * I * α * w))) ^ 2
      = -(2 * Real.pi * I * α) * tauC σ α w * (tauC σ α w - σ) / σ := by
    rw [exp_eq_tauC σ α w hσ hE]
    have ha : (1 : ℂ) - (tauC σ α w - σ) / tauC σ α w ≠ 0 := by
      have hha : (1 : ℂ) - (tauC σ α w - σ) / tauC σ α w = σ / tauC σ α w := by
        field_simp
        ring
      rw [hha]
      exact div_ne_zero hσ hz
    field_simp [hσ, hz, ha]
    ring
  rw [hv] at hd
  exact hd

/-- Shishikura (A.1.7)(ii): the `w`-derivative of `s(w) = σ u(τ_f w)/(1 + τ_f w · u(τ_f w))`
(defined as `Work.Pert.sfun u σ α`), written in terms of
`τ_f'(w) = -2πiα τ_f(w)(τ_f(w) - σ)/σ`.

The file should start with `import Mathlib`, `import Submission.Work.Pert.Basic`,
`namespace Work.Pert`, then `open Complex` (so that `I` in `hE` resolves to `Complex.I`, as in
`Basic.lean`). A sibling file `Submission/Work/Pert/deriv_tauC.lean` is being proved in parallel
and may not exist yet: do it self-contained, using the τ' fact locally.

Proof sketch. With `z = tauC σ α w`, `z' = -(2*Real.pi*I*α) * z * (z - σ)/σ`, `u' = deriv u z`,
obtain `hτ : HasDerivAt (tauC σ α) z' w` exactly as in the sibling `deriv_tauC` (chain rule for
the exponential + `HasDerivAt.div` + `Work.Pert.exp_eq_tauC` + `field_simp`/`ring`). Then
`hu.hasDerivAt.comp w hτ : HasDerivAt (fun y => u (tauC σ α y)) (u' * z') w`;
`.const_mul σ` gives the numerator, `hτ.mul hu_comp` then `.const_add 1` the denominator, and
`HasDerivAt.div` applied to those two with the hypothesis `h1` gives the raw quotient rule value
`(σ * (u' * z') * (1 + z*u z) - σ * u z * (z' * u z + z * (u' * z')))/(1 + z*u z)^2`. That equals
the clean stated value `σ * z' * (u' - u z ^ 2)/(1 + z*u z)^2` because the two `z * u * u'` terms
cancel: prove this value equality with plain `ring` (the denominators are identical, so no
`field_simp` is needed), `rw` it, and finish with `exact` (the `sfun` function itself is
definitionally the lambda appearing in the goal, so `exact` works and no `convert`/`funext` is
needed). Trap: do NOT use `simpa` on a `HasDerivAt` goal — the function-space instances can
differ and `simpa` fails; use `rw [hv] at h; exact h` instead. -/
theorem deriv_sfun {u : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0) (hσ : σ ≠ 0)
    (hu : DifferentiableAt ℂ u (tauC σ α w)) (hz : tauC σ α w ≠ 0)
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1)
    (h1 : (1 : ℂ) + tauC σ α w * u (tauC σ α w) ≠ 0) :
    HasDerivAt (sfun u σ α)
      (σ * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ)
        * (_root_.deriv u (tauC σ α w) - u (tauC σ α w) ^ 2)
        / (1 + tauC σ α w * u (tauC σ α w)) ^ 2) w := by
  have hτ := tauC_hasDerivAt hσ hz hE
  have hcomp : HasDerivAt (fun y => u (tauC σ α y))
      (_root_.deriv u (tauC σ α w)
        * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ)) w :=
    hu.hasDerivAt.comp w hτ
  have hnum : HasDerivAt (fun y => σ * u (tauC σ α y))
      (σ * (_root_.deriv u (tauC σ α w)
        * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ))) w :=
    hcomp.const_mul σ
  have hmul : HasDerivAt (fun y => tauC σ α y * u (tauC σ α y))
      ((-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ) * u (tauC σ α w)
        + tauC σ α w * (_root_.deriv u (tauC σ α w)
          * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ))) w :=
    hτ.mul hcomp
  have hden : HasDerivAt (fun y => 1 + tauC σ α y * u (tauC σ α y))
      ((-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ) * u (tauC σ α w)
        + tauC σ α w * (_root_.deriv u (tauC σ α w)
          * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ))) w :=
    hmul.const_add 1
  have hd := hnum.div hden h1
  have hv :
      (σ * (_root_.deriv u (tauC σ α w)
            * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ))
          * (1 + tauC σ α w * u (tauC σ α w))
        - σ * u (tauC σ α w)
          * ((-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ) * u (tauC σ α w)
            + tauC σ α w * (_root_.deriv u (tauC σ α w)
              * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ))))
        / (1 + tauC σ α w * u (tauC σ α w)) ^ 2
      = σ * (-(2 * Real.pi * Complex.I * α) * tauC σ α w * (tauC σ α w - σ) / σ)
        * (_root_.deriv u (tauC σ α w) - u (tauC σ α w) ^ 2)
        / (1 + tauC σ α w * u (tauC σ α w)) ^ 2 := by
    ring
  rw [hv] at hd
  exact hd

end Work.Pert
