import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_one_add_add_bound_curve_sqrt_left_curve

namespace Commons.NumberTheory.Zeta

/-- **Sharp `1/2`-power bound for `ζ(1+z+z')` when `z` and `z'` both lie on (or at most `β/log 2`
to the left of) the classical zero-free curve `{Re = -β/log(|Im|+2)}`.**

The admissible region is `-β/log 2 ≤ Re z ≤ -β/log(|z.im|+2)`, and symmetrically for `z'`; both
inequalities are needed and sufficient:
* `Re z ≤ -β/log(|z.im|+2)` keeps the pole at `1` under control: with
  `A := log(|z.im|+2)`, `B := log(|z'.im|+2)` one has `(z+z').re ≤ -β/A - β/B < 0`, hence
  `β/A + β/B ≤ ‖(1+z+z')-1‖` and `1/‖(1+z+z')-1‖ ≤ (A+B)/β ≤ 2·log base/β ≤ 4·base^{1/2}/β`
  with `base := |z.im|+|z'.im|+3 ≥ 1` (using `log x ≤ 2x^{1/2}` for `x ≥ 1`).
  (Dropping this side makes the statement FALSE: `z = z' = -ε` puts `1+z+z' = 1-2ε` next to the
  pole while `base = 3`.)
* `Re z ≥ -β/log 2` keeps `1+z+z'` in the strip where the strip bounds are available:
  `Re(1+z+z') ≥ 1 - 2β/log 2 ≥ 0.711 > 1/2 + 1/5` (as `β ≤ 1/10`, `Real.log_two_gt_d9`).
  (Dropping this side makes the statement FALSE as well: `z = -1+it`, `z' = -1` give
  `‖ζ(-1+it)‖ ≍ |t|^{3/2}`, while `base ≍ |t|`.)

Hence with `δ = 1/5`:
* if `|Im(1+z+z')| ≥ 1` use `Commons.NumberTheory.Zeta.zeta_strip_growth`, whose exponent
  `1/2 - δ/2 = 2/5 ≤ 1/2` gives `C₁(1+1/δ)(|Im(1+z+z')|+3)^{2/5} ≤ 6C₁·base^{1/2}` (as `base ≥ 1`);
* if `|Im(1+z+z')| ≤ 1` use `Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound`, giving
  `C₂(1+1/δ)(1 + 1/‖(1+z+z')-1‖) ≤ 6C₂(1 + 4·base^{1/2}/β) ≤ (6C₂ + 24C₂/β)·base^{1/2}`
  (note `1+z+z' ≠ 1` because its real part is `< 1`).  Take
  `C := 6C₁ + 6C₂ + 24C₂/β`.

In particular, for `z = Commons.Analysis.Complex.gam β t₀`, `z' = Commons.Analysis.Complex.gam β t`
(real parts `-β/log(|t|+2)`) this gives a two-variable form of
`Commons.NumberTheory.Zeta.zeta_curve_shift_bound` with the combined base `|t₀|+|t|+3` and
exponent `1/2` — e.g. the hypothesis `hznumγ` of the Green–Tao two-pole shift. -/
theorem zeta_one_add_add_bound_curve_sqrt_curve {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ z z' : ℂ,
      -(β / Real.log 2) ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
      -(β / Real.log 2) ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
      ‖riemannZeta (1 + z + z')‖ ≤ C * (|z.im| + |z'.im| + 3) ^ ((1:ℝ) / 2) := by
  exact zeta_one_add_add_bound_curve_sqrt_left_curve hβ hβ10

end Commons.NumberTheory.Zeta
