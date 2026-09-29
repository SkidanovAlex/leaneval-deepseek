import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_pole_strip

noncomputable section
open Complex
open scoped Real

namespace Commons.NumberTheory.Zeta

/-!
# `zeta_logDeriv_re_pole`: log-derivative real-part pole bound above a zero of ζ

**Statement.**  There is `C > 0` and `H ≥ 2` such that, whenever `β + i·t` is a zero of
the Riemann zeta function with `|t| ≥ H` and `1/2 ≤ β < 1`, then for every `0 < x ≤ 1/2`
the real part of `−ζ′/ζ(1 + x + i·t)` is bounded above by the contribution
`−1/(x + (1 − β))` of the pole of `−ζ′/ζ` at `β + i·t`, plus an `O(log(|t|+3))` term:

    Re(−ζ′/ζ)(1+x+it) ≤ −1/(x + (1−β)) + C·(log(|t|+3) + 1).

This is the de la Vallée Poussin "pole bound" used to prove the zero-free region
`1 − β ≥ c/log(|t|+3)` for zeros at large height (see
`zeta_zeroFreeRegion_largeHeight`): on the vertical line above the zero, every pole of
`−ζ′/ζ` other than the one at `β + i·t` (other zeros and the trivial zeros, all of real
part `< 1`) has non-positive real-part contribution, the pole at `s = 1` contributes
`Re(1/(s−1)) ≤ 1/|t|`, and the `Γ`-factor remainder is `O(log(|t|+3))`.

The full analytic content (the partial-fraction estimate for `ζ′/ζ` on the strip
`1 < Re s ≤ 2` plus the uniform real-part bound `zeta_logDeriv_re_upper`, both
published in the shared commons) is contained in the identical theorem
`Commons.NumberTheory.Zeta.zeta_logDeriv_re_pole_strip`; this file restates it under
the required name.
-/

/-- **Log-derivative real-part pole bound for ζ.**  See module docstring. -/
theorem zeta_logDeriv_re_pole :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      ∀ t : ℝ, H ≤ |t| → ∀ β : ℝ, (1 / 2 : ℝ) ≤ β → β < 1 →
        riemannZeta (((β : ℂ) + (t : ℂ) * Complex.I)) = 0 →
        ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
        (-deriv riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re ≤
          - (1 / (x + (1 - β))) + C * (Real.log (|t| + 3) + 1) :=
  zeta_logDeriv_re_pole_strip

end Commons.NumberTheory.Zeta
