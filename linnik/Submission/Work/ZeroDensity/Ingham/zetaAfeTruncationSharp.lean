import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeClean.zetaAfeSharp

/-!
# The sharp (un-smoothed) approximate functional equation for `ζ` on the critical line

Target (`Work.ZeroDensity.Ingham.zetaAfeTruncationSharp`): there is an absolute `C > 0`
such that for every real `t ≥ 1`, with `N = ⌊√(t/2π)⌋ + 1`,

`‖ζ(1/2 + it)‖ ≤ C * (1 + ‖Σ_{n ≤ N} n^{-(1/2 + it)}‖)`.

## Status / roadmap (why this is a real theorem, and how it is proved here)

This is the classical **approximate functional equation** (Titchmarsh, *Theory of the Riemann
Zeta-function*, Thm 4.11/4.13; Iwaniec–Kowalski Thm 5.3).  It is *not* a corollary of the
*smoothed* approximate functional equation: with any admissible Gaussian smoothing the weight
`W_s(x)` in the smoothed AFE is a smooth step in `log x` of width `O(1)`, hence nearly constant
over a window of `N/e … Ne` integers, and the comparison of the smoothed sum with the sharp
truncated sum loses a factor `t^{1/4}`; making the step sharp in `n` forces the smoothing out of
the evenness used to identify the dual sum, and the resulting "weights" blow up
(`W_{1-s}` is not the conjugate of `W_s`).

The proof implemented here is the classical **Euler–Maclaurin + sawtooth–Fourier** route, which
is elementary (real analysis only) and gives the *sharp* truncated sums with an explicit error
`O(t^{-1/4} log t)`.

### Steps

1. `zetaEMIntegral` (delegated): for `0 < Re s`, `s ≠ 1`, `N ≥ 1`,
   `ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 - s ∫_N^∞ ({u} - 1/2) u^{-s-1} du`,
   where `{u} = Int.fract u`.  (First-order Euler–Maclaurin; per-interval
   `∫_a^{a+1} ({u}-1/2) f' = (f(a)+f(a+1))/2 - ∫_a^{a+1} f` summed and analytically continued.)

2. `fractFourierIntegral` (delegated): the pointwise sawtooth expansion
   `{u} - 1/2 = -(1/π) Σ_{k ≥ 1} sin(2πk u)/k` integrated termwise:
   `∫_N^∞ ({u}-1/2) u^{-s-1} du = -Σ_{k ≥ 1} (1/(πk)) ∫_N^∞ sin(2πk u) u^{-s-1} du`.
   The interchange is justified by dominated convergence (the sawtooth partial sums are
   uniformly bounded) plus the integration-by-parts bound `|∫ sin | = O(1/(kN))`.

3. Substitution `v = 2πk u`:
   `∫_N^∞ sin(2πk u) u^{-s-1} du = (2πk)^s T(2πk N)`,
   `T(A) = ∫_A^∞ sin v · v^{-s-1} dv`.

4. Asymptotics of `T(A)` (delegated in parts):
   * `sinIntegralComplete`: `∫_0^∞ sin v · v^{-s-1} dv = Γ(-s) sin(-πs/2)` for `0 < Re s < 1`;
     call this constant `c₀`, so `T(A) = c₀ - ∫_0^A sin v v^{-s-1} dv`.
   * `sinIntegralKummerBound`: `‖∫_0^A sin v v^{-s-1} dv‖ ≤ 8 A^{-Re s}/‖s‖` for `4A ≤ ‖s‖`
     (Kummer expansion of the lower incomplete gamma).
   * `sinIntegralTailBound`: `‖T(A)‖ ≤ 16 A^{-Re s-1}` for `2 |Im s| ≤ A`
     (integration by parts; needs `Im s` bounded by `A`, as the phase `v - Im s·log v`
     has its stationary point at `v = Im s`).

5. Assembly (this file): with `s = 1/2 + it`, `y := t/(2πN)`, and `c₀(2π)^s/π = χ(s)`
   (where `χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s)` is the functional-equation factor, and
   `sΓ(-s) = -Γ(1-s)`),
   `ζ(s) = Σ_{n ≤ N} n^{-s} + χ(s) Σ_{k ≤ y} k^{s-1} + N^{1-s}/(s-1) - N^{-s}/2 + O(t^{-1/4} log t)`.
   For `k ≤ y/4` the "resonant" evaluation `T(2πkN) = c₀ + O(...)` gives exactly the
   `χ(s)`-term with an `O(t^{-1/4} log t)` remainder; for `2y ≤ k` the tail bound makes the
   remainder summable; the remaining window `y/4 ≤ k ≤ 2y` (where the phase `v - t log v` is
   stationary at `v = t`) needs a van-der-Corput/Fresnel estimate of `T(2πkN)`; that estimate
   is the one remaining gap in this development.

6. Conclusion: `y = t/(2πN)` satisfies `|y - N| ≤ 2` and
   `‖Σ_{k ≤ y} k^{s-1}‖ = ‖conj(Σ_{k ≤ ⌊y⌋} k^{-s})‖ ≤ ‖Σ_{n ≤ N} n^{-s}‖ + 3`,
   hence `‖ζ(1/2+it)‖ ≤ 2‖Σ_{n ≤ N} n^{-s}‖ + C` for large `t`; for `1 ≤ t ≤ T₀` the same
   Euler–Maclaurin identity with a fixed `N` gives an absolute bound.
-/

namespace Work.ZeroDensity.Ingham

/-- **Sharp approximate functional equation for `ζ` on the critical line.**
There is an absolute `C > 0` such that for every real `t ≥ 1`,
`‖ζ(1/2 + it)‖ ≤ C · (1 + ‖Σ_{n ≤ ⌊√(t/2π)⌋+1} n^{-(1/2+it)}‖)`. -/
theorem zetaAfeTruncationSharp :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + ‖∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
          (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) :=
  Work.ZeroDensity.Ingham.AfeClean.zetaAfeSharp

end Work.ZeroDensity.Ingham
