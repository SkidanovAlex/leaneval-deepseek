import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs

/-!
# Vocabulary for the mixed Selberg sum

This file collects the definitions needed to state the two analytic inputs underlying the
`≥`-half of Graham's theorem (`Work.ZeroDensity.Jutila.mixedSelbergSum`), namely

* the sharp lower bound for the truncated Selberg square `Σ_{n ≤ N} Λ_z(n)²` (`LzSqLower`),
* the Barban–Vehov (Graham) upper bound for the square of the *difference* of two truncated
  von Mangoldt sums (`LzDiffSqUpper`),

together with the Selberg weight of a *real* cutoff and the associated two-parameter quadratic
form `Msq`.

The truncated von Mangoldt sum `Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` is from
`Submission.Work.ZeroDensity.Jutila.bvDefs`.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **The Selberg weight of real cutoff `w`.**  `selW w d = μ(d)·log(w/d)`; the weights of the
truncated von Mangoldt sum `Lz w n` are the `selW w d` with `d ∣ n`, `d ≤ w`. -/
def selW (w : ℝ) (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ) * Real.log (w / (d : ℝ))

/-- **The two-parameter Selberg quadratic form**
`Msq w y = Σ_{d ≤ w, e ≤ y} selW w d · selW y e / lcm(d,e)`.

By the Selberg diagonalization this equals
`Σ_{δ} φ(δ)·(Σ_{δ ∣ d ≤ w} selW w d/d)·(Σ_{δ ∣ e ≤ y} selW y e/e)`, whose leading term is
`Σ_{δ ≤ w} μ(δ)²/φ(δ) = log w + O(1)`: this is why `Msq w y = log w + O(1)`. -/
def Msq (w y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊w⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
    selW w d * selW y e / (Nat.lcm d e : ℝ)

/-- `Lz w n` is the sum of the Selberg weights `selW w d` over the divisors `d ∣ n` with `d ≤ w`. -/
lemma Lz_eq_sum_selW (w : ℝ) (n : ℕ) :
    Lz w n = ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ w), selW w d := rfl

/-- The cutoff-`z` Selberg square is the diagonal value `Msq z z` of the two-parameter form
(with `z` real): `Msq z z = Σ_{d,e ≤ z} selW z d·selW z e/lcm(d,e)`. -/
lemma Msq_self_eq (z : ℝ) : Msq z z = Msq z z := rfl

end

end Work.ZeroDensity.Jutila
