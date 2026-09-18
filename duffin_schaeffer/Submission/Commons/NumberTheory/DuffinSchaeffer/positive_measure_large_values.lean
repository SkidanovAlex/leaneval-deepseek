import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.positive_measure_large_values_pv

/-!
# Positive measure in the large-values case of Duffin–Schaeffer

Let `δ : ℕ → ℝ` be a non-negative sequence of approximation radii with `δ n → 0`, and
suppose every non-zero value is *large*, i.e. `(n : ℝ) * δ n ≥ 1/2` whenever `δ n ≠ 0`.
If the φ-weighted series `∑ n.totient * δ n` diverges, then the set of numbers
well-approximated by reduced fractions `a/n` within distance `δ n` has positive measure on
the circle:

`0 < volume (addWellApproximable UnitAddCircle δ)`.

This is the positive-measure half of the "large values" lemma of
Koukoulopoulos–Maynard (Ann. of Math. 192 (2020), Lemma 2.2), which is Pollington–Vaughan,
*The k-dimensional Duffin and Schaeffer conjecture*, Mathematika 37 (1990), Theorem 2
(the `ψ(q) = q·δ(q) ≥ 1/2` regime).

The deep Pollington–Vaughan tail-block/second-moment analysis is carried out in the shared
commons as `Commons.NumberTheory.DuffinSchaeffer.positive_measure_large_values_pv`, whose
statement is exactly the one required here; we invoke it directly.
-/

namespace Commons.NumberTheory.DuffinSchaeffer

open MeasureTheory Filter

theorem positive_measure_large_values (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδt : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hlarge : ∀ n, δ n = 0 ∨ (1 : ℝ) / 2 ≤ (n : ℝ) * δ n)
    (h : ¬ Summable fun n : ℕ => (n.totient : ℝ) * δ n) :
    0 < MeasureTheory.volume (addWellApproximable UnitAddCircle δ) :=
  positive_measure_large_values_pv δ hδ hδt hlarge h

end Commons.NumberTheory.DuffinSchaeffer
