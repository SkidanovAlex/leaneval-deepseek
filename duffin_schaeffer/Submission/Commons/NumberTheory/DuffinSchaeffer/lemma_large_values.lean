import Mathlib.NumberTheory.WellApproximable
import Submission.Commons.NumberTheory.DuffinSchaeffer.km_full_hard_of_not_tendsto
import Submission.Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure
import Submission.Commons.NumberTheory.DuffinSchaeffer.positive_measure_large_values

/-!
# The `large values` case of the Duffin--Schaeffer conjecture

`lemma_large_values` is the special case of the Duffin--Schaeffer theorem in which every
non-zero radius is *large*, i.e. `(n : ℝ) * δ n ≥ 1/2` whenever `δ n ≠ 0`
(equivalently, the arcs of radius `δ n` around the reduced fractions of denominator `n`
overlap at least to the extent of touching fractions one lattice step away).

This is Koukoulopoulos--Maynard, *On the Duffin--Schaeffer conjecture*, Lemma 2.2, which
they deduce from Pollington--Vaughan, *The k-dimensional Duffin and Schaeffer conjecture*,
Mathematika 37 (1990), Theorem 2.

## Proof

We split on the behaviour of `δ` at infinity.

* If `δ` does **not** tend to `0`, then `km_full_hard_of_not_tendsto` (commons) shows
  directly that the well-approximable set has full measure (indeed it is all of the
  circle): the radii stay away from `0` and reduced fractions of arbitrarily large
  denominators are dense, so every point is eventually approximated.

* If `δ → 0`, the *large values* second-moment analysis of Pollington--Vaughan
  (`positive_measure_large_values`, commons) gives that the well-approximable set has
  **positive** measure, and Gallagher's ergodic 0--1 law in the form
  `volume_eq_one_of_positive_measure` (commons) upgrades this to full measure.
-/

open MeasureTheory

namespace Commons.NumberTheory.DuffinSchaeffer

theorem lemma_large_values (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hlarge : ∀ n, δ n = 0 ∨ (1 : ℝ) / 2 ≤ (n : ℝ) * δ n)
    (h : ¬ Summable fun n : ℕ => (n.totient : ℝ) * δ n) :
    MeasureTheory.volume (addWellApproximable UnitAddCircle δ) = 1 := by
  by_cases hδt : Filter.Tendsto δ Filter.atTop (nhds 0)
  · exact volume_eq_one_of_positive_measure δ hδt
      (positive_measure_large_values δ hδ hδt hlarge h)
  · exact km_full_hard_of_not_tendsto δ hδ hδt

end Commons.NumberTheory.DuffinSchaeffer
