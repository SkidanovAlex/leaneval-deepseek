import Mathlib.NumberTheory.WellApproximable
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers

import Submission.Commons.NumberTheory.DuffinSchaeffer.km_full_conv
import Submission.Commons.NumberTheory.DuffinSchaeffer.km_full_hard_of_not_tendsto
import Submission.Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure
import Submission.Work.NumberTheory.DuffinSchaeffer.km_hard_positive

open MeasureTheory

namespace Submission

/-- **Duffin–Schaeffer conjecture** (Koukoulopoulos–Maynard, Ann. of Math. 192 (2020)).

For a nonnegative sequence of approximation radii `δ`, the set of points of the unit circle
lying within distance `δ n` of a point of exact additive order `n` has full measure if and
only if the totient-weighted series `∑ n.totient * δ n` diverges.

The proof assembled here is the standard one:

* `Commons.NumberTheory.DuffinSchaeffer.km_full_conv` — the convergence direction
  (first Borel–Cantelli lemma);
* `Commons.NumberTheory.DuffinSchaeffer.km_full_hard_of_not_tendsto` — if `δ` does not
  tend to `0` then the well-approximable set is the whole circle;
* `Commons.NumberTheory.DuffinSchaeffer.km_positive_small` (proved in
  `Submission/Work/NumberTheory/DuffinSchaeffer/km_positive_small.lean`) — the small-value
  case: `n * δ n ≤ 1/2`, divergent totient-weighted series `⟹` positive measure, via the
  second-moment argument together with `km_prop_gcd` (KM Proposition 5.4) and the
  Pollington–Vaughan reduced-pair window count;
* `Commons.NumberTheory.DuffinSchaeffer.lemma_large_values` — the large-value case
  (Pollington–Vaughan, Mathematika 37 (1990), Theorem 2);
* `Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure` — Gallagher's
  ergodic `0–1` law, upgrading positive measure to full measure.
-/
theorem duffin_schaeffer (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) :
    volume (addWellApproximable UnitAddCircle δ) = 1 ↔
      ¬ Summable fun n : ℕ => n.totient * δ n := by
  constructor
  · intro hvol hs
    have h0 := Commons.NumberTheory.DuffinSchaeffer.km_full_conv δ hδ hs
    rw [hvol] at h0
    exact one_ne_zero h0
  · intro h
    by_cases hδt : Filter.Tendsto δ Filter.atTop (nhds 0)
    · exact Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure δ hδt
        (Commons.NumberTheory.DuffinSchaeffer.km_hard_positive δ hδ hδt h)
    · exact Commons.NumberTheory.DuffinSchaeffer.km_full_hard_of_not_tendsto δ hδ hδt

end Submission
