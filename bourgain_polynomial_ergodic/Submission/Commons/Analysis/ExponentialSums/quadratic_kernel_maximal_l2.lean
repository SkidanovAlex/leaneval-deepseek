/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bourgain's ℓ² maximal inequality for the square averages

The target `Commons.Analysis.ExponentialSums.quadratic_kernel_maximal_l2`: the ℓ² maximal
inequality for the averages `(1/N) ∑_{i<N} g (m + i²)` on `ℓ²(ℕ)` (Bourgain, *Pointwise ergodic
theorems for arithmetic sets*, Publ. Math. IHÉS **69** (1989), §6).

The proof is assembled from the shared commons.  The analytic content of the circle method
(§5–§6 of the paper) is in

* `Commons.Analysis.ExponentialSums.quadratic_kernel_circle_method_inputs` — the §5 inputs;
* `Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic_at_quarter` — Bourgain (6.10)
  at the fixed scale `δ = 1/4`;
* `Commons.Analysis.ExponentialSums.quadratic_kernel_major_arc_model` — Bourgain's Lemma 6.14;
* `Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family` and
  `quadratic_kernel_dyadic_of_model` — the error term;
* `Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2` — Bourgain's Lemma 4.1
  (the maximal estimate for the major-arc model multipliers);
* `Commons.Analysis.ExponentialSums.quadratic_kernel_dyadic_reduction_z` and
  `quadratic_kernel_shift_transfer` — the dyadic and `ℤ → ℕ` transfers;
* `Commons.Analysis.ExponentialSums.quadratic_kernel_maximal_l2_of_model` — the final assembly.
-/
import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_maximal_l2_of_model
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2

namespace Commons.Analysis.ExponentialSums

open _root_.MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- **The ℓ² maximal inequality for the quadratic (squares) averages** — Bourgain's
result for the squares, in the discrete form the Calderón transference consumes.  The
maximal operator `sup_N |(1/N) ∑_{i<N} g (m + i²)|` is bounded on `ℓ²(ℤ)`.  This is the
analytic core of Bourgain's polynomial ergodic result for `P(n) = n²`; it is proven by the
circle method (major arcs via the Hardy–Littlewood maximal function and `ℓ²` multiplier
estimates, minor arcs via Weyl's inequality). -/
theorem quadratic_kernel_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + i ^ 2)‖ₑ) ^ (2 : ℝ)
          ∂Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂Measure.count :=
  quadratic_kernel_maximal_l2_of_model quadratic_kernel_model_maximal_l2

end Commons.Analysis.ExponentialSums
