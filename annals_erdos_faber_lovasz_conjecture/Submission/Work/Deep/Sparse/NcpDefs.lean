/-
# The class-sum statistic of the naive colouring procedure, sliced

This module collects the vocabulary in which the concentration proof of
`Work.Deep.Sparse.ncp_concentration` is phrased.

For a graph `G` on `V`, a colouring `f : V → Fin k` and a vertex `v`:

* `occW j = (j-1)(4-j)/2` — the increment `h j - h (j-1)` of `h n = C(n,2) - C(n,3)`;
* `occH n = C(n,2) - C(n,3)` — the contribution of a colour class of size `n` to
  `pairTerm v - tripleTerm v`;
* `occHtrunc J n = occH (min n J)` — its truncation at `J`;
* `occClass G f v J = ∑_c occHtrunc J (colourClassCount G f v c)` — the truncated statistic
  expressed through the colour classes;
* `occSlice G f v J = ∑_{2 ≤ j ≤ J} occW j · #{c : j ≤ colourClassCount G f v c}` — the same
  statistic expressed through the occupancy numbers of its slices;
* `occWsum J = ∑_{2 ≤ j ≤ J} |occW j|` — the Lipschitz constant of `occHtrunc J` in the
  class size.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.SliceDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The increment `h j - h (j-1)` of the class contribution `h n = C(n,2) - C(n,3)`. -/
noncomputable def occW (j : ℕ) : ℝ := ((j : ℝ) - 1) * (4 - (j : ℝ)) / 2

/-- The contribution `C(n,2) - C(n,3)` of a colour class of size `n`. -/
noncomputable def occH (n : ℕ) : ℝ := (n.choose 2 : ℝ) - (n.choose 3 : ℝ)

/-- The truncation of the class contribution at level `J`. -/
noncomputable def occHtrunc (J n : ℕ) : ℝ := occH (min n J)

/-- `∑_{2 ≤ j ≤ J} |occW j|`, the Lipschitz constant of `occHtrunc J` in the class size. -/
noncomputable def occWsum (J : ℕ) : ℝ := ∑ j ∈ Finset.Icc 2 J, |occW j|

/-- The truncated statistic, expressed through the colour classes of `v`. -/
noncomputable def occClass (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k)
    (v : V) (J : ℕ) : ℝ := ∑ c : Fin k, occHtrunc J (colourClassCount G f v c)

/-- The truncated statistic, expressed through the occupancy numbers of its slices. -/
noncomputable def occSlice (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k)
    (v : V) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, occW j *
    (((Finset.univ : Finset (Fin k)).filter
      (fun c => j ≤ colourClassCount G f v c)).card : ℝ)

end Work.Deep.Sparse

namespace Work.Deep.Sparse

/-- The slice truncation level used in the concentration proof (`J = 18`). -/
def ncpJ : ℕ := 18

/-- The logarithmic slack `⌈(log (D+2))^4/5000⌉ + 10` of the concentration proof. -/
noncomputable def ncpBeta (D : ℕ) : ℕ := ⌈((Real.log ((D : ℝ) + 2)) ^ 4 / 5000)⌉₊ + 10

/-- The "large class" level `⌈D^{1/6}⌉ + 10` of the concentration proof. -/
noncomputable def ncpA0 (D : ℕ) : ℕ := ⌈((D : ℝ) ^ ((1 : ℝ) / 6))⌉₊ + 10

/-- The crude mean occupancy `2 D 2^j / j!`, which dominates `k (d/k)^j / j!` when `d ≤ D` and
`k ≤ 2D`. -/
noncomputable def ncpMu (D j : ℕ) : ℝ := 2 * (D : ℝ) * (2 : ℝ) ^ j / (j.factorial : ℝ)

/-- The per-slice threshold `3 ⌈μ_j⌉ + β`. -/
noncomputable def ncpK (D j : ℕ) : ℕ := 3 * ⌈ncpMu D j⌉₊ + ncpBeta D

end Work.Deep.Sparse

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The threshold `ω = (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)` of the concentration
statement. -/
noncomputable def ncpOmega (G : SimpleGraph V) [DecidableRel G.Adj] (k D : ℕ) (v : V) : ℝ :=
  (((nonAdjPairs G v).card : ℝ) / 2) *
    ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))

end Work.Deep.Sparse
