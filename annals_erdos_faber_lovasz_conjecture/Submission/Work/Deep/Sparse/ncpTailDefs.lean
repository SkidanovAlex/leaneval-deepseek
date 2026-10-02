/-
# Vocabulary for the lower tail of the truncated occupancy statistic

This module collects the definitions used by the proof of
`Work.Deep.Sparse.ncp_tail_bound`.

For a graph `G` on `V`, a colouring `f : V → Fin k` and a vertex `v`:

* `ncpN G f v j` — the number of colours carried by at least `j` *retained* neighbours of `v`
  (the `j`-th slice occupancy of `occSlice`);
* `indepSets G A j` — the independent `j`-element subsets of a vertex set `A`; a colour class of
  `j` retained neighbours of `v` is such a set;
* `ncpMuT G k v j` — the envelope `μ_j = (|nonAdjPairs G v|/2)/k · 2^j / j!` which dominates the
  first moment of the `j`-th slice occupancy and the `K`-th moment of its counting variable;
* `ncpL D = log (D+2)`, `ncpT D = (log (D+2))^4/5000 + 2` — the logarithmic scale of the tail
  bound and the target exponent;
* `ncpJlev D` — the cutoff level `J` above which the probability of a colour class of size `≥ J`
  is negligible;
* `ncpRR D` — the reference threshold `R` for the per-slice counting variables;
* `ncpKj G k v D j` — the per-slice threshold `max (3 μ_j) R`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of colours carried by at least `j` *retained* neighbours of `v`: the `j`-th slice
occupancy of `occSlice`. -/
noncomputable def ncpN (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k) (v : V)
    (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c)).card

/-- The independent `j`-element subsets of a vertex set `A`. -/
def indepSets (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (j : ℕ) : Finset (Finset V) :=
  (A.powersetCard j).filter (fun S => ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x = y)

@[simp] lemma mem_indepSets {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V} {j : ℕ}
    {S : Finset V} :
    S ∈ indepSets G A j ↔ S ⊆ A ∧ S.card = j ∧ ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x = y := by
  simp [indepSets, Finset.mem_powersetCard, and_assoc]

/-- The envelope `μ_j = (|nonAdjPairs G v|/2) / k · 2^j / j!` of the first moment of `ncpN`. -/
noncomputable def ncpMuT (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (v : V) (j : ℕ) : ℝ :=
  (((nonAdjPairs G v).card : ℝ) / 2) / (k : ℝ) * (2 : ℝ) ^ j / (j.factorial : ℝ)

/-- `L = log (D+2)`. -/
noncomputable def ncpL (D : ℕ) : ℝ := Real.log ((D : ℝ) + 2)

/-- `T = L^4/5000 + 2`, the exponent of the target tail bound. -/
noncomputable def ncpT (D : ℕ) : ℝ := (ncpL D) ^ 4 / 5000 + 2

/-- The cutoff level `J` for the "large colour class" event. -/
noncomputable def ncpJlev (D : ℕ) : ℕ := 19 + 2 * (⌈(ncpL D) ^ 4 / 5000⌉₊ + ⌈ncpL D⌉₊ + 50)

/-- The reference threshold `R` for the per-slice counting variables. -/
noncomputable def ncpRR (D : ℕ) : ℝ := 11 * (ncpT D + Real.log (2 * (ncpJlev D)) + 10)

/-- The per-slice threshold `K_j = max (3 ⌈μ_j⌉) ⌈R⌉`. -/
noncomputable def ncpKj (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (v : V) (D j : ℕ) : ℕ :=
  max (3 * ⌈ncpMuT G k v j⌉₊) ⌈ncpRR D⌉₊

end Work.Deep.Sparse
