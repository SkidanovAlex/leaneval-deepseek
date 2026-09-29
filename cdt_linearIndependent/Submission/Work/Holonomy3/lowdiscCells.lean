import Mathlib
import Submission.Work.Holonomy3.siegelDefs

/-!
# The half-open grid cells of the low-discrepancy lattice count

For the counting argument of `Work.Holonomy3.lattice_lowdisc_card` the exponent vectors
`k : Fin d → ℕ` with all coordinates `< D` are put in bijection with the half-open cells
`cell d D k = ∏_j [k_j/D, (k_j+1)/D) ⊆ [0,1)^d`.  The cells attached to distinct `k` are
pairwise disjoint, each has `(muP d)`-measure `D^{-d}`, and a cell whose centre `k/D` has box
discrepancy `≥ ε` is contained in the tail event `{u | ε/2 ≤ disc u}`.
-/

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open scoped BigOperators

/-- The half-open grid cell `∏_j [k_j/D, (k_j+1)/D)` attached to the exponent vector `k`. -/
def cell (d D : ℕ) (k : Fin d → ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun j => Set.Ico ((k j : ℝ) / (D : ℝ)) (((k j : ℝ) + 1) / (D : ℝ)))

lemma mem_cell {d D : ℕ} {k : Fin d → ℕ} {u : Fin d → ℝ} :
    u ∈ cell d D k ↔
      ∀ j, u j ∈ Set.Ico ((k j : ℝ) / (D : ℝ)) (((k j : ℝ) + 1) / (D : ℝ)) :=
  Set.mem_univ_pi

end Work.Holonomy3
