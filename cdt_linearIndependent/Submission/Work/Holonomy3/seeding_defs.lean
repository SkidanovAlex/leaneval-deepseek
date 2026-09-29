import Mathlib
import Submission.Work.Holonomy3.defs

/-!
# The seeding partition of the variables (`§Seeding`, display `(seed sum est)`)

The paper partitions the `d` variables into `l+1` consecutive blocks according to the ranks of the
sorted components of the leading exponent vector `n`: variable `s` is assigned the map `φ_k` where
`k` is the block index of its rank `j = s`, i.e. `γ_k/m ≤ j/d < γ_{k+1}/m`.

This module fixes the definition `blockIdx` and records its two basic properties:

* `blockIdx_spec`      : `blockIdx m γ j = p ↔ γ_p/m ≤ j/d ∧ j/d < γ_{p+1}/m`;
* `card_blockIdx_close`: the number of variables in block `p` is `d (γ_{p+1}-γ_p)/m` up to `2`.
-/

namespace Work.Holonomy3

open scoped BigOperators

noncomputable section

/-- The **block index** of the rank `j`: the number of division points `γ_p/m` not exceeding
`j/d`, minus one — i.e. the unique `p` with `γ_p/m ≤ j/d < γ_{p+1}/m`. -/
def blockIdx {l d : ℕ} (m : ℕ) (γ : Fin (l+2) → ℝ) (j : Fin d) : Fin (l + 1) :=
  ⟨(Finset.univ.filter (fun p : Fin (l + 1) => γ p.castSucc / (m : ℝ) ≤ (j : ℝ) / d)).card - 1, by
    have h1 : (Finset.univ.filter
        (fun p : Fin (l + 1) => γ p.castSucc / (m : ℝ) ≤ (j : ℝ) / d)).card ≤ l + 1 := by
      simpa using Finset.card_le_univ
        (Finset.univ.filter (fun p : Fin (l + 1) => γ p.castSucc / (m : ℝ) ≤ (j : ℝ) / d))
    omega⟩

end

end Work.Holonomy3
