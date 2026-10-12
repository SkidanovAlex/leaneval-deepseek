import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU
import Submission.Work.BoseFixB3.Split.integrableOn_abox_of_prod
import Submission.Work.BoseFixB3.Split.integrable_chi_wScaled_chi_local
import Submission.Work.BoseFixR.BlockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.PotSplitDefs` — context module for `Work.BoseFixR.PotSplit`

This module only collects the imports and the one definition that the lemma
`Work.BoseFixR.PotSplit` and its supporting lemmas need:

* `Work.BoseFixR.comb k j z y` — the configuration of `k + j` particles whose first
  `k` slots are `z` and whose last `j` slots are `y` (the map `(z,y) ↦ Λ^{k+j}`);
* the two definitional identities `bfL Φ y z = Φ (comb k j z y)` and
  `bfR Φ z y = Φ (comb k j z y)` (both are `rfl`, by construction of `bfL`/`bfR`).

`comb` agrees with `Submission.BoseGases.mergeBlock` (the two differ only in that
`mergeBlock` routes through `finSumFinEquiv`), and `Submission.BoseGases.blockSplitEquiv`
is its inverse: `blockSplitEquiv k j (comb k j z y) = (z, y)`.
-/

noncomputable section

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false

/-- **The two-block combination map**: the configuration of `k + j` particles whose first
`k` coordinates are `z` and whose last `j` coordinates are `y`. -/
def comb {k j : ℕ} (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    Submission.BoseGases.X (k + j) :=
  fun i => if h : (i : ℕ) < k then z ⟨i, h⟩ else y ⟨(i : ℕ) - k, by omega⟩

/-- **The first-block fibre is `Φ` evaluated at the combined configuration.** -/
lemma bfL_eq_comb {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (y : Submission.BoseGases.X j) (z : Submission.BoseGases.X k) :
    bfL Φ y z = Φ (comb z y) := rfl

/-- **The second-block fibre is `Φ` evaluated at the combined configuration.** -/
lemma bfR_eq_comb {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    bfR Φ z y = Φ (comb z y) := rfl

/-- `bfL` and `bfR` agree pointwise (both are `Φ ∘ comb`). -/
lemma bfL_bfR_eq_comb {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    bfL Φ y z = bfR Φ z y := rfl

end Work.BoseFixR
