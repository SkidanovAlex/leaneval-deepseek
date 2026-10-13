import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.CD.fibDerivGraph_mem
import Submission.Work.WilG4a.CD.inflated_mem
import Submission.Work.WilG4a.CD.sliceContDiffAt_mem

set_option autoImplicit false
noncomputable section

namespace Work.WilG4a

open WilkiesDesign

/-- `sliceGeq f j`: the set of `z` at which the slice `x ↦ f (init z) x` is `C^j` at `z (last)`
with `j`-th derivative `≥ 0`. -/
def sliceGeq {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  WilkiesDesign.projLast (CD.fibDerivGraph f j ∩
    {w : Fin (p + 2) → ℝ | 0 ≤ w (Fin.last (p + 1))})

/-- `sliceLeq f j`: the set of `z` at which the slice `x ↦ f (init z) x` is `C^j` at `z (last)`
with `j`-th derivative `≤ 0`. -/
def sliceLeq {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  WilkiesDesign.projLast (CD.fibDerivGraph f j ∩
    {w : Fin (p + 2) → ℝ | w (Fin.last (p + 1)) ≤ 0})

/-- The per-member "locally good" set: the points `z` at which the slice `x ↦ f (init z) x` is
`C^{r+2}` on a neighbourhood of `z (last)` and, for every `j ≤ r+1`, the `j`-th derivative of
the slice has locally constant sign at `z (last)`. -/
def locGoodSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (r : ℕ) : Set (Fin (p + 1) → ℝ) :=
  CD.inflated p (WilkiesDesign.projLast (CD.fibDerivGraph f (r + 2))) ∩
    ⋂ j : Fin (r + 2),
      (CD.inflated p (sliceGeq f j.val) ∪ CD.inflated p (sliceLeq f j.val))

/-- **The all-members locally good set.**  This is the set on which every family member is
locally `C^{r+2}` with locally constant-signed derivatives; it is the set of points at which an
affine chart is *valid*. -/
def allGoodSet {p : ℕ} (k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (r : ℕ) :
    Set (Fin (p + 1) → ℝ) :=
  ⋂ i : Fin k, locGoodSet (F i) r

/-- The "bad" set of the all-members-good structure inside the strip. -/
def badSet {p : ℕ} (k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (r : ℕ) :
    Set (Fin (p + 1) → ℝ) :=
  (allGoodSet k F r)ᶜ ∩ {z : Fin (p + 1) → ℝ | z (Fin.last p) ∈ I}

/-- The "bad" set of a *single* member's locally-good structure, inside the strip. -/
def locBadSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (r : ℕ) : Set (Fin (p + 1) → ℝ) :=
  (locGoodSet f r)ᶜ ∩ {z : Fin (p + 1) → ℝ | z (Fin.last p) ∈ I}

end Work.WilG4a
