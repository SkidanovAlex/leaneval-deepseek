import Mathlib
import Submission.Work.Serre.MapPathDefs
import Submission.Work.FGThm.mpathOf_comp_mpathFst_homotopic

/-!
# The mapping path space is homotopy equivalent to the total space

For `p : E → B`, the mapping path space `mpath p` (see `Work.Serre.MapPathDefs`) is the space of
pairs `(e, γ)` with `γ` a path in `B` starting at `p e`.  The projection

`mpathFst p : mpath p → E`,  `(e, γ) ↦ e`

has the strict section `mpathOf p : E → mpath p`, `e ↦ (e, const (p e))`:

`(mpathFst p).comp (mpathOf p) = ContinuousMap.id E`.

The other composite, `(mpathOf p).comp (mpathFst p)`, sends `(e, γ)` to `(e, const (p e))` and is
homotopic to the identity of `mpath p` by the path contraction `(e, γ, t) ↦ (e, s ↦ γ (t s))`; this
is `Work.FGThm.mpathOf_comp_mpathFst_homotopic`.  Hence `mpathFst p` is a homotopy equivalence
`mpath p ≃ E`, so the mapping path space is homotopy equivalent to the total space `E`.
-/

open ContinuousMap

namespace Work.FGThm

/-- The projection `mpathFst p : mpath p → E` of the mapping path space is a homotopy equivalence,
with homotopy inverse the section `mpathOf p`.  Consequently the mapping path space `mpath p` is
homotopy equivalent to `E`. -/
theorem mpathHomotopyEquiv {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    Nonempty (ContinuousMap.HomotopyEquiv (Work.Serre.mpath p) E) := by
  refine ⟨ContinuousMap.HomotopyEquiv.mk (Work.Serre.mpathFst p) (Work.Serre.mpathOf p)
    (mpathOf_comp_mpathFst_homotopic p) ?_⟩
  have h : (Work.Serre.mpathFst p).comp (Work.Serre.mpathOf p) = ContinuousMap.id E := by
    ext e; rfl
  rw [h]

end Work.FGThm
