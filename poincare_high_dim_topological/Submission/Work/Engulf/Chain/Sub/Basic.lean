import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.mem_hullOf
import Submission.Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic

/-!
# `Submission.Work.Engulf.Chain.Sub.Basic`

Auxiliary API for `Work.Engulf.Chain.E5` (Newman §15): relative interiors of faces of a
simplicial complex, and the relationship between the faces of a subdivision `Γ₁` and those of
the coarse complex `Γ` (`E5` subdivides `Γ` so that the shelled `(q+1)`-faces have small
`f`-image; the chart hypothesis of `L7c` then has to be transported from `Γ` to `Γ₁`).

Main definition: `RelInt K s p` -- `p` lies in the relative interior of the face `s` of `K`
(i.e. `p ∈ simp s` and `p` lies in no proper subface of `s`).
-/

open Set Metric PL

namespace Work.Engulf.Chain

variable {N : ℕ}

/-- `p` lies in the **relative interior** of the face `s` of the complex `K`: `p ∈ simp s` and
`p` is in no proper subface of `s` which is a face of `K`. -/
def RelInt (K : PL.Cx N) (s : Finset (PL.E N)) (p : PL.E N) : Prop :=
  p ∈ PL.simp s ∧ ∀ s' ∈ K.faces, s' ⊂ s → p ∉ PL.simp s'

theorem RelInt.mem (K : PL.Cx N) (s : Finset (PL.E N)) (p : PL.E N) (h : RelInt K s p) :
    p ∈ PL.simp s := h.1

theorem RelInt.not_mem (K : PL.Cx N) (s : Finset (PL.E N)) (p : PL.E N) (h : RelInt K s p)
    {s' : Finset (PL.E N)} (hs' : s' ∈ K.faces) (hss' : s' ⊂ s) : p ∉ PL.simp s' := h.2 s' hs' hss'

end Work.Engulf.Chain
