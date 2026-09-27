import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.mem_suppS_iff_of_expansion
import Submission.Work.Compact.Noncompact.rSupp_inf_eq
import Submission.Work.Compact.Noncompact.suppS_empty

namespace Work.Compact.Noncompact

/-- A `k`-chain supported both in `S` and in `T` is supported in `S ∩ T` (this is
`rSupp_inf_eq`, rewritten using the definitional identity `suppS = rSupp`), and a chain
supported in `∅` is zero (`suppS_empty`).  Hence for disjoint `S` and `T` the only chain
supported in both is `0`. -/
theorem eq_zero_of_mem_suppS_of_disjoint {X : TopCat} {S T : Set X} (hd : Disjoint S T) (k : ℕ)
    {c : Work.Compact.Noncompact.Ch X k}
    (hS : c ∈ Work.Compact.Noncompact.suppS X S k)
    (hT : c ∈ Work.Compact.Noncompact.suppS X T k) : c = 0 := by
  -- `c` lies in both support submodules, hence in their intersection.
  have hST : c ∈ Work.Compact.Noncompact.suppS X (S ∩ T) k := by
    have h : c ∈ Work.Compact.Noncompact.rSupp X S k ⊓ Work.Compact.Noncompact.rSupp X T k :=
      Submodule.mem_inf.mpr ⟨hS, hT⟩
    rw [Work.Compact.Noncompact.rSupp_inf_eq (X := X) S T k] at h
    exact h
  -- Disjointness rewrites `S ∩ T` to `∅`, and there are no chains supported in `∅`.
  rw [Set.disjoint_iff_inter_eq_empty] at hd
  rw [hd, Work.Compact.Noncompact.suppS_empty (X := X) k] at hST
  exact hST

end Work.Compact.Noncompact
