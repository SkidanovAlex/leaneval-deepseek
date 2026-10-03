import Mathlib
import Submission.Work.FIArea7.oddPartKernelDefs
import Submission.Work.FIArea4.sqfreeKernel_eq_of_mul_sq

namespace Work.FIArea7

/-- For nonzero `a, b`, the product `a * b` is a perfect square **iff** `a` and `b` have the same
squarefree kernel.

`(→)` is `Work.FIArea4.sqfreeKernel_eq_of_mul_sq`.  `(←)` is the explicit decomposition: writing
`a = d * sa ^ 2` and `b = d * sb ^ 2` with `d = sqfreeKernel a = sqfreeKernel b` (available since
`a, b ≠ 0`, from `Work.FIArea4.sqfree_kernel`), one has `a * b = (d * sa * sb) ^ 2`. -/
theorem sq_iff_sqfreeKernel_eq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ s : ℕ, a * b = s ^ 2) ↔ Work.FIArea4.sqfreeKernel a = Work.FIArea4.sqfreeKernel b := by
  constructor
  · intro ⟨s, hs⟩
    exact Work.FIArea4.sqfreeKernel_eq_of_mul_sq a b (by omega) (by omega) ⟨s, hs⟩
  · intro h
    -- `a = da * sa ^ 2`, `b = db * sb ^ 2` with `da = sqfreeKernel a`, `db = sqfreeKernel b`,
    -- and `h : da = db`; take `s = da * sa * sb`.
    obtain ⟨_, _, hsa, _, _⟩ := Work.FIArea4.sqfree_kernel a ha
    obtain ⟨_, _, hsb, _, _⟩ := Work.FIArea4.sqfree_kernel b hb
    set da := Work.FIArea4.sqfreeKernel a
    set sa := Work.FIArea4.sqPart a
    set sb := Work.FIArea4.sqPart b
    have hsa' : da * sa ^ 2 = a := hsa
    have hsb' : Work.FIArea4.sqfreeKernel b * sb ^ 2 = b := hsb
    have h' : da = Work.FIArea4.sqfreeKernel b := h
    refine ⟨da * sa * sb, ?_⟩
    rw [← hsa', ← hsb', h']
    ring

end Work.FIArea7
