import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.prop232Defs

namespace Work.FIArea7.P231

lemma sum_primaryPrimSet_eq_sum_primarySet (c : ℕ) (F : GaussianInt → ℂ)
    (h : ∀ e ∈ Work.FIArea7.primarySet c, ¬ IsCoprime e.re e.im → F e = 0) :
    ∑ e ∈ Work.FIArea7.primaryPrimSet c, F e = ∑ e ∈ Work.FIArea7.primarySet c, F e := by
  refine Finset.sum_subset (fun x hx => ?_) (fun x hx hxnot => ?_)
  · obtain ⟨hp, hg, _⟩ := Work.FIArea7.mem_primaryPrimSet.mp hx
    exact Work.FIArea7.mem_primarySet.mpr ⟨hp, hg⟩
  · refine h x hx (fun hcop => hxnot ?_)
    obtain ⟨hp, hg⟩ := Work.FIArea7.mem_primarySet.mp hx
    exact Work.FIArea7.mem_primaryPrimSet.mpr ⟨hp, hg, hcop⟩

end Work.FIArea7.P231
