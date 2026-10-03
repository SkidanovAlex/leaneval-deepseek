import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.TF

/-- Torsion-freeness is inherited by subgroups: an element of `G` of finite order maps to an
element of `H` of finite order, which is trivial by hypothesis; injectivity then forces it to be
trivial in `G`. -/
theorem isTorsionFree_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : Work.ORLocInd.IsTorsionFree H) :
    Work.ORLocInd.IsTorsionFree G := by
  intro g hg
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  have h1 : f g = 1 :=
    h (f g) (by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨n, hn, by rw [← map_pow, hgn, map_one]⟩)
  exact hf (by rw [h1, map_one])

end Work.ORLocInd.TF
