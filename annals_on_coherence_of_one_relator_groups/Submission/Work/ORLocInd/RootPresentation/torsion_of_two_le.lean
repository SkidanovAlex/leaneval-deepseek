import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.RootPresentation

/-- If a root presentation `⟨X | u ^ l⟩` has `l ≥ 2` and the root has a nontrivial image `u ≠ 1`
in `G`, then `G` is not torsion-free: `u` is a nontrivial element of finite order (its `l`-th
power is the defining relator, hence trivial in `G`). -/
theorem torsion_of_two_le {G : Type*} [Group G] (P : Work.ORLocInd.RootPresentation G)
    (hl : 2 ≤ P.l) (hu : P.rootElem ≠ 1) : ¬ Work.ORLocInd.IsTorsionFree G := by
  intro h
  have hfin : IsOfFinOrder P.rootElem :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨P.l, by omega, P.rootElem_pow⟩
  exact hu (h P.rootElem hfin)

end Work.ORLocInd.RootPresentation
