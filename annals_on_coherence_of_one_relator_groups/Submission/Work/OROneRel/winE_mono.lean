import Mathlib
import Submission.Work.OROneRel.winBasisDefs

namespace Work.OROneRel

theorem winE_mono {α : Type*} (c : α → ℤ) {lo hi lo' hi' : ℤ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    Work.OROneRel.winE c lo hi ⊆ Work.OROneRel.winE c lo' hi' := by
  intro e he
  rw [mem_winE] at he ⊢
  exact ⟨hlo.trans he.1, he.2.1.trans hhi, hlo.trans he.2.2.1, he.2.2.2.trans hhi⟩

end Work.OROneRel
