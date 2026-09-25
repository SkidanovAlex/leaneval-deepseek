import Mathlib

namespace Work.Tower.CMAdjoin

theorem isSquare_neg_one_zmod {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 1) :
    IsSquare (-1 : ZMod q) := by
  have : Fact q.Prime := ⟨hq⟩
  exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)

end Work.Tower.CMAdjoin
