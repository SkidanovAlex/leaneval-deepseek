import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarCxEnum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.Qbar

open Work.MbarHomology

theorem cellOf_surjective (e : Fin 865) (k : ℕ)
    (f : {f : QbarCell // f ≤ (⟨e⟩ : QbarCell) ∧ QbarCW.dim f = k}) :
    ∃ i, cellOf e k i = f := by
  have hmem : f.1.idx ∈ dimListLe e k := by
    rw [mem_dimListLe]
    exact ⟨f.2.2, f.2.1⟩
  rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply QbarCell.ext
  simp only [cellOf, hi]

end Work.MbarHomology.Qbar
