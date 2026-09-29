import Mathlib
import Submission.Work.MainP.crtDefs

namespace Work.MainP

theorem invLabLab {S : ℕ} {lab : List ℕ} (hlab : lab.length = S)
    (hinj : ∀ i < S, ∀ j < S, lab.getD i 0 = lab.getD j 0 → i = j)
    {i : ℕ} (hi : i < S) : Work.MainP.invLab lab (lab.getD i 0) = i := by
  have hi' : i < lab.length := by omega
  have hex : ∃ j, j < lab.length ∧ lab.getD j 0 = lab.getD i 0 := ⟨i, hi', rfl⟩
  obtain ⟨hlt, hget⟩ := invLab_spec hex
  have hS : invLab lab (lab.getD i 0) < S := by omega
  exact hinj (invLab lab (lab.getD i 0)) hS i hi hget

end Work.MainP
