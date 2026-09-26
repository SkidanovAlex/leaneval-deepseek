import Mathlib

namespace Work.SG

/-- In a finite type, iterating any endofunction along an orbit must eventually
repeat: there are `a < b` with `F^[a] h = F^[b] h`. This is the pigeonhole
principle applied to the `L + 1` values `F^[0] h, …, F^[L] h` living in the
`L`-element type `Fin L`. -/
theorem RepCoh_orbit {L : ℕ} (F : Fin L → Fin L) (h : Fin L) :
    ∃ a b : ℕ, a < b ∧ F^[a] h = F^[b] h := by
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (L + 1) => F^[i.val] h)
    (by rw [Fintype.card_fin, Fintype.card_fin]; omega)
  rcases lt_or_gt_of_ne (fun hh => hne (Fin.ext hh)) with hlt | hlt
  · exact ⟨x.val, y.val, hlt, heq⟩
  · exact ⟨y.val, x.val, hlt, heq.symm⟩

end Work.SG
