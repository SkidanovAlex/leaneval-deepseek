import Mathlib

namespace Work.WilG4c

theorem card_countvec_le (n r : ℕ) :
    Fintype.card {c : Fin n → Fin (r + 1) //
      (Finset.univ.sum (fun i : Fin n => (c i : ℕ))) ≤ r} ≤ (r + 1) ^ n := by
  calc Fintype.card {c : Fin n → Fin (r + 1) //
        (Finset.univ.sum (fun i : Fin n => (c i : ℕ))) ≤ r}
      ≤ Fintype.card (Fin n → Fin (r + 1)) :=
        Fintype.card_subtype_le _
    _ = (r + 1) ^ n := by simp

end Work.WilG4c
