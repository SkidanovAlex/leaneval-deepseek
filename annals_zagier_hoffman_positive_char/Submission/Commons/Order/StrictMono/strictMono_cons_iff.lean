import Mathlib.Order.Fin.Tuple

namespace Commons.Order.StrictMono

theorem strictMono_cons_iff {r : ℕ} (d : ℕ) (w : Fin (r + 1) → ℕ) :
    StrictMono (Fin.cons d w) ↔ d < w 0 ∧ StrictMono w := by
  rw [Fin.strictMono_cons]
  constructor
  · rintro ⟨h, hw⟩
    exact ⟨h 0, hw⟩
  · rintro ⟨hd, hw⟩
    exact ⟨fun j => lt_of_lt_of_le hd (hw.monotone (Fin.zero_le j)), hw⟩

end Commons.Order.StrictMono