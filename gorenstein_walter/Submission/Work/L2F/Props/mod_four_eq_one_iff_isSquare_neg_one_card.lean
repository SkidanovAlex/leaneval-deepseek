import Mathlib

namespace Work.L2F.Props

/-- In a finite field `F` of odd characteristic with `Nat.card F = q`: `-1` is a square in `F` iff
`q ≡ 1 (mod 4)`, and `q` is odd.  (Mathlib's `FiniteField.isSquare_neg_one_iff` gives
`IsSquare (-1) ↔ Fintype.card F % 4 ≠ 3`, and `FiniteField.odd_card_of_char_ne_two` gives the
oddness, from which the two residue classes `1` and `3` mod `4` are the only options.) -/
theorem mod_four_eq_one_iff_isSquare_neg_one_card (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (q : ℕ) (hq : Nat.card F = q) :
    (q % 4 = 1 ↔ IsSquare (-1 : F)) ∧ Odd q := by
  -- `(2 : F) ≠ 0` means the ring characteristic is not `2`.
  have hchar : ringChar F ≠ 2 := by
    intro h
    have hd : ¬ ringChar F ∣ 2 := fun hd => h2 ((ringChar.spec F 2).2 hd)
    exact hd (h.symm ▸ dvd_rfl)
  -- `Nat.card F = q` is the same as `Fintype.card F = q`.
  have hcard : Fintype.card F = q := by
    rw [← Nat.card_eq_fintype_card]; exact hq
  -- Oddness of the cardinality.
  have hodd : Odd q := by
    have h := FiniteField.odd_card_of_char_ne_two (F := F) hchar
    rw [hcard] at h
    exact Nat.odd_iff.mpr h
  -- `-1` is a square iff the cardinality is not `3` mod `4`.
  have hsq : IsSquare (-1 : F) ↔ q % 4 ≠ 3 := by
    rw [FiniteField.isSquare_neg_one_iff, hcard]
  refine ⟨?_, hodd⟩
  -- For an odd `q`, `q % 4` is `1` or `3`, hence `q % 4 = 1 ↔ q % 4 ≠ 3`.
  obtain ⟨k, rfl⟩ := hodd
  rw [hsq]
  omega

end Work.L2F.Props
