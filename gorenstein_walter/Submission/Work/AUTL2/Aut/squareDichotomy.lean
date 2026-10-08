import Mathlib

namespace Work.AUTL2.Aut

/-- In a finite field `F` of odd characteristic, multiplication by a fixed non-square `d`
sends every element either into the squares itself or into the squares after multiplying by `d`:
for every `δ` either `δ` or `δ * d` is a square. -/
theorem squareDichotomy (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (d : F) (hd : ¬ IsSquare d) : ∀ δ : F, IsSquare δ ∨ IsSquare (δ * d) := by
  -- `0` is a square, so a non-square is nonzero.
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd ⟨0, by ring⟩
  intro δ
  rcases eq_or_ne δ 0 with rfl | hδ
  · exact Or.inl ⟨0, by ring⟩
  · -- In odd characteristic, `x ^ (#F / 2)` is `1` for squares and `-1` for non-squares.
    rcases FiniteField.pow_dichotomy hF hδ with h | h
    · exact Or.inl ((FiniteField.isSquare_iff hF hδ).mpr h)
    · right
      have hdne : d ^ (Fintype.card F / 2) = -1 := by
        rcases FiniteField.pow_dichotomy hF hd0 with h' | h'
        · exact absurd ((FiniteField.isSquare_iff hF hd0).mpr h') hd
        · exact h'
      have hpow : (δ * d) ^ (Fintype.card F / 2) = 1 := by
        rw [mul_pow, h, hdne]
        ring
      exact (FiniteField.isSquare_iff hF (mul_ne_zero hδ hd0)).mpr hpow

end Work.AUTL2.Aut
