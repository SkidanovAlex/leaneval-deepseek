import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic

/-!
# Comparing the values of a restricted valuation

For a valuation subring `W` of a field `L` and a ring homomorphism `f : A →+* L` of fields, the
valuation of the pulled-back valuation subring `W.comap f` of `A` computes exactly the valuation of
`W` on the images: `(W.comap f).valuation x ≤ (W.comap f).valuation y ↔ W.valuation (f x) ≤
W.valuation (f y)`.

This is the book-keeping lemma needed to move back and forth between the value groups of a
valuation subring and of its pullback (they are canonically identified, but not defeq).
-/

namespace NK.RingTheory.Valuation

/-- The value comparison of a pulled back valuation subring is the value comparison of the images
under the ring homomorphism. -/
lemma valuation_le_iff_comap_le {A L : Type*} [Field A] [Field L] (W : ValuationSubring L)
    (f : A →+* L) (x y : A) :
    (W.comap f).valuation x ≤ (W.comap f).valuation y ↔ W.valuation (f x) ≤ W.valuation (f y) := by
  rw [ValuationSubring.valuation_le_iff, ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, hay⟩
    exact ⟨⟨f a, a.2⟩, by rw [← map_mul, hay]⟩
  · rintro ⟨b, hb⟩
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero, mul_zero] at hb
      have hx0 : x = 0 := f.injective (by rw [hb.symm, map_zero])
      subst hx0
      exact ⟨0, by simp⟩
    · have hfy : f y ≠ 0 := fun h => hy (f.injective (by rw [h, map_zero]))
      have hbx : f x = (b : L) * f y := hb.symm
      have hb' : f (x / y) = (b : L) := by
        rw [map_div₀, hbx, mul_div_cancel_right₀ _ hfy]
      refine ⟨⟨x / y, ?_⟩, by rw [div_mul_cancel₀ _ hy]⟩
      rw [ValuationSubring.mem_comap, hb']
      exact b.2

/-- Equality of values of a pulled back valuation subring is equivalent to the equality of the
values of the images. -/
lemma valuation_eq_iff_comap_eq {A L : Type*} [Field A] [Field L] (W : ValuationSubring L)
    (f : A →+* L) (x y : A) :
    (W.comap f).valuation x = (W.comap f).valuation y ↔ W.valuation (f x) = W.valuation (f y) :=
  ⟨fun h => le_antisymm ((valuation_le_iff_comap_le W f x y).mp h.le)
      ((valuation_le_iff_comap_le W f y x).mp h.ge),
    fun h => le_antisymm ((valuation_le_iff_comap_le W f x y).mpr h.le)
      ((valuation_le_iff_comap_le W f y x).mpr h.ge)⟩

end NK.RingTheory.Valuation
