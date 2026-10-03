import Mathlib

namespace Work.FatouL1

open MeasureTheory

/-- An even function that is integrable on `(0, ∞)` is integrable on all of `ℝ`.

Negation is a measure-preserving involution of `volume` on `ℝ` that exchanges `Ioi 0` and `Iio 0`,
so integrability transfers from `Ioi 0` to `Iio 0` (using evenness to replace `f (-x)` by `f x`).
Adding the null singleton `{0}` gives `IntegrableOn f (Ici 0)`, and `Ici 0 ∪ Iio 0 = univ`. -/
theorem integrable_of_even_of_integrableOn_Ioi {f : ℝ → ℝ} (hf : Function.Even f)
    (h : MeasureTheory.IntegrableOn f (Set.Ioi 0)) : MeasureTheory.Integrable f := by
  -- Negation exchanges the two half-lines, at the level of the restricted measures.
  have h_map_neg :
      (volume.restrict (Set.Ioi (0 : ℝ))).map Neg.neg = volume.restrict (Set.Iio (0 : ℝ)) := by
    conv => rhs; rw [← Measure.map_neg_eq_self volume, measurableEmbedding_neg.restrict_map]
    simp
  -- Integrability on `Iio 0` follows by pulling back along `Neg.neg` and using evenness.
  have hIio : IntegrableOn f (Set.Iio 0) := by
    rw [IntegrableOn, ← h_map_neg, measurableEmbedding_neg.integrable_map_iff]
    exact h.congr (Filter.Eventually.of_forall fun x => (hf x).symm)
  -- `Ici 0` is `Ioi 0` plus the null singleton `{0}`.
  have hIci : IntegrableOn f (Set.Ici 0) := by
    have hset : Set.Ici (0 : ℝ) = Set.Ioi 0 ∪ {0} := by
      ext x
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
      constructor
      · intro hx
        rcases lt_or_eq_of_le hx with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'.symm
      · rintro (h' | rfl)
        · exact le_of_lt h'
        · exact le_rfl
    rw [hset, integrableOn_union]
    exact ⟨h, IntegrableOn.of_measure_zero (by simp)⟩
  -- `Ici 0 ∪ Iio 0 = univ`.
  rw [← integrableOn_univ, ← Set.Ici_union_Iio (a := (0 : ℝ))]
  exact hIci.union hIio

end Work.FatouL1
