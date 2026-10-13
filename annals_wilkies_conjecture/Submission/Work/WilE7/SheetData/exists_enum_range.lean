import Mathlib

namespace Work.WilE7.SheetData

/-- The distinct values of a real-valued function on a finite type can be enumerated in strictly
increasing order, with a representative of each value: there are `K : ℕ` (the number of distinct
values), an order embedding `e : Fin K ↪o ℝ` (so `e` is strictly increasing) and a representative
map `rep : Fin K → ι` with `e i = f (rep i)`, the range of `e` being exactly the range of `f`, and
`K ≤ Fintype.card ι`. -/
theorem exists_enum_range {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ (K : ℕ) (e : Fin K ↪o ℝ) (rep : Fin K → ι),
      K ≤ Fintype.card ι ∧
      (∀ i : Fin K, e i = f (rep i)) ∧
      (∀ a : ι, ∃ i : Fin K, e i = f a) := by
  classical
  let s : Finset ℝ := Finset.image f Finset.univ
  have hcard : s.card ≤ Fintype.card ι := by
    calc s.card = (Finset.image f (Finset.univ : Finset ι)).card := rfl
      _ ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
      _ = Fintype.card ι := Finset.card_univ
  refine ⟨s.card, s.orderEmbOfFin rfl,
    fun i => (Finset.mem_image.mp (Finset.orderEmbOfFin_mem s rfl i)).choose,
    hcard, ?_, ?_⟩
  · intro i
    exact ((Finset.mem_image.mp (Finset.orderEmbOfFin_mem s rfl i)).choose_spec).2.symm
  · intro a
    have ha : f a ∈ (↑s : Set ℝ) := by
      rw [Finset.mem_coe]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    rw [← Finset.range_orderEmbOfFin s rfl] at ha
    exact Set.mem_range.mp ha

end Work.WilE7.SheetData
