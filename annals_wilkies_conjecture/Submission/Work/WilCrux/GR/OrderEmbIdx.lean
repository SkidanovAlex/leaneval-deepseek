import Mathlib

namespace Work.WilCrux.GR

theorem OrderEmbIdx {α : Type*} [LinearOrder α] (S : Finset α) {k : ℕ}
    (h : S.card = k) (i : Fin k) {j : α} (hj : j ∈ S) :
    S.orderEmbOfFin h i = j ↔ (i : ℕ) = (S.filter (fun x => x < j)).card := by
  classical
  -- For every index `i`, the number of elements of `S` below the `i`-th one is exactly `i`.
  have key : ∀ i : Fin k, (S.filter (fun x => x < S.orderEmbOfFin h i)).card = (i : ℕ) := by
    intro i
    have h1 : (Finset.map (S.orderEmbOfFin h).toEmbedding Finset.univ).filter
          (fun x => x < S.orderEmbOfFin h i)
        = S.filter (fun x => x < S.orderEmbOfFin h i) := by
      rw [Finset.map_orderEmbOfFin_univ S h]
    rw [← h1, Finset.filter_map, Finset.card_map]
    simp only [Function.comp_apply, RelEmbedding.coe_toEmbedding]
    have hcongr : Finset.univ.filter (fun a : Fin k => S.orderEmbOfFin h a < S.orderEmbOfFin h i)
        = Finset.univ.filter (fun a : Fin k => a < i) := by
      apply Finset.filter_congr
      intro a _
      exact (S.orderEmbOfFin h).lt_iff_lt
    rw [hcongr]
    have hIio : (Finset.univ.filter (fun a : Fin k => a < i)) = Finset.Iio i := by
      ext t; simp [Finset.mem_Iio]
    rw [hIio, Fin.card_Iio]
  obtain ⟨i₀, hi₀⟩ := Set.mem_range.mp (by rw [Finset.range_orderEmbOfFin S h]; exact hj)
  have hc : (S.filter (fun x => x < j)).card = (i₀ : ℕ) := by
    rw [← hi₀]; exact key i₀
  constructor
  · intro heq
    have : i = i₀ := (S.orderEmbOfFin h).injective (heq.trans hi₀.symm)
    rw [this, hc]
  · intro heq
    have : i = i₀ := Fin.ext (by rw [heq, hc])
    rw [this, hi₀]

end Work.WilCrux.GR
