import Mathlib

namespace Work.Holonomy3

theorem card_filter_add_card_filter_le {n : ℕ} {p q : Fin n → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ i, p i → ¬ q i) :
    (Finset.univ.filter p).card + (Finset.univ.filter q).card ≤ n := by
  have hsub : Finset.univ.filter q ⊆ Finset.univ.filter (fun i => ¬ p i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun hp => h i hp hi
  have hcard : (Finset.univ.filter q).card ≤ (Finset.univ.filter (fun i => ¬ p i)).card :=
    Finset.card_le_card hsub
  have hnot : (Finset.univ.filter p).card + (Finset.univ.filter (fun i => ¬ p i)).card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) p
    simpa using this
  omega

end Work.Holonomy3
