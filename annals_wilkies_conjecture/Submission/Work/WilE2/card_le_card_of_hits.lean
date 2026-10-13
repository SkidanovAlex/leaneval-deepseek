import Mathlib

namespace Work.WilE2

theorem card_le_card_of_hits {k : ℕ} {X : Set (Fin k → ℝ)} {s t : Finset (Fin k → ℝ)}
    (ht : (↑t : Set (Fin k → ℝ)) ⊆ X)
    (hhit : ∀ x ∈ X, ∃ y ∈ t, connectedComponentIn X x = connectedComponentIn X y)
    (hs : (↑s : Set (Fin k → ℝ)) ⊆ X)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      connectedComponentIn X x ≠ connectedComponentIn X y) :
    s.card ≤ t.card := by
  classical
  have _ : (↑t : Set (Fin k → ℝ)) ⊆ X := ht
  -- For each x ∈ s pick a witness y ∈ t lying in the same connected component.
  have hwit : ∀ x ∈ s, ∃ y ∈ t, connectedComponentIn X x = connectedComponentIn X y :=
    fun x hx => hhit x (hs hx)
  let g : s → t := fun x =>
    ⟨Classical.choose (hwit x.1 x.2), (Classical.choose_spec (hwit x.1 x.2)).1⟩
  have hg : ∀ x : s, connectedComponentIn X x.1 = connectedComponentIn X (g x).1 :=
    fun x => (Classical.choose_spec (hwit x.1 x.2)).2
  have hinj : Function.Injective g := by
    intro x y hxy
    by_contra hne
    have hxne : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    have heq : connectedComponentIn X x.1 = connectedComponentIn X y.1 := by
      have h1 : connectedComponentIn X (g x).1 = connectedComponentIn X (g y).1 := by rw [hxy]
      rw [hg x, h1, ← hg y]
    exact hdist x.1 x.2 y.1 y.2 hxne heq
  have hcard := Fintype.card_le_of_injective g hinj
  rwa [Fintype.card_coe s, Fintype.card_coe t] at hcard

end Work.WilE2
