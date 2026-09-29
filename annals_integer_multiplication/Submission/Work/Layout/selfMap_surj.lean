import Mathlib

namespace Work.Layout

/-- A self-map of `{0, …, N-1}` that is injective on that set is surjective onto it:
the image is contained in `Finset.range N` and has the same cardinality. -/
lemma selfMap_surj {N : ℕ} {f : ℕ → ℕ} (hf : ∀ i, i < N → f i < N)
    (hinj : ∀ i, i < N → ∀ i', i' < N → f i = f i' → i = i') :
    ∀ a, a < N → ∃ i, i < N ∧ f i = a := by
  intro a ha
  have hinj' : Function.Injective (fun i : Fin N => (⟨f i, hf i i.isLt⟩ : Fin N)) := by
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    exact Fin.ext (hinj i i.isLt j j.isLt hij)
  have hsurj := Finite.surjective_of_injective hinj'
  obtain ⟨i, hi⟩ := hsurj ⟨a, ha⟩
  exact ⟨i, i.isLt, by simpa using congrArg Fin.val hi⟩

end Work.Layout
