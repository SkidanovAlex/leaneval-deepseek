import Mathlib

namespace Work.WilE9G.Sard

/-- **Lindelöf property of `ℝⁿ`.**  Any open cover of a subset of `ℝⁿ` indexed by its own points
admits a countable subcover.

`ℝⁿ = Fin n → ℝ` is second countable (a countable product of second countable spaces), hence
hereditarily Lindelöf: every subset is Lindelöf.  Applying the countable-subcover form of
Lindelöfness to the open cover `F` of `S` yields the result. -/
theorem exists_countable_subcover {n : ℕ} {S : Set (Fin n → ℝ)}
    (F : (Fin n → ℝ) → Set (Fin n → ℝ)) (hopen : ∀ x, IsOpen (F x))
    (hmem : ∀ x ∈ S, x ∈ F x) :
    ∃ T : Set (Fin n → ℝ), T.Countable ∧ S ⊆ ⋃ x ∈ T, F x :=
  (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover F hopen
    (fun x hx => Set.mem_iUnion.2 ⟨x, hmem x hx⟩)

end Work.WilE9G.Sard
