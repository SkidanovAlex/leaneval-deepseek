import Mathlib

namespace Work.WilE7

theorem section_eq_snoc {n : ℕ} {C : Set (Fin n → ℝ)} {S : Set (Fin (n + 1) → ℝ)}
    (hS : S ⊆ {z | Fin.init z ∈ C}) {e : OpenPartialHomeomorph C S}
    (hsec : ∀ v ∈ e.source, (⟨Fin.init (e v).1, hS (e v).2⟩ : C) = v)
    {v : C} (hv : v ∈ e.source) :
    (e v).1 = Fin.snoc v.1 ((e v).1 (Fin.last n)) := by
  have h : Fin.init (e v).1 = v.1 := by
    have := congrArg Subtype.val (hsec v hv)
    simpa using this
  rw [← h]
  exact (Fin.snoc_init_self (e v).1).symm

end Work.WilE7
