import Mathlib

namespace Work.Q44Geom

/-- For a list `l` with `l.length ≤ d`, an existential over the `Fin d`-indices of a predicate applied to `l.getD i a` is equivalent to an existential over the entries of `l`, provided the predicate fails on the default value `a`. -/
theorem exists_fin_getD {α M : Type*} (l : List α) (d : ℕ) (a : α) (g : M → Prop) (q : α → M)
    (hq : ¬ g (q a)) (hd : l.length ≤ d) :
    (∃ i : Fin d, g (q (l.getD (i : ℕ) a))) ↔ ∃ p ∈ l, g (q p) := by
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : (i : ℕ) < l.length
    · exact ⟨l[(i : ℕ)], List.getElem_mem h, by rwa [List.getD_eq_getElem l a h] at hi⟩
    · exfalso
      have hle : l.length ≤ (i : ℕ) := Nat.le_of_not_lt h
      exact hq (by rwa [List.getD_eq_default l a hle] at hi)
  · rintro ⟨p, hp, hgp⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
    exact ⟨⟨j, lt_of_lt_of_le hj hd⟩, by rwa [List.getD_eq_getElem l a hj]⟩

end Work.Q44Geom
