import Mathlib

namespace Work.L2F.Dihedral

/-- A subgroup `V` with four elements contains an element different from both the
identity and a given element `s ∈ V`.  Pure counting: `{1, s} ⊆ V` has at most two
elements, while `V` has four. -/
theorem exists_ne_one_ne_of_card_four {G : Type*} [Group G] (V : Subgroup G) {s : G}
    (hcard : Nat.card V = 4) (hs : s ∈ V) : ∃ u ∈ V, u ≠ 1 ∧ u ≠ s := by
  classical
  by_contra h
  push Not at h
  -- Every element of `V` is either `1` or `s`.
  have key : ∀ u : V, u = 1 ∨ u = ⟨s, hs⟩ := by
    intro u
    by_cases hu : u = 1
    · exact Or.inl hu
    · exact Or.inr (Subtype.ext (h (u : G) u.2 (fun hc => hu (Subtype.ext hc))))
  -- The map sending `1 ↦ 0` and `s ↦ 1` is well defined on `V`.
  have hf : ∀ u : V, ((if u = 1 then (0 : Fin 2) else 1) = 0) ↔ u = 1 := by
    intro u
    by_cases hu : u = 1
    · simp [hu]
    · simp [hu]
  have hinj : Function.Injective (fun u : V => if u = 1 then (0 : Fin 2) else 1) := by
    intro u v huv
    have h1 : (if u = 1 then (0 : Fin 2) else 1) = (if v = 1 then (0 : Fin 2) else 1) := huv
    have hiff : (u = 1) ↔ (v = 1) := by rw [← hf u, ← hf v, h1]
    by_cases hu : u = 1
    · rw [hu, hiff.mp hu]
    · have hv : v ≠ 1 := fun hvv => hu (hiff.mpr hvv)
      have h1' : u = ⟨s, hs⟩ := (key u).resolve_left hu
      have h2' : v = ⟨s, hs⟩ := (key v).resolve_left hv
      rw [h1', h2']
  have hle := Nat.card_le_card_of_injective (fun u : V => if u = 1 then (0 : Fin 2) else 1) hinj
  rw [hcard, Nat.card_fin] at hle
  omega

end Work.L2F.Dihedral
