import Mathlib

namespace Work.RED

/-- A normal subgroup of cardinality two is contained in the center.

Indeed, `N` has a unique element `a` different from `1`; conjugation by any `g : G`
maps `N` to itself (normality), fixes `1`, and is injective, so it fixes `a`.
Every element of `N` is `1` or `a`, hence central. -/
theorem le_center_of_card_eq_two {G : Type} [Group G] (N : Subgroup G) (hNn : N.Normal)
    (hcard : Nat.card N = 2) : N ≤ Subgroup.center G := by
  -- There is a unique element of `N` different from the identity.
  obtain ⟨a, ha_ne, ha_unique⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hcard
  -- Every element of `N` is `1` or `a`.
  have hdich : ∀ y : N, y = 1 ∨ y = a := fun y =>
    or_iff_not_imp_left.mpr (fun hy => ha_unique y hy)
  -- `a` is central.
  have ha_center : (a : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hb : g * (a : G) * g⁻¹ ∈ N := hNn.conj_mem (a : G) a.2 g
    rcases hdich ⟨g * (a : G) * g⁻¹, hb⟩ with h1 | h2
    · -- the conjugate of `a` cannot be `1`, else `a = 1`
      exfalso
      have hz : g * (a : G) * g⁻¹ = 1 := by
        have := congrArg Subtype.val h1
        simpa using this
      have h1a : (a : G) = 1 := by
        calc (a : G) = g⁻¹ * (g * (a : G) * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hz]
          _ = 1 := by group
      exact ha_ne (Subtype.ext h1a)
    · -- hence the conjugate of `a` equals `a`, so `g` commutes with `a`
      have hz : g * (a : G) * g⁻¹ = (a : G) := by
        have := congrArg Subtype.val h2
        simpa using this
      calc g * (a : G) = (g * (a : G) * g⁻¹) * g := by group
        _ = (a : G) * g := by rw [hz]
  -- Conclude.
  intro n hn
  rcases hdich ⟨n, hn⟩ with h | h
  · have hn1 : n = 1 := by
      have := congrArg Subtype.val h
      simpa using this
    rw [hn1, Subgroup.mem_center_iff]
    intro g
    simp
  · have hna : n = (a : G) := by
      have := congrArg Subtype.val h
      simpa using this
    rw [hna]
    exact ha_center

end Work.RED
