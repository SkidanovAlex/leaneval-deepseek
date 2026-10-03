import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

/-- A group homomorphism `f` carrying `N` and `t` to `N.map f` and `f t` preserves `TwistData`,
provided it is injective (injectivity is needed for the infinite-order condition: without it
`N.map f` can be trivial even though `t` has infinite order modulo `N`). -/
theorem P311.TwistData.map {G K : Type*} [Group G] [Group K] {N : Subgroup G} {t : G}
    (f : G →* K) (hf : Function.Injective f) (h : P311.TwistData N t) :
    P311.TwistData (N.map f) (f t) where
  conj x hx := by
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨t * b * t⁻¹, h.conj b hb, ?_⟩
    simp [map_mul, map_inv]
  conj_inv x hx := by
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨t⁻¹ * b * t, h.conj_inv b hb, ?_⟩
    simp [map_mul, map_inv]
  inf k hk := by
    rw [Subgroup.mem_map] at hk
    obtain ⟨b, hb, hbk⟩ := hk
    rw [← map_zpow] at hbk
    have hbt : b = t ^ k := hf hbk
    rw [hbt] at hb
    exact h.inf k hb

theorem twistData_map {G : Type*} [Group G] (H : Subgroup G) (H₀ : Subgroup ↥H) (N : Subgroup H₀) (hN : N.Normal) (t : H₀) (htinf : ∀ k : ℤ, t ^ k ∈ N → k = 0) : Work.ORP311.P311.TwistData ((N.map H₀.subtype).map H.subtype) ((t : H₀) : G) := by
  have h : P311.TwistData N t :=
    { conj := fun x hx => hN.conj_mem x hx t
      conj_inv := fun x hx => by simpa using hN.conj_mem x hx t⁻¹
      inf := htinf }
  exact ((h.map H₀.subtype (Subgroup.subtype_injective H₀)).map H.subtype
    (Subgroup.subtype_injective H))

end Work.ORP311
