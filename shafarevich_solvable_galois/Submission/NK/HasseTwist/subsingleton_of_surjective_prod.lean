import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HasseTwist

/-- If `S` has cardinality a prime `p`, every `T i` has cardinality at least `p`,
and there is a surjection `S → ∀ i, T i`, then there is at most one index `i`:
otherwise the product `∀ i, T i` contains a factor `T i × T j` with at least
`p * p > p` elements, which cannot be the image of the `p`-element set `S`. -/
theorem subsingleton_of_surjective_prod {ι : Type*} {T : ι → Type*} {S : Type*}
    (p : ℕ) (hp : p.Prime) (hS : Nat.card S = p) (hT : ∀ i, p ≤ Nat.card (T i))
    (f : S → ∀ i, T i) (hf : Function.Surjective f) : ∀ i j : ι, i = j := by
  classical
  have hSpos : 0 < Nat.card S := by rw [hS]; exact hp.pos
  obtain ⟨hNe, hFin⟩ := Nat.card_pos_iff.mp hSpos
  have hNeS : Nonempty S := hNe
  have hFinS : Finite S := hFin
  intro i j
  by_contra hij
  obtain ⟨s0⟩ := hNe
  -- the composite `S → T i × T j` is surjective
  have hsurj : Function.Surjective (fun s : S => (f s i, f s j)) := by
    rintro ⟨a, b⟩
    obtain ⟨s₁, hs₁⟩ := hf (Function.update (f s0) i a)
    have h1 : f s₁ i = a := by rw [hs₁, Function.update_self]
    obtain ⟨s₂, hs₂⟩ := hf (Function.update (f s₁) j b)
    have h2 : f s₂ j = b := by rw [hs₂, Function.update_self]
    have h3 : f s₂ i = f s₁ i := by rw [hs₂, Function.update_of_ne hij]
    exact ⟨s₂, by change (f s₂ i, f s₂ j) = (a, b); rw [h3, h1, h2]⟩
  have hcard : Nat.card (T i × T j) ≤ Nat.card S :=
    Nat.card_le_card_of_surjective (fun s : S => (f s i, f s j)) hsurj
  rw [hS, Nat.card_prod] at hcard
  have hle : p * p ≤ p := (Nat.mul_le_mul (hT i) (hT j)).trans hcard
  have hp1 : p ≤ 1 :=
    Nat.le_of_mul_le_mul_left (a := p) (b := 1) (c := p) (by simpa using hle) hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  omega

end NK.HasseTwist
