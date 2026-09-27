import Mathlib

namespace Work.Mostow

/-- Counting lemma: if a subgroup `B` is covered by the right `A`-cosets attached to a finite
set `s` (i.e. every `x ∈ B` lies in `A * {y}` for some `y ∈ s`), then `B` is dominated by
`|s| * |A|`.  A finite union of `|s|` sets each of cardinality `|A|`. -/
theorem cardTransversal {G : Type*} [Group G] (B A : Subgroup G) (s : Finset G) [Finite A]
    (h : ∀ x ∈ B, ∃ y ∈ s, x * y⁻¹ ∈ A) : Nat.card B ≤ s.card * Nat.card A := by
  classical
  -- Map each `x ∈ B` to a chosen `y ∈ s` together with `x * y⁻¹ ∈ A`.
  let f : B → ↥(s : Set G) × A := fun x =>
    (⟨Classical.choose (h x.1 x.2), (Classical.choose_spec (h x.1 x.2)).1⟩,
     ⟨x.1 * (Classical.choose (h x.1 x.2))⁻¹, (Classical.choose_spec (h x.1 x.2)).2⟩)
  have hf : Function.Injective f := by
    intro x x' hxx
    have h1 : Classical.choose (h x.1 x.2) = Classical.choose (h x'.1 x'.2) :=
      Subtype.ext_iff.mp (Prod.ext_iff.mp hxx).1
    have h2 : x.1 * (Classical.choose (h x.1 x.2))⁻¹ = x'.1 * (Classical.choose (h x'.1 x'.2))⁻¹ :=
      Subtype.ext_iff.mp (Prod.ext_iff.mp hxx).2
    apply Subtype.ext
    have hx : x.1 = (x.1 * (Classical.choose (h x.1 x.2))⁻¹) * Classical.choose (h x.1 x.2) := by
      group
    have hx' : x'.1 = (x'.1 * (Classical.choose (h x'.1 x'.2))⁻¹) * Classical.choose (h x'.1 x'.2) := by
      group
    rw [hx, hx', h2, h1]
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  have hs : Nat.card ↥(s : Set G) = s.card := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_coe s
  rw [hs] at hcard
  exact hcard

end Work.Mostow
