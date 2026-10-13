import Mathlib
import Submission.Work.WilC4.monoDefs

namespace Work.WilC4

/-- If every point of the open interval `(a,b)` is a point at which the partial function described
by `Y` is locally constant, then the partial function is nondecreasing on `(a,b)`.

The point is that local constancy is inherited to every point of `(a,b)` (each of them lies in
`MonoW`), so the value of the partial function is a locally constant function on the preconnected
space `(a,b)`; it is therefore constant, and all values carried by `Y` on `(a,b)` coincide. -/
theorem germ_const_of_W {Y : Set (Fin 2 → ℝ)} {a b : ℝ}
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hW : Set.Ioo a b ⊆ MonoW Y) : MonoIncOn Y a b := by
  intro x₁ x₂ y₁ y₂ hx₁ hx₁₂ hx₂ hy₁ hy₂
  have hpre : IsPreconnected (Set.univ : Set ↥(Set.Ioo a b)) :=
    (Subtype.preconnectedSpace isPreconnected_Ioo).isPreconnected_univ
  -- the value of the partial function at a point of `(a,b)`
  let yv : ↥(Set.Ioo a b) → ℝ := fun x => Classical.choose (hW x.2)
  -- `yv x` is indeed a value carried by `Y` at `x`
  have hspec : ∀ x : ↥(Set.Ioo a b), ![x.1, yv x] ∈ Y := fun x =>
    (Classical.choose_spec (Classical.choose_spec (hW x.2))).2.1
  -- a whole neighbourhood of `x` carries the value `yv x`
  have hnb : ∀ x : ↥(Set.Ioo a b), ∃ ε > 0,
      ∀ z : ℝ, x.1 - ε < z → z < x.1 + ε → ![z, yv x] ∈ Y := by
    intro x
    obtain ⟨ε, hε, _, hnl⟩ := Classical.choose_spec (hW x.2)
    exact ⟨ε, hε, hnl⟩
  -- hence `yv` is locally constant
  have hloc : IsLocallyConstant yv := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨ε, hε, hnl⟩ := hnb x
    refine ⟨{x' : ↥(Set.Ioo a b) | (x'.1 : ℝ) ∈ Set.Ioo (x.1 - ε) (x.1 + ε)},
      isOpen_Ioo.preimage continuous_subtype_val,
      ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩, ?_⟩
    intro x' hx'
    exact hfun x'.1 (yv x') (yv x) (hspec x') (hnl x'.1 hx'.1 hx'.2)
  -- and `(a,b)` is preconnected, so `yv` is constant
  have hX₁ : x₁ ∈ Set.Ioo a b := ⟨hx₁, lt_trans hx₁₂ hx₂⟩
  have hX₂ : x₂ ∈ Set.Ioo a b := ⟨lt_trans hx₁ hx₁₂, hx₂⟩
  have heq : yv ⟨x₁, hX₁⟩ = yv ⟨x₂, hX₂⟩ :=
    hloc.apply_eq_of_isPreconnected hpre trivial trivial
  have e₁ : y₁ = yv ⟨x₁, hX₁⟩ := hfun x₁ y₁ (yv ⟨x₁, hX₁⟩) hy₁ (hspec ⟨x₁, hX₁⟩)
  have e₂ : y₂ = yv ⟨x₂, hX₂⟩ := hfun x₂ y₂ (yv ⟨x₂, hX₂⟩) hy₂ (hspec ⟨x₂, hX₂⟩)
  linarith

end Work.WilC4
