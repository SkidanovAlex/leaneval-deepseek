import Mathlib
import Submission.Work.Drive.even_ncard_of_involution

namespace Work.Drive

/-- **An involution swapping a finite set between two parts pairs the parts.**

If `P` is an involution of a finite set `s`, and `s` splits as a disjoint union `s₀ ∪ s₁`
with `P` mapping `s₀` into `s₁` and `s₁` into `s₀`, then `s₀` and `s₁` have the same
cardinality: `P` restricts to a bijection `s₀ ≃ s₁`. -/
theorem ncard_eq_of_involution_swap {α : Type*} {s : Set α} (hs : s.Finite) (P : α → α)
    (hmaps : ∀ x ∈ s, P x ∈ s) (hPinv : ∀ x ∈ s, P (P x) = x)
    {s₀ s₁ : Set α} (hdisj : Disjoint s₀ s₁) (hunion : s₀ ∪ s₁ = s)
    (hswap₀ : ∀ x ∈ s₀, P x ∈ s₁) (hswap₁ : ∀ x ∈ s₁, P x ∈ s₀) :
    s₀.ncard = s₁.ncard := by
  -- both parts lie in `s`, so the involution identity is available on them
  have hs₀ : s₀ ⊆ s := by rw [← hunion]; exact Set.subset_union_left
  have hs₁ : s₁ ⊆ s := by rw [← hunion]; exact Set.subset_union_right
  -- `P` restricts to a bijection `s₀ → s₁`
  refine Set.ncard_congr (fun x _ => P x) (fun x hx => hswap₀ x hx) ?_ ?_
  · -- injective, using that `P` is an involution on `s`
    intro x y hx hy hxy
    calc x = P (P x) := (hPinv x (hs₀ hx)).symm
      _ = P (P y) := by rw [hxy]
      _ = y := hPinv y (hs₀ hy)
  · -- surjective, since `y = P (P y)` and `P y ∈ s₀` for `y ∈ s₁`
    intro y hy
    exact ⟨P y, hswap₁ y hy, hPinv y (hs₁ hy)⟩

end Work.Drive
