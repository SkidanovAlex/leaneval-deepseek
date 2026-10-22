import Mathlib

namespace Work.ANALYTIC

open CategoryTheory

universe v u

/-- The null-sequence scheme of REFS/03 §1: if precomposition with `T` (resp. `T'`) is bijective on `Hom(-,D)`, and the two towers satisfy the seven identities `h₁`–`h₇`, then precomposition with `g` is bijective on `Hom(-,D)`. Proof: let `eT` be the inverse of precomposition by `T` and `t y := s ≫ eT (G ≫ y)`; then `t` is a two-sided inverse of precomposition by `g` (`h₄`, `h₆`, `h₇` enter through `m ≫ eT z = eT' (m ≫ z)`, which follows from `h₆`). -/
theorem scheme_bijective {C : Type u} [Category.{v} C] {A A' B X D : C}
    (g : B ⟶ X) (F : A ⟶ X) (s : X ⟶ A) (G : A ⟶ B) (T : A ⟶ A)
    (F' : A' ⟶ B) (s' : B ⟶ A') (T' : A' ⟶ A') (m : A' ⟶ A)
    (h₁ : T ≫ F = G ≫ g) (h₂ : s ≫ F = 𝟙 X) (h₃ : m ≫ F = F' ≫ g)
    (h₄ : m ≫ G = T' ≫ F') (h₅ : g ≫ s = s' ≫ m) (h₆ : m ≫ T = T' ≫ m)
    (h₇ : s' ≫ F' = 𝟙 B)
    (hT : Function.Bijective (fun h : A ⟶ D => T ≫ h))
    (hT' : Function.Bijective (fun h : A' ⟶ D => T' ≫ h)) :
    Function.Bijective (fun h : X ⟶ D => g ≫ h) := by
  classical
  -- `eT` is a left inverse of precomposition by `T` on `Hom(-,D)`.
  let eT : (A ⟶ D) → (A ⟶ D) := fun z => Classical.choose (hT.2 z)
  have hTA : ∀ z : A ⟶ D, T ≫ eT z = z := fun z => Classical.choose_spec (hT.2 z)
  have hTAinv : ∀ w : A ⟶ D, eT (T ≫ w) = w := by
    intro w
    have hw : T ≫ eT (T ≫ w) = T ≫ w := by rw [hTA]
    exact hT.1 hw
  -- `eT'` is a left inverse of precomposition by `T'` on `Hom(-,D)`.
  let eT' : (A' ⟶ D) → (A' ⟶ D) := fun z => Classical.choose (hT'.2 z)
  have hT'A : ∀ z : A' ⟶ D, T' ≫ eT' z = z := fun z => Classical.choose_spec (hT'.2 z)
  have hT'Ainv : ∀ w : A' ⟶ D, eT' (T' ≫ w) = w := by
    intro w
    have hw : T' ≫ eT' (T' ≫ w) = T' ≫ w := by rw [hT'A]
    exact hT'.1 hw
  -- `h₆` makes `m` compatible with the two inverses `eT`, `eT'`.
  have key : ∀ z : A ⟶ D, m ≫ eT z = eT' (m ≫ z) := by
    intro z
    have h : T' ≫ (m ≫ eT z) = m ≫ z := by
      rw [← Category.assoc, ← h₆, Category.assoc, hTA]
    rw [← h, hT'Ainv]
  -- `t y := s ≫ eT (G ≫ y)` is a left inverse of precomposition by `g` …
  have hleft : ∀ y : X ⟶ D, s ≫ eT (G ≫ (g ≫ y)) = y := by
    intro y
    have hG : G ≫ (g ≫ y) = T ≫ (F ≫ y) := by
      rw [← Category.assoc, ← h₁, Category.assoc]
    rw [hG, hTAinv, ← Category.assoc, h₂, Category.id_comp]
  -- … and a right inverse.
  have hright : ∀ y : B ⟶ D, g ≫ (s ≫ eT (G ≫ y)) = y := by
    intro y
    rw [← Category.assoc, h₅, Category.assoc, key, ← Category.assoc, h₄, Category.assoc,
      hT'Ainv, ← Category.assoc, h₇, Category.id_comp]
  constructor
  · intro y₁ y₂ hy
    have hy' : g ≫ y₁ = g ≫ y₂ := hy
    rw [← hleft y₁, ← hleft y₂, hy']
  · intro y
    exact ⟨s ≫ eT (G ≫ y), hright y⟩

end Work.ANALYTIC
