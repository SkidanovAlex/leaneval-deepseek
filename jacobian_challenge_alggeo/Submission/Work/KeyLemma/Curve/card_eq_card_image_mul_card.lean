import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.KeyLemma.Curve

/-- If `ρ` is constant exactly on the left cosets of a subgroup `H` (i.e.
`ρ a = ρ b ↔ a⁻¹ * b ∈ H`) and `X` is closed under right multiplication by `H`,
then `X` is a union of left cosets of `H`, each of which has `Nat.card H` elements,
and `Nat.card X = Nat.card (ρ '' X) * Nat.card H`. -/
theorem card_eq_card_image_mul_card {G β : Type*} [Group G] [Finite G]
    (H : Subgroup G) (ρ : G → β) (hρ : ∀ a b, ρ a = ρ b ↔ a⁻¹ * b ∈ H)
    (X : Set G) (hX : ∀ g ∈ X, ∀ h ∈ H, g * h ∈ X) :
    Nat.card X = Nat.card (ρ '' X) * Nat.card H := by
  classical
  -- `ρ` is invariant under right multiplication by `H`
  have hρmul : ∀ (g : G) (h : H), ρ (g * (h : G)) = ρ g := by
    intro g h
    exact ((hρ g (g * (h : G))).mpr (by simp)).symm
  -- choose a representative in `X` for every value in `ρ '' X`
  have rep_exists : ∀ y : ↥(ρ '' X), ∃ g, g ∈ X ∧ ρ g = y.val := by
    rintro ⟨yval, hy⟩
    rw [Set.mem_image] at hy
    exact hy
  let rep : ↥(ρ '' X) → G := fun y => Classical.choose (rep_exists y)
  have rep_mem : ∀ y, rep y ∈ X := fun y => (Classical.choose_spec (rep_exists y)).1
  have rep_eq : ∀ y, ρ (rep y) = y.val := fun y => (Classical.choose_spec (rep_exists y)).2
  -- the bijection `(ρ '' X) × H → X`, `(y, h) ↦ rep y * h`
  let f : ↥(ρ '' X) × ↥H → ↥X := fun p => ⟨rep p.1 * (p.2 : G), hX _ (rep_mem p.1) _ p.2.2⟩
  have finj : Function.Injective f := by
    rintro ⟨y, h⟩ ⟨y', h'⟩ heq
    have hv : rep y * (h : G) = rep y' * (h' : G) := by
      have := congrArg Subtype.val heq
      simpa [f] using this
    have hyy : y = y' := by
      apply Subtype.ext
      have h1 : ρ (rep y * (h : G)) = ρ (rep y' * (h' : G)) := by rw [hv]
      rw [hρmul (rep y) h, hρmul (rep y') h'] at h1
      exact (rep_eq y).symm.trans (h1.trans (rep_eq y'))
    have hrep : rep y = rep y' := congrArg rep hyy
    have hhh : (h : G) = (h' : G) := by
      have h2 : rep y * (h : G) = rep y * (h' : G) := by
        calc rep y * (h : G) = rep y' * (h' : G) := hv
          _ = rep y * (h' : G) := by rw [← hrep]
      exact mul_left_cancel h2
    exact Prod.ext hyy (Subtype.ext hhh)
  have fsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    let y0 : ↥(ρ '' X) := ⟨ρ x, ⟨x, hx, rfl⟩⟩
    have hmem : (rep y0)⁻¹ * x ∈ H := (hρ (rep y0) x).mp (rep_eq y0)
    refine ⟨(y0, ⟨(rep y0)⁻¹ * x, hmem⟩), ?_⟩
    apply Subtype.ext
    dsimp only [f, y0]
    rw [mul_inv_cancel_left]
  let e : ↥(ρ '' X) × ↥H ≃ ↥X := Equiv.ofBijective f ⟨finj, fsurj⟩
  calc Nat.card X = Nat.card (↥(ρ '' X) × ↥H) := (Nat.card_congr e).symm
    _ = Nat.card (ρ '' X) * Nat.card H := Nat.card_prod _ _

end Work.KeyLemma.Curve
