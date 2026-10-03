import Mathlib

namespace Work.OROneRel

universe u

/-- If `u = A * of x ^ ε * B` in the free group with `ε = ±1`, then the conjugate
`A⁻¹ * u * B⁻¹` computed in `⟨α | rels⟩` is `of x ^ ε`, and raising it to the power `ε`
recovers the generator `of x`. -/
theorem mk_conj_zpow_of_eq {α : Type u} (rels : Set (FreeGroup α)) {A B u : FreeGroup α} {x : α}
    {ε : ℤ} (hu : u = A * (FreeGroup.of x) ^ ε * B) (hε : ε * ε = 1) :
    ((PresentedGroup.mk rels A)⁻¹ * PresentedGroup.mk rels u * (PresentedGroup.mk rels B)⁻¹) ^ ε
      = PresentedGroup.of x := by
  subst hu
  -- push `mk` inside the free-group word
  rw [map_mul, map_mul, map_zpow]
  -- the conjugate in `⟨α | rels⟩` collapses to `mk (of x) ^ ε`
  have h1 : (PresentedGroup.mk rels A)⁻¹ *
      ((PresentedGroup.mk rels A) * (PresentedGroup.mk rels) (FreeGroup.of x) ^ ε *
        PresentedGroup.mk rels B) * (PresentedGroup.mk rels B)⁻¹
      = ((PresentedGroup.mk rels) (FreeGroup.of x)) ^ ε := by
    group
  -- and then `ε * ε = 1` (so `ε = ±1`) returns the generator
  rw [h1, ← zpow_mul, hε, zpow_one]
  rfl

end Work.OROneRel
