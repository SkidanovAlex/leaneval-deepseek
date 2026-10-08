import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

theorem map_centralizer_mulEquiv {A A' : Type*} [Group A] [Group A'] (eA : A ≃* A')
    (P : Subgroup A) :
    (Subgroup.centralizer (P : Set A)).map eA.toMonoidHom
      = Subgroup.centralizer ((P.map eA.toMonoidHom : Subgroup A') : Set A') := by
  -- `eA` is a bijective homomorphism, so it carries the centralizer of `P`
  -- onto the centralizer of the image of `P`.
  ext x
  rw [Subgroup.mem_map]
  constructor
  · -- An element commuting with all of `P` maps to an element commuting with the image.
    rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro p' hp'
    change p' ∈ Subgroup.map eA.toMonoidHom P at hp'
    rw [Subgroup.mem_map] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    simpa using congrArg (eA.toMonoidHom) (hy p hp)
  · -- Conversely, an element commuting with the image is the image of an element of `A`
    -- (namely `eA.symm x`) commuting with all of `P`.
    intro hx
    refine ⟨eA.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    apply eA.injective
    have h : eA.toMonoidHom p * x = x * eA.toMonoidHom p :=
      hx (eA.toMonoidHom p) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa using h

end Work.Hering.AppVII
