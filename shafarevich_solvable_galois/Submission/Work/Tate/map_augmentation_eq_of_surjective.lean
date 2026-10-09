import Mathlib
import Submission.Work.Tate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- A surjective `G`-equivariant additive map `B →+ C` carries the augmentation submodule of `B`
onto the augmentation submodule of `C`.

One inclusion is the general functoriality `map_le_augmentation`; for the converse one lifts a
generator `γ • c - c` of `I_G · C` to `γ • b - b` using `hsurj`, where `c = g b`. -/
theorem map_augmentation_eq_of_surjective {G : Type*} {B : Type*} {C : Type*} [Group G]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G B] [DistribMulAction G C]
    (g : B →+ C) (hg : ∀ (γ : G) (b : B), g (γ • b) = γ • g b)
    (hsurj : Function.Surjective g) :
    (Work.Tate.augmentation G B).map g = Work.Tate.augmentation G C := by
  refine le_antisymm (map_le_augmentation g hg) ?_
  rw [augmentation, AddSubgroup.closure_le]
  rintro _ ⟨⟨γ, c⟩, rfl⟩
  obtain ⟨b, rfl⟩ := hsurj c
  refine AddSubgroup.mem_map.mpr ⟨γ • b - b, smul_sub_self_mem_augmentation γ b, ?_⟩
  rw [map_sub, hg γ b]

end Work.Tate
