import Mathlib.GroupTheory.Commutator.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Commutator

open scoped commutatorElement

/-- The image of the commutator set under any homomorphism is contained in the commutator set
of the target. -/
theorem image_commutatorSet_subset {G Q : Type*} [Group G] [Group Q] (f : G →* Q) :
    f '' commutatorSet G ⊆ commutatorSet Q := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, b, hab⟩ := hg
  exact ⟨f a, f b, by rw [← map_commutatorElement, hab]⟩

/-- For a surjective homomorphism, the commutator set of the target is the image of the
commutator set of the source. -/
theorem commutatorSet_subset_image {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) : commutatorSet Q ⊆ f '' commutatorSet G := by
  intro q hq
  obtain ⟨y, z, hyz⟩ := hq
  obtain ⟨y', rfl⟩ := hf y
  obtain ⟨z', rfl⟩ := hf z
  exact ⟨⁅y', z'⁆, commutator_mem_commutatorSet y' z', by rw [map_commutatorElement, hyz]⟩

/-- For a surjective homomorphism, `f` maps the commutator set of the source onto the
commutator set of the target. -/
theorem image_commutatorSet_eq {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) : f '' commutatorSet G = commutatorSet Q :=
  Set.Subset.antisymm (image_commutatorSet_subset f) (commutatorSet_subset_image f hf)

/-- The property "every element is a commutator" passes to quotients (images under surjective
homomorphisms). -/
theorem commutatorSet_eq_univ_of_surjective {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (hG : commutatorSet G = Set.univ) :
    commutatorSet Q = Set.univ := by
  rw [← image_commutatorSet_eq f hf, hG, Set.image_univ, Set.range_eq_univ.mpr hf]

end Commons.GroupTheory.Commutator