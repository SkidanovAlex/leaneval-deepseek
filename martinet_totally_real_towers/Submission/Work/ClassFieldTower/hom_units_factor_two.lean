import Mathlib

namespace Work.ClassFieldTower

/-- If `A` is a group of exponent dividing `2` (every element squares to `1`), then every monoid
homomorphism `A →* Rˣ` into the units of a field lands in the subgroup `rootsOfUnity 2 R` of
elements of order dividing `2`, and conversely.  Since the inclusion of that subgroup into `Rˣ` is
injective, restriction of the codomain is a bijection on hom-monoids, i.e. a monoid isomorphism. -/
theorem hom_units_factor_two {A R : Type*} [Group A] [Field R] (h : ∀ x : A, x ^ 2 = 1) :
    Nonempty ((A →* Rˣ) ≃* (A →* rootsOfUnity 2 R)) := by
  -- every value of a homomorphism out of `A` is a square root of `1`
  have key : ∀ (f : A →* Rˣ), ∀ x : A, f x ∈ rootsOfUnity 2 R := by
    intro f x
    rw [mem_rootsOfUnity, ← map_pow, h x, map_one]
  -- the postcomposition map with the inclusion `rootsOfUnity 2 R → Rˣ`
  let ψ : (A →* rootsOfUnity 2 R) →* (A →* Rˣ) :=
    MonoidHom.compHom (rootsOfUnity 2 R).subtype
  have hψ : ∀ (g : A →* rootsOfUnity 2 R),
      (ψ g : A →* Rˣ) = (rootsOfUnity 2 R).subtype.comp g := fun g => rfl
  have hinj : Function.Injective ψ := by
    intro g₁ g₂ hg
    apply MonoidHom.ext; intro a
    apply Subtype.ext
    have h2 : (ψ g₁) a = (ψ g₂) a := congrArg (fun k : A →* Rˣ => k a) hg
    simp only [hψ, MonoidHom.comp_apply] at h2
    simpa using h2
  have hsurj : Function.Surjective ψ := by
    intro f
    refine ⟨f.codRestrict (rootsOfUnity 2 R) (key f), ?_⟩
    apply MonoidHom.ext; intro x
    rw [hψ]
    simp [MonoidHom.codRestrict_apply]
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

end Work.ClassFieldTower
