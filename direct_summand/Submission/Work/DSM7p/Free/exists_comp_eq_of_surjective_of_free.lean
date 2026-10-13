import Mathlib

namespace Work.DSM7p.Free

universe a

/-- A free module is projective: any linear map from a free module into the target of a surjective
linear map lifts along it. -/
theorem exists_comp_eq_of_surjective_of_free {A : Type a} [CommRing A]
    {F : Type a} [AddCommGroup F] [Module A F] [Module.Free A F]
    {M : Type a} [AddCommGroup M] [Module A M] {N : Type a} [AddCommGroup N] [Module A N]
    (p : M →ₗ[A] N) (hp : Function.Surjective p) (f : F →ₗ[A] N) :
    ∃ g : F →ₗ[A] M, p.comp g = f :=
  -- `Module.Free A F` makes `F` projective (`Module.Projective.of_free`), and projective
  -- modules have the lifting property along surjections.
  Module.projective_lifting_property p f hp

end Work.DSM7p.Free
