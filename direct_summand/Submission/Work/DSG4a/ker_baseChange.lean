import Mathlib

namespace Work.DSG4a

theorem ker_baseChange {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (hflat : Module.Flat A A')
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    (LinearMap.ker f).baseChange A' = (f.baseChange A').ker := by
  -- Tensoring the exact sequence `0 → ker f → M → N` with the flat `A`-algebra `A'`
  -- preserves exactness, which is precisely the statement that the base change of the
  -- kernel is the kernel of the base change.
  have : Module.Flat A A' := hflat
  exact (Module.Flat.ker_lTensor_eq (R := A) (S := A') (M := A') f).symm

end Work.DSG4a
