import Mathlib

universe u

namespace Work.DSEQ0.FFR

/-- Over a local ring, a finitely generated module of projective dimension `≤ 0`
(equivalently, a finitely generated projective module) is free. -/
theorem free_of_hasProjectiveDimensionLE_zero (R : Type u) [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (h : CategoryTheory.HasProjectiveDimensionLE M 0) :
    Module.Free R M := by
  -- projective dimension `≤ 0` means the object is projective in `ModuleCat R`
  have hP : CategoryTheory.Projective M :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr h
  -- which is exactly `Module.Projective R M`
  have hMP : Module.Projective R M := ModuleCat.projective_of_module_projective M
  -- projective `⟹` flat
  have hF : Module.Flat R M := Module.Flat.of_projective
  -- finitely generated flat over a local ring is free
  exact Module.free_of_flat_of_isLocalRing

end Work.DSEQ0.FFR
