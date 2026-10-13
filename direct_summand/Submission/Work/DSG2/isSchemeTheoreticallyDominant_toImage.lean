import Mathlib

namespace Work.DSG2

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- The canonical morphism `f.toImage : X ⟶ f.image` to the scheme-theoretic image of a
quasi-compact morphism `f` is scheme-theoretically dominant: its kernel ideal sheaf is trivial.

This is the general fact that an ideal sheaf `I` on a scheme `Y` is the kernel of the canonical
map `I.subschemeι : I.subscheme ⟶ Y`, applied to `I = f.ker`; equivalently, a section of an affine
open of `f.image` which vanishes after pulling back to `X` must already be zero, since
`f.toImage` is injective on stalks. -/
theorem isSchemeTheoreticallyDominant_toImage {X Y : AlgebraicGeometry.Scheme}
    (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsSchemeTheoreticallyDominant f.toImage := by
  refine ⟨?_⟩
  apply le_antisymm _ bot_le
  rw [Scheme.IdealSheafData.le_def]
  intro U
  -- `f.toImage` is injective on the stalks of `f.image` (`Scheme.Hom.stalkFunctor_toImage_injective`),
  -- hence injective on sections over every open, in particular over the affine open `U`.
  have hinj : Function.Injective
      ⇑(ConcreteCategory.hom ((f.toImage).c.app (op (U : (f.image).Opens)))) :=
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := (f.image).sheaf)
      (f := (f.toImage).c) (U : (f.image).Opens)
      (fun x _ => Scheme.Hom.stalkFunctor_toImage_injective f x)
  have hinj' : Function.Injective ((f.toImage).app (U : (f.image).Opens)).hom := hinj
  rw [Scheme.Hom.ker_apply f.toImage U]
  exact le_bot_iff.mpr ((RingHom.injective_iff_ker_eq_bot _).mp hinj')

end Work.DSG2
