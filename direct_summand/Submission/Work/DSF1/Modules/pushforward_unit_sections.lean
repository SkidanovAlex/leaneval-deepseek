import Mathlib

namespace Work.DSF1.Modules

theorem pushforward_unit_sections (X : AlgebraicGeometry.Scheme) (U V : X.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward U.ι).obj
        (SheafOfModules.unit U.toScheme.ringCatSheaf)).presheaf.obj (Opposite.op V)
      = AddCommGrpCat.of (X.presheaf.obj (Opposite.op (U ⊓ V))) := by
  have h := AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj U.ι
    (SheafOfModules.unit U.toScheme.ringCatSheaf) V
  rw [h]
  rw [show (AlgebraicGeometry.Scheme.Modules.presheaf
      (SheafOfModules.unit U.toScheme.ringCatSheaf)).obj
        (Opposite.op ((TopologicalSpace.Opens.map U.ι.base).obj V))
      = AddCommGrpCat.of (U.toScheme.presheaf.obj
        (Opposite.op ((TopologicalSpace.Opens.map U.ι.base).obj V))) from rfl]
  rw [AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_obj]
  rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι]

end Work.DSF1.Modules
