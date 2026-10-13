import Mathlib

namespace Work.DSG2

open CategoryTheory AlgebraicGeometry Limits

theorem isSchemeTheoreticallyDominant_lift_qc {X Y : AlgebraicGeometry.Scheme} (i : X ⟶ Y)
    [AlgebraicGeometry.IsSchemeTheoreticallyDominant i] [AlgebraicGeometry.QuasiCompact i]
    (V : Y.Opens) (h : Set.range i ⊆ Set.range V.ι) :
    AlgebraicGeometry.IsSchemeTheoreticallyDominant
      (AlgebraicGeometry.IsOpenImmersion.lift V.ι i h) := by
  have H : IsPullback (IsOpenImmersion.lift V.ι i h) (𝟙 X) V.ι i :=
    IsOpenImmersion.isPullback_lift_id i V.ι h
  rw [← H.isoPullback_hom_fst]
  infer_instance

end Work.DSG2
