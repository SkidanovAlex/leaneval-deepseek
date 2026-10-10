import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
theorem comp_isOver {X Y Z S : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [X.Over S] [Y.Over S] [Z.Over S] (f : X.PartialMap Y)
    [AlgebraicGeometry.IsDominant f.hom] [f.IsOver S] (g : Y.PartialMap Z) [g.IsOver S] :
    (f.comp g).IsOver S := by
  rw [AlgebraicGeometry.Scheme.PartialMap.isOver_iff]
  have hf : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ X ↘ S := by
    simpa only [AlgebraicGeometry.Scheme.PartialMap.compHom_hom] using
      (AlgebraicGeometry.Scheme.PartialMap.isOver_iff.mp (show f.IsOver S from inferInstance))
  have hg : g.hom ≫ (Z ↘ S) = g.domain.ι ≫ Y ↘ S := by
    simpa only [AlgebraicGeometry.Scheme.PartialMap.compHom_hom] using
      (AlgebraicGeometry.Scheme.PartialMap.isOver_iff.mp (show g.IsOver S from inferInstance))
  show (f.domain.ι.isoImage (f.hom ⁻¹ᵁ g.domain)).inv ≫ f.hom ∣_ g.domain ≫ g.hom ≫ Z ↘ S =
    (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).ι ≫ X ↘ S
  rw [hg, morphismRestrict_ι_assoc, hf, Scheme.Hom.isoImage_inv_ι_assoc]

end Work.Motivic
