import Mathlib.Algebra.Homology.Opposite
import Mathlib.Combinatorics.Quiver.ReflQuiver

namespace Commons.Algebra.Homology

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
theorem homologyUnop_hom_naturality {V : Type*} [Category* V] {ι : Type*} {c : ComplexShape ι}
    [Preadditive V] [CategoryWithHomology V] {K L : HomologicalComplex Vᵒᵖ c} (ψ : K ⟶ L)
    (i : ι) [K.HasHomology i] [L.HasHomology i] :
    (HomologicalComplex.homologyUnop L i).hom ≫ (HomologicalComplex.homologyMap ψ i).unop ≫
        (HomologicalComplex.homologyUnop K i).inv =
      HomologicalComplex.homologyMap ((HomologicalComplex.unopFunctor V c).map ψ.op) i := by
  apply Quiver.Hom.op_inj
  simp only [HomologicalComplex.homologyUnop, HomologicalComplex.homologyOp,
    HomologicalComplex.homologyMap]
  simp only [op_comp, Iso.unop_hom, Iso.unop_inv, Quiver.Hom.op_unop]
  have h : ShortComplex.opMap ((HomologicalComplex.shortComplexFunctor V c.symm i).map
        ((HomologicalComplex.unopFunctor V c).map ψ.op)) =
      (HomologicalComplex.shortComplexFunctor Vᵒᵖ c i).map ψ := by
    ext <;> simp only [ShortComplex.opMap_τ₁, ShortComplex.opMap_τ₂, ShortComplex.opMap_τ₃,
      HomologicalComplex.shortComplexFunctor_map_τ₁,
      HomologicalComplex.shortComplexFunctor_map_τ₂,
      HomologicalComplex.shortComplexFunctor_map_τ₃]
    all_goals rfl
  rw [← h]
  rw [ShortComplex.homologyMap_op]
  rw [Category.assoc]
  rfl

end Commons.Algebra.Homology