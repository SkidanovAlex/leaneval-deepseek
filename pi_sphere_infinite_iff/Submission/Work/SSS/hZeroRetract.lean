import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.serreE2Defs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial

/-
`H_0(F; ℤ)` carries a canonical augmentation `ε : H_0(F; ℤ) ⟶ ℤ` (the "sum of coefficients",
`TopCat.singularHomology₀ε`) and, since `F` is nonempty, a point `x₀` of `F` determines a
`0`-simplex of the singular simplicial set `Sing F`, hence a class in `H_0`.  The two are
compatible: `SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε` says precisely that the cycle
class of any `0`-simplex is sent to `1` by the augmentation, so `ε` is a split epimorphism and
`ℤ` is a direct summand of `H_0(F; ℤ)`.
-/
theorem hZeroRetract {F : Type} [TopologicalSpace F] (x₀ : F) :
    ∃ (aug : HZCoeff F (ModuleCat.of ℤ ℤ) 0 ⟶ ModuleCat.of ℤ ℤ)
      (pt : ModuleCat.of ℤ ℤ ⟶ HZCoeff F (ModuleCat.of ℤ ℤ) 0),
      CategoryTheory.CategoryStruct.comp pt aug = CategoryTheory.CategoryStruct.id _ := by
  let R : ModuleCat ℤ := ModuleCat.of ℤ ℤ
  let X : SSet := TopCat.toSSet.obj (TopCat.of F)
  -- `x₀` gives a `0`-simplex of the singular simplicial set, i.e. `Sing F` is nonempty in degree 0.
  have hx : Nonempty (X.obj (Opposite.op (SimplexCategory.mk 0))) :=
    ⟨(TopCat.toSSetObjEquivT (TopCat.of F) (Opposite.op (SimplexCategory.mk 0))).symm
      (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x₀)⟩
  let x : X.obj (Opposite.op (SimplexCategory.mk 0)) := Classical.choice hx
  refine ⟨TopCat.singularHomology₀ε (TopCat.of F) R, ?_, ?_⟩
  · exact HomologicalComplex.liftCycles (X.chainComplex R) (X.ιChainComplex x) 0
        (by simp) (by simp) ≫ HomologicalComplex.homologyπ (X.chainComplex R) 0
  · exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε X R x

end Work.SSS
