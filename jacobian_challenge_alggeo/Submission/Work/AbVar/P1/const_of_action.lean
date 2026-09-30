import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.Gen
import Submission.Work.AbVar.P1.rigid_Gm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# A morphism out of a proper `k`-scheme with a dense `𝔾_m`-orbit into a proper group scheme
is constant

This is step `P1` of the Jacobian development.

`act : X ⊗ 𝔾_m ⟶ X` is a `𝔾_m`-action (only the unit law `h1` and the fact that `x₀` is a
fixed point `hfix` are needed), `j : 𝔾_m ⟶ X` is a dominant equivariant morphism (i.e. the
orbit of `j(1)` is dense), and `A` is a group scheme which is proper over `k`.

The proof is the rigidity argument: the map
`ψ(x,g) = φ(g·x)·φ(x)⁻¹ : X ⊗ 𝔾_m ⟶ A`
collapses on the two coordinate axes `X ⊗ {1}` (`h1`) and `{x₀} ⊗ 𝔾_m` (`hfix`), so by
`Work.AbVar.P1.rigid_Gm` it is constantly `1`.  Hence `φ` is invariant under the action,
so `φ ∘ j` is constant (using `horb`), and since `j` is dominant and `X` is reduced while
`A` is separated, `φ` itself is constant.
-/

set_option autoImplicit false

namespace Work.AbVar.P1

open scoped CategoryTheory.MonObj

open CategoryTheory in
theorem const_of_action {k : Type*} [Field k] {X A : Work.AbVar.Sch k}
    [AlgebraicGeometry.IsProper X.hom] [AlgebraicGeometry.GeometricallyIntegral X.hom]
    [CategoryTheory.GrpObj A] [AlgebraicGeometry.IsProper A.hom]
    (act : MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k) ⟶ X)
    (h1 : Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
        (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)) ≫ act = 𝟙 X)
    (x0 : Work.AbVar.Point X)
    (hfix : Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ act =
      SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ x0)
    (j : Work.AbVar.Gm k ⟶ X) [AlgebraicGeometry.IsDominant j.left]
    (horb : MonoidalCategoryStruct.tensorHom j (𝟙 (Work.AbVar.Gm k)) ≫ act =
      CategoryTheory.MonObj.mul ≫ j)
    (φ : X ⟶ A) :
    ∃ c : Work.AbVar.Point A, φ = SemiCartesianMonoidalCategory.toUnit X ≫ c := by
  -- `X` is reduced (needed to conclude by density) and `A` is separated.
  haveI : AlgebraicGeometry.IsIntegral X.left :=
    AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  -- The "difference" map `ψ(x,g) = φ(g·x)φ(x)⁻¹`.
  let ψ : MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k) ⟶ A :=
    (act ≫ φ) * (SemiCartesianMonoidalCategory.fst X (Work.AbVar.Gm k) ≫ φ)⁻¹
  -- `ψ` collapses on the first axis `X ⊗ {1}`.
  have hB : Work.AbVar.sectionLeft X (Work.AbVar.Gm k)
      (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)) ≫ ψ =
      SemiCartesianMonoidalCategory.toUnit X ≫ CategoryTheory.MonObj.one (X := A) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    rw [← Category.assoc, h1, Category.id_comp]
    rw [← Category.assoc, Work.AbVar.sectionLeft_fst, Category.id_comp]
    simp [Hom.one_def]
  -- `ψ` collapses on the second axis `{x₀} ⊗ 𝔾_m`.
  have hC : Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ ψ =
      SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫
        CategoryTheory.MonObj.one (X := A) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    rw [show (Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫ (act ≫ φ))
          = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ (x0 ≫ φ) by
        rw [← Category.assoc, hfix, Category.assoc]]
    rw [show (Work.AbVar.sectionRight X (Work.AbVar.Gm k) x0 ≫
            (SemiCartesianMonoidalCategory.fst X (Work.AbVar.Gm k) ≫ φ))
          = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫ (x0 ≫ φ) by
        rw [← Category.assoc, Work.AbVar.sectionRight_fst, Category.assoc]]
    simp [Hom.one_def]
  -- Rigidity: `ψ` is the constant map `1`.
  have hψ : ψ = SemiCartesianMonoidalCategory.toUnit
      (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)) ≫
      CategoryTheory.MonObj.one (X := A) :=
    rigid_Gm x0 ψ hB hC
  -- Hence `act ≫ φ = fst ≫ φ`: the action does not change `φ`.
  have hD : act ≫ φ = SemiCartesianMonoidalCategory.fst X (Work.AbVar.Gm k) ≫ φ := by
    have hψ' : ψ = 1 := by rw [hψ, ← Hom.one_def]
    exact mul_inv_eq_one.mp (by rw [← hψ'])
  -- Consequently `φ ∘ j` is invariant under multiplication on `𝔾_m`: `Φ(gh) = Φ(g)`.
  have hE : MonObj.mul (X := Work.AbVar.Gm k) ≫ (j ≫ φ) =
      SemiCartesianMonoidalCategory.fst (Work.AbVar.Gm k) (Work.AbVar.Gm k) ≫ (j ≫ φ) := by
    have h : MonoidalCategoryStruct.tensorHom j (𝟙 (Work.AbVar.Gm k)) ≫ act ≫ φ =
        MonObj.mul (X := Work.AbVar.Gm k) ≫ (j ≫ φ) := by
      rw [← Category.assoc, horb, Category.assoc]
    rw [← h, hD]
    rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
  -- Evaluating at `g = 1` (via the section `g ↦ (1,g)`) shows that `φ ∘ j` is constant.
  have hF : j ≫ φ = SemiCartesianMonoidalCategory.toUnit (Work.AbVar.Gm k) ≫
      (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k) ≫ (j ≫ φ)) := by
    have hmul : Work.AbVar.sectionRight (Work.AbVar.Gm k) (Work.AbVar.Gm k)
        (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)) ≫
          MonObj.mul (X := Work.AbVar.Gm k) = 𝟙 (Work.AbVar.Gm k) :=
      MonObj.lift_comp_one_left _ _
    have h := congrArg (fun t : MonoidalCategoryStruct.tensorObj (Work.AbVar.Gm k)
        (Work.AbVar.Gm k) ⟶ A =>
          Work.AbVar.sectionRight (Work.AbVar.Gm k) (Work.AbVar.Gm k)
            (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)) ≫ t) hE
    rw [← Category.assoc, hmul, Category.id_comp] at h
    rw [← Category.assoc, Work.AbVar.sectionRight_fst, Category.assoc] at h
    exact h
  -- Finally, `j` is dominant, so `φ` is the constant map with value `φ(j(1))`.
  refine ⟨CategoryTheory.MonObj.one (X := Work.AbVar.Gm k) ≫ (j ≫ φ), ?_⟩
  refine Work.AbVar.eq_of_isDominant (A := A) j ?_
  conv_lhs => rw [hF]
  conv_rhs => rw [← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit]

end Work.AbVar.P1
